use rustc_hash::FxHashMap;

use crate::term::intern::{Block, Store};

/// Renumbers the store so each declaration follows soon after what it uses, keeping the
/// session tables warm. Blocks move as one unit, and everything up to the last builtin stays
/// put. Returns false, leaving the store untouched, when the import recorded no dependencies
/// or some reference does not resolve to an earlier declaration.
pub fn reorder(store: &mut Store<'_>) -> bool {
    let Some(rec) = store.deps.take() else {
        return false;
    };
    let n = store.declars.len();
    let mut unit_of = vec![0u32; n];
    let mut units: Vec<(u32, u32)> = Vec::new();
    let mut i = 0;
    while i < n {
        let end = store
            .blocks
            .get(&store.declars[i].name())
            .map_or(i as u32 + 1, |b| b.end);
        unit_of[i..end as usize].fill(units.len() as u32);
        units.push((i as u32, end));
        i = end as usize;
    }
    let m = units.len();
    let pin = store
        .names
        .all()
        .iter()
        .filter_map(|(_, n)| n.and_then(|n| n.decl_idx()))
        .map(|i| unit_of[i as usize] as usize + 1)
        .max()
        .unwrap_or(0);

    let mut start = vec![0u32; m + 1];
    let mut deps: Vec<u32> = Vec::new();
    let mut own: Vec<u32> = Vec::new();
    let (mut d0, mut n0) = (0, 0);
    for (u, &(s, e)) in units.iter().enumerate() {
        own.clear();
        for &(d1, n1) in &rec.ends[s as usize..e as usize] {
            own.extend(
                rec.decls[d0..d1 as usize]
                    .iter()
                    .map(|&j| unit_of[j as usize]),
            );
            for name in &rec.names[n0..n1 as usize] {
                let Some(j) = name.decl_idx() else {
                    return false;
                };
                own.push(unit_of[j as usize]);
            }
            (d0, n0) = (d1 as usize, n1 as usize);
        }
        if own.iter().any(|&v| v as usize > u) {
            return false;
        }
        if u >= pin {
            own.retain(|&v| v as usize != u && v as usize >= pin);
            own.sort_unstable();
            own.dedup();
            deps.extend_from_slice(&own);
        }
        start[u + 1] = deps.len() as u32;
    }

    let mut indeg = vec![0u32; m];
    let mut ustart = vec![0u32; m + 1];
    for &d in &deps {
        ustart[d as usize + 1] += 1;
    }
    for u in 0..m {
        ustart[u + 1] += ustart[u];
        indeg[u] = start[u + 1] - start[u];
    }
    let mut fill = ustart.clone();
    let mut users = vec![0u32; deps.len()];
    for u in pin..m {
        for &d in &deps[start[u] as usize..start[u + 1] as usize] {
            users[fill[d as usize] as usize] = u as u32;
            fill[d as usize] += 1;
        }
    }

    let mut order: Vec<u32> = (0..pin as u32).collect();
    let mut ready: Vec<u32> = (pin as u32..m as u32)
        .rev()
        .filter(|&u| indeg[u as usize] == 0)
        .collect();
    while let Some(u) = ready.pop() {
        order.push(u);
        for &w in users[ustart[u as usize] as usize..ustart[u as usize + 1] as usize]
            .iter()
            .rev()
        {
            indeg[w as usize] -= 1;
            if indeg[w as usize] == 0 {
                ready.push(w);
            }
        }
    }
    assert_eq!(order.len(), m, "dependency cycle");

    let mut declars = Vec::with_capacity(n);
    let mut blocks = FxHashMap::default();
    for &u in &order {
        let (s, e) = units[u as usize];
        let at = declars.len() as u32;
        for d in &store.declars[s as usize..e as usize] {
            d.name().set_decl_idx(declars.len() as u32);
            declars.push(*d);
        }
        if let Some(&b) = store.blocks.get(&store.declars[s as usize].name()) {
            let b = Block {
                start: at,
                types_end: b.types_end - s + at,
                ctors_end: b.ctors_end - s + at,
                end: b.end - s + at,
            };
            for d in &declars[at as usize..] {
                blocks.insert(d.name(), b);
            }
        }
    }
    store.declars = declars;
    store.blocks = blocks;
    true
}
