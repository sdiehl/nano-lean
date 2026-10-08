//! blean fixtures are `olean-export convert` of the NDJSON fixture with the same name.

#![allow(clippy::unwrap_used, clippy::panic)]

use nano_lean::{checker, import, term::arena::Arena};

type Summary = ([usize; 4], Vec<(String, bool)>);

fn summary(bytes: &[u8]) -> Result<Summary, String> {
    let arena = Arena::new();
    let store = import::import_bytes(&arena, bytes).map_err(|e| e.to_string())?;
    let verdicts = (0..store.declars.len() as u32)
        .map(|i| {
            let ok = checker::check_declaration(&store, &mut Arena::new(), i, Default::default());
            (store.declars[i as usize].name().to_string(), ok.is_ok())
        })
        .collect();
    let s = &store.stats;
    Ok(([s.names, s.levels, s.expressions, s.declarations], verdicts))
}

macro_rules! same {
    ($($test:ident: $name:literal),* $(,)?) => {$(
        #[test]
        fn $test() {
            let ndjson = summary(include_bytes!(concat!("fixtures/", $name, ".ndjson")));
            let blean = summary(include_bytes!(concat!("fixtures/blean/", $name, ".blean")));
            match (ndjson, blean) {
                (Ok(a), Ok(b)) => assert_eq!(a, b),
                (Err(_), Err(_)) => {}
                (a, b) => panic!("ndjson {a:?}, blean {b:?}"),
            }
        }
    )*};
}

same! {
    mutual: "mutual",
    nested: "nested",
    primitives: "primitives",
    theorem_reduction: "theorem-reduction",
    invalid_nested_parameter: "invalid-nested-parameter",
}

#[test]
fn damaged_files_are_rejected() {
    let bytes = include_bytes!("fixtures/blean/nested.blean");
    let arena = Arena::new();
    for cut in [8, bytes.len() / 2, bytes.len() - 1] {
        assert!(import::import_bytes(&arena, &bytes[..cut]).is_err());
    }
    let mut extra = bytes.to_vec();
    extra.push(0);
    assert!(import::import_bytes(&arena, &extra).is_err());
}
