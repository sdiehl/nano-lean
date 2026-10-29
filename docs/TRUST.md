# Trust model

Like Lean's kernel, every checker reduces `Nat` and `String` primitives such as `Nat.add` by name and trusts their bodies. The importer rejects a primitive name declared with the wrong type, but an export can redefine `Nat.add` with the right type and a different body, then prove `False` by literal folding ([`tests/fixtures/ForgedNatAdd.lean`](../tests/fixtures/ForgedNatAdd.lean)). Lean rules this out with [comparator](https://github.com/leanprover/comparator), and `--prelude` does the same: it compares every primitive, and the closure of their types and definition bodies, with a trusted export and rejects any difference. Build the trusted export from the same toolchain as the export under check.

```sh
lake env olean-export Init -f blean -o init.blean
nl-fast --prelude init.blean FILE.blean
```

`--axioms` rejects an export that declares any axiom outside the list.

```sh
nl-fast --prelude init.blean --axioms propext,Classical.choice,Quot.sound FILE.blean
```

`--cache` files are trusted input like the export: a recorded key is taken as an accepted declaration, so keep the file where only the checker writes. `--cache-audit` rechecks every declaration and exits 1 if the file records a rejected one.
