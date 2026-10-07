<p align="center">
  <img src=".github/logo.png" width="250" height="250" alt="Nano Lean, the tiny Lean kernel that can">
</p>

# nano-lean

A minimalist (but complete) Lean type checker in Rust built on [unbound](https://github.com/sdiehl/unbound), using de Bruijn indices for binders.

Successfully type-checks all of Mathlib (718k declarations) with 0 errors and 0 timeouts.

- `nl-fast`: fast interned-term checker for Lean NDJSON exports.
- `nl-ref`: reference kernel for core-syntax files and exports.
- `nl-mutate`: mutation tester that edits an export and diffs every checker's verdict.

```sh
# Install nl-fast and nl-ref
cargo install --git https://github.com/sdiehl/nano-lean

# Check a Lean NDJSON export
nl-fast FILE.ndjson [-j THREADS]

# Check a core-syntax file
nl-ref examples/core.ltc

# Check an export with the reference kernel, optionally in parallel
nl-ref --export FILE.ndjson
nl-ref --export-parallel JOBS [--memory-mib MIB] FILE.ndjson

# Write a core-syntax file's declarations as an NDJSON export
nl-ref --emit FILE.ltc > FILE.ndjson

# Mutate an export and report checker disagreements, shrinking each finding
nl-mutate [--seed N] [--per-op N] [--op NAME] [--out DIR] FILE.ndjson

# Run the tests (BLESS=1 regenerates golden .out and .verdict files)
cargo test
```

## Checking Mathlib

Exports come from [olean-export](https://crates.io/crates/olean-export), run inside a Mathlib checkout so `lake env` can find its oleans.

```sh
# Install the exporter
cargo install olean-export

# Fetch Mathlib and its prebuilt oleans (no compile)
git clone --depth 1 https://github.com/leanprover-community/mathlib4 && cd mathlib4
lake exe cache get

# Export Mathlib to a file, then check it
lake env olean-export Mathlib -o mathlib.ndjson
nl-fast mathlib.ndjson

# Or pipe it straight through
lake env olean-export Mathlib -q | nl-fast
```

### Performance

Checking all of Mathlib on an Apple M5 from the blean binary export:

|                       | `-j 1`  | `-j 10` |
| --------------------- | ------- | ------- |
| Wall time             | 57.4 s  | 16.7 s  |
| Kernel check          | 53.5 s  | 12.5 s  |
| Instructions          | 708.5 G | 746.5 G |
| Cycles                | 247.7 G | 385.6 G |
| Peak memory footprint | 7.5 GB  | 9.2 GB  |

## License

Released under the MIT License. See [LICENSE](LICENSE) for details.
