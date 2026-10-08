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

Checking all of Mathlib from the blean binary export:

|                       | M5 `-j 1` | M5 `-j 10` | M4 Max `-j 14` |
| --------------------- | --------- | ---------- | -------------- |
| Wall time             | 57.4 s    | 16.7 s     | 11.85 s        |
| Kernel check          | 53.5 s    | 12.5 s     | 7.55 s         |
| Instructions          | 708.5 G   | 746.5 G    | 742.3 G        |
| Cycles                | 247.7 G   | 385.6 G    | 352.7 G        |
| Peak memory footprint | 7.5 GB    | 9.2 GB     | 10.7 GB        |

Checking the full imported environment of [OpenAI's Navier–Stokes and Euler proofs](https://github.com/openai/NavierStokesAndEuler) from the blean binary export

|                       | M4 Max `-j 1` | M4 Max `-j 10` | M4 Max `-j 14` | M4 Max `-j 28` | M4 Max `-j 64` |
| --------------------- | ------------- | -------------- | -------------- | -------------- | -------------- |
| Wall time             | 83.58 s       | 18.74 s        | 17.13 s        | 17.67 s        | 20.85 s        |
| Kernel check          | 78.83 s       | 13.00 s        | 12.11 s        | 12.56 s        | 15.51 s        |
| Instructions          | 914.8 G       | 971.5 G        | 977.0 G        | 984.8 G        | 1011.8 G       |
| Cycles                | 333.2 G       | 426.4 G        | 471.3 G        | 483.5 G        | 566.2 G        |
| Peak memory footprint | 10.14 GB      | 11.56 GB       | 12.29 GB       | 14.62 GB       | 19.86 GB       |

Checking the full imported environment of [CSLib](https://github.com/leanprover/cslib) from the blean binary export

|                       | M4 Max `-j 1` | M4 Max `-j 10` | M4 Max `-j 14` | M4 Max `-j 28` | M4 Max `-j 64` |
| --------------------- | ------------- | -------------- | -------------- | -------------- | -------------- |
| Wall time             | 21.74 s       | 4.61 s         | 4.42 s         | 4.56 s         | 4.74 s         |
| Kernel check          | 20.04 s       | 2.96 s         | 2.75 s         | 2.81 s         | 3.04 s         |
| Instructions          | 258.0 G       | 296.1 G        | 300.8 G        | 305.5 G        | 309.2 G        |
| Cycles                | 87.5 G        | 120.4 G        | 136.6 G        | 141.1 G        | 142.4 G        |
| Peak memory footprint | 3.18 GB       | 5.89 GB        | 6.92 GB        | 8.92 GB        | 12.08 GB       |

## License

Released under the MIT License. See [LICENSE](LICENSE) for details.
