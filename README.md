<p align="center">
  <img src=".github/logo.png" width="250" height="250" alt="Nano Lean, the tiny Lean kernel that can">
</p>

# nano-lean

A minimalist (but complete) parallel Lean type checker in Rust built on [unbound](https://github.com/sdiehl/unbound), using de Bruijn indices for binders.

The package providers four binaries:

- `nl-fast`: the main fast typechecker
- `nl-ref`: reference kernel for checking core-syntax files and exports
- `nl-mutate`: mutation tester that edits an export and diffs every checker's verdict
- `nl-watch`: a fast cached build watch tool for Lake projects

Successfully type-checks all of Mathlib (718k declarations) with 0 errors and 0 timeouts.

```sh
# Install nl-fast and nl-ref
cargo install --git https://github.com/sdiehl/nano-lean

# Check a Lean export (NDJSON or blean)
nl-fast FILE.ndjson [-j THREADS]
nl-fast FILE.blean [-j THREADS]

# Reject an export whose primitives differ from a trusted export of Init
nl-fast --prelude init.blean FILE.blean

# Skip declarations a previous run accepted
nl-fast --cache FILE.accepted FILE.blean

# Rebuild and recheck a Lake project on every save, from its root
nl-watch MODULE [-j THREADS]

# Check a core-syntax file
nl-ref examples/core.ltc

# Check an export with the reference kernel, optionally in parallel
nl-ref --export FILE.ndjson
nl-ref --export-parallel JOBS [--memory-mib MIB] FILE.ndjson

# Write a core-syntax file's declarations as an NDJSON export
nl-ref --emit FILE.ltc > FILE.ndjson

# Mutate an export and report checker disagreements, shrinking each finding
nl-mutate [--seed N] [--per-op N] [--op NAME] [--out DIR] FILE.ndjson
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

# The blean binary format is smaller and faster to load, nl-fast detects it
lake env olean-export Mathlib -f blean -o mathlib.blean
nl-fast mathlib.blean

# Convert an existing export between NDJSON and blean
olean-export convert mathlib.ndjson -o mathlib.blean
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

Checking [OpenAI's quasi-Riemann hypothesis proof](https://github.com/openai/math/blob/main/lean/docs/003.md) and its dependencies from the blean binary export

|                       | M4 Max `-j 1` | M4 Max `-j 10` | M4 Max `-j 14` | M4 Max `-j 28` | M4 Max `-j 64` |
| --------------------- | ------------- | -------------- | -------------- | -------------- | -------------- |
| Wall time             | 20.74 s       | 3.75 s         | 3.66 s         | 3.76 s         | 4.04 s         |
| Kernel check          | 19.71 s       | 2.71 s         | 2.58 s         | 2.70 s         | 2.90 s         |
| Instructions          | 227.4 G       | 235.2 G        | 236.4 G        | 239.0 G        | 242.6 G        |
| Cycles                | 84.0 G        | 108.0 G        | 122.6 G        | 125.2 G        | 127.2 G        |
| Peak memory footprint | 3.12 GB       | 6.80 GB        | 7.42 GB        | 10.15 GB       | 12.08 GB       |

Checking [OpenAI's Erdős reciprocal-sum proof](https://github.com/openai/math/blob/main/lean/docs/159.md) and its dependencies from the blean binary export

|                       | M4 Max `-j 1` | M4 Max `-j 14` |
| --------------------- | ------------- | -------------- |
| Wall time             | 94.58 s       | 23.33 s        |
| Kernel check          | 91.80 s       | 19.11 s        |
| Instructions          | 796.9 G       | 837.9 G        |
| Cycles                | 375.6 G       | 550.0 G        |
| Peak memory footprint | 12.64 GB      | 26.42 GB       |

## Trust model

See [docs/TRUST.md](docs/TRUST.md) for what the checkers trust and how `--prelude`, `--axioms` and the cache bound it.

## Caching

`--cache FILE` skips declarations a previous run accepted and records the new ones. Editing a declaration rechecks it and everything that depends on it, and a new checker version starts the file over.

```sh
nl-fast --cache mathlib.accepted mathlib.blean
nl-fast --cache mathlib.accepted --cache-audit mathlib.blean  # recheck everything
```

In `nano-lean.toml`, `cache = "mathlib.accepted"` turns it on and `--no-cache` turns it off for one run.

## Configuration

`nl-fast` reads `nano-lean.toml` from the working directory if one exists, or the file given with `--config`. Every key is optional and a flag on the command line overrides it. A relative `prelude` or `cache` path resolves against the file's directory.

```toml
threads = 10
steps = 200000000
arena_mib = 2048
fallback = false
term_core = false
prelude = "init.blean"
axioms = ["propext", "Classical.choice", "Quot.sound"]
cache = "mathlib.accepted"
cache_audit = false
```

Without the file the defaults are one thread, no prelude check, no axiom restriction and no cache.

## License

Released under the MIT License. See [LICENSE](LICENSE) for details.
