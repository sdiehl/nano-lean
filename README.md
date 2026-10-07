# nano-lean

A minimalist (but complete) Lean type checker in Rust built on [unbound](https://github.com/sdiehl/unbound), using de Bruijn indices for binders.

Successfully type-checks all of Mathlib (718k declarations) with 0 errors and 0 timeouts.

- `nl-fast`: fast interned-term checker for Lean NDJSON exports.
- `nl-ref`: reference kernel for core-syntax files and exports.

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

# Run the tests
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

## License

Released under the MIT License. See [LICENSE](LICENSE) for details.
