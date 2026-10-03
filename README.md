# nano-lean

A small Lean kernel written in Rust built on [unbound](https://github.com/sdiehl/unbound), using hash consing and de Bruijn indices for binders to give much faster performance than the vanilla Lean kernel.

Aims to support the full Lean kernel with the full theory, including universe polymorphism, inductive types, and quotients.

```sh
cargo run -- examples/core.ltc
cargo test
```

Can currently type-check 670k declarations in Mathlib with no errors or timeouts and peak resident memory of 11 GB. Trying to bring this down to like 2 GB.

Lean NDJSON exports can be checked with `cargo run --release -- --export FILE.ndjson`.
The importer accepts safe proof exports and rejects unsafe or partial declarations.

Check in parallel with `cargo run --release -- --export-parallel 2 FILE.ndjson`.
The default memory budget is 2 GiB; override with `--memory-mib 4096` before the filename.

Pushes run the full Mathlib check in CI with a 10 GiB memory budget and saved logs.

Parallel checks show periodic status in CI; set `NANO_LEAN_PROGRESS=1` to enable it locally.

Set `NANO_LEAN_TRACE=1` to log each declaration to stderr during a long export check.

Build with `--features profile` to emit evaluator allocation counts and inclusive
timings to stderr after each export check. Profiling is disabled in normal builds.

## License

Released under the MIT License. See [LICENSE](LICENSE) for details.
