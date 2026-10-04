# nano-lean

A small Lean kernel written in Rust built on [unbound](https://github.com/sdiehl/unbound), using hash consing and de Bruijn indices for binders to give much faster performance than the vanilla Lean kernel.

Aims to support the full Lean kernel with the full theory, including universe polymorphism, inductive types, and quotients.

```sh
cargo run -- examples/core.ltc
cargo test
```

Full Mathlib verification is not yet achieved. The latest measured Lean 4.34.1 run
checked 111,492 declarations in 4m04s before reaching the 10 GiB memory limit.
Current work focuses on reducing memory use and repeated conversion work.

Lean NDJSON exports can be checked with `cargo run --release -- --export FILE.ndjson`.
The importer accepts safe proof exports and rejects unsafe or partial declarations.

Check in parallel with `cargo run --release -- --export-parallel 2 FILE.ndjson`.
The default memory budget is 2 GiB; override with `--memory-mib 4096` before the filename.

Pushes run the full Mathlib check in CI with a 10 GiB memory budget and saved logs.
CI reuses a checksum-pinned Mathlib export across runs. A cache miss generates it
with a separate 14 GiB memory limit; export timing and peak memory are saved with
the CI logs. The checker retains its 11 GiB OS limit.

Parallel checks show periodic status in CI; set `NANO_LEAN_PROGRESS=1` to enable it locally.

Set `NANO_LEAN_TRACE=1` to log each declaration to stderr during a long export check.

Build with `--features profile` to emit evaluator allocation counts and inclusive
timings to stderr after each export check. Profiling is disabled in normal builds.

The experimental arena checker is available separately:

```sh
cargo run --release --example nl -- FILE.ndjson
cargo test --example nl
```

It defaults to one worker and displays terminal progress with an ETA. Use
`--declaration NAME` or `--limit N` to isolate work, and `--trace` for declaration
names, timings, and arena sizes. Per-declaration defaults are 10 million work
steps and 64 MiB of term storage; adjust with `--steps N` and `--arena-mib N`.
These are cooperative checker budgets, not process RSS limits. Exhaustion is
reported as unsupported and causes a nonzero exit, while remaining declarations
are still attempted. Inductive validation is incomplete, so a successful run of
this driver is not full kernel verification.

## License

Released under the MIT License. See [LICENSE](LICENSE) for details.
