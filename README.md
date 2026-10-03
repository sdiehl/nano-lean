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

Use `cargo run --release -- --export-parallel 2 FILE.ndjson` to check a single
export with two worker processes. Each worker imports the whole export in order
and validates its assigned ordinary declarations; inductives and quotient
primitives are validated in every worker. The coordinator accepts only when all
partitions succeed with the same SHA-256 input digest and declaration counts.
Parallel mode defaults to a **2 GiB total memory budget**, monitored across the
coordinator and workers (including compressed memory on macOS, and RSS plus swap
on Linux). Exceeding the budget stops all workers and returns a failure; polling
can briefly overshoot the limit. Set a different budget explicitly with
`--export-parallel 2 --memory-mib 4096 FILE.ndjson`. Parsing and environment storage
are duplicated, so more workers need more memory and do not guarantee a
proportional speedup. One worker also provides a monitored serial run. The internal
`--export-shard FILE INDEX JOBS` command reports only `shard_checked`; a single
worker result does not validate the export.

Set `NANO_LEAN_TRACE=1` to log each declaration to stderr during a long export check.

## License

Released under the MIT License. See [LICENSE](LICENSE) for details.
