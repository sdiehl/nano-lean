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

Set `NANO_LEAN_TRACE=1` to log each declaration to stderr during a long export check.

## License

Released under the MIT License. See [LICENSE](LICENSE) for details.
