# nano-lean

A minimalist (but complete) Lean type checker in Rust built on [unbound](https://github.com/sdiehl/unbound), using de Bruijn indices for binders.

Aims to support the full Lean kernel with the full theory, including universe polymorphism, inductive types, and quotients.

```sh
cargo run -- examples/core.ltc
cargo test
```

The interned-term checker used by CI is available with `cargo run --release --bin nl -- FILE.ndjson [THREADS] --native-only`. Its `checker`, `import`, and `term` modules are part of the library and their unit tests run with `cargo test`. Inductive validation still uses the existing kernel.

Lean NDJSON exports can be checked with `cargo run --release -- --export FILE.ndjson`.
The importer accepts safe proof exports and rejects unsafe or partial declarations.
Natural/string literals and quotient primitives are supported

Parallel export checking is available with `cargo run --release -- --export-parallel JOBS [--memory-mib MIB] FILE.ndjson`.

## License

Released under the MIT License. See [LICENSE](LICENSE) for details.
