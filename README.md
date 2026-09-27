# nano-lean

A minimal Lean-style type checker in Rust built on [unbound](https://github.com/sdiehl/unbound), using de Bruijn indices for bound variables and fresh names when opening binders.
Lean's kernel uses the same locally nameless approach, but supports the full theory, including universe polymorphism, inductive types, and quotients.

```sh
cargo run -- examples/core.ltc
cargo test
```

## License

Released under the MIT License. See [LICENSE](LICENSE) for details.
