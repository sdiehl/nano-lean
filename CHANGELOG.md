# Changelog

## Unreleased

- Keep a `Nat` let value behind a local in both fast cores, so closed literal folding in the body never evaluates it, as in Lean's kernel.

## 0.2.0 (2026-10-25)

- Add a Nix flake dev shell.
- Compare the structure name when two stuck projections meet in the fast cores, matching the reference kernel.
- Charge the value core argument probe per step instead of per comparison, so a probe on a big structure stays bounded.
- Compare persistent sessions with fresh ones across every fixture, past rejections.
- Shrink findings on the unmutated export and re-apply the edit, so a witness keeps a valid base and its expected verdict.
- Keep export ids stable when compacting a mutant.
- Reject declarations that reuse a `Nat`, `Bool`, `Char`, `String` or `List` primitive name with another signature, in the importer and the reference kernel.
- Gate quotient reduction on `Quot` declarations.
- Reject quotient names on other declarations.
- Add `quot-axiom` mutation operator.
- Report rejections over unsupported in `nl-fast` exit code.
- Bound importer memory on sparse ids.
- Accept missing `"all"` groups like the reference loader.
- Cap `Nat.pow` result size.
- Derive reserved binder names from the lexer.
- Share JSON helpers, schema keys and projection checks.
- Check the owning block for `--declaration` on a generated name.
- Reject oversized universe offsets in the parser.
- Keep budget errors distinct in `Error::context`.
- Export `Expr` and `Level` under `kernel`.
- Add `Nat.log2` to the reference kernel.
- Unfold oversized `Nat.pow` and `Nat.shiftLeft` as Lean does.
- Pin Rust 1.97.1, elan 4.2.4 and olean-export 0.2.0.
- Check Mathlib and corpora as blean in CI.
- Upgrade olean-export to 0.3.0.
- Replace `stacker` with a stack floor guard that declines a declaration instead of overflowing.
- Return value checker rejections and declines through `R` instead of unwinding.
- Return reference checker rejections and declines through `R` and drop the panic channel.
- Pin function alignment to 64 bytes so code placement cannot move the hot loops.
- Split the Mathlib CI script into a bounded shell driver and two Python helpers, and drop the perf probe.

## 0.1.0 (2026-10-08)

- Initial release.
