# Changelog

## 0.3.2 (2026-11-05)

- Intern Pi values built by rule substitution, so deep `List` indexing runs about 12x cheaper.
- Accept recursors that match the ones built from their inductive.
- Check nested inductive blocks natively by expanding nested occurrences.
- Start faster on tiny inputs: one worker per declaration at most, no mimalloc environment scan.
- Keep long sparse environments untrimmed, so shift cascades check about 40% cheaper.
- Give argument probes under cheap heads a smaller budget, so lazy projections check about 35% cheaper.

## 0.3.1 (2026-11-03)

- Cut Mathlib checking cost by about a tenth:
  - Hash memo keys once and check projected memo hits with a lockstep environment walk.
  - Memoize Pi codomain instantiation across application spines.
  - Index environment frames directly from node runs.
  - Build applications of up to 16 arguments on the stack.
  - Build runs of application lines straight into the import table.
- Check long beta ladders in near linear time by collapsing deep environment runs into frames.

## 0.3.0 (2026-11-02)

- Check `.olean` files directly with `nl-fast --olean`, importing records straight into the checker.
- Add `nl-watch`, which keeps the environment loaded and rechecks a Lake project on every save.
- Add a content cache of accepted declarations, with `--cache`, `--cache-audit` and `--no-cache`, saved on interrupt.
- Add `--prelude` and `--axioms` to reject untrusted primitives and unexpected axioms.
- Read settings from `nano-lean.toml` or `--config`, and add `--quiet`.
- Cut Mathlib checking cost substantially:
  - Derive reduction rules for hot definitions.
  - Memoize evaluation, including wide applications.
  - Memoize whnf and types on values.
  - Keep bounded tables across declarations.
  - Scan import lines in a single pass.
- Scale cleanly across threads by claiming declarations in contiguous runs.
- Bound value core memory, and enforce pointer and table invariants in release builds.
- Keep `Nat` let values behind a local, as in Lean's kernel.
- Add a memocheck oracle, a weekly mutation campaign, a kernel benchmark suite and new adversarial fixtures.

## 0.2.0 (2026-10-25)

- Reject primitive names like `Nat` or `List` reused with another signature.
- Gate quotient reduction on `Quot` declarations and reject quotient names elsewhere.
- Compare structure names when stuck projections meet, as the reference kernel does.
- Match Lean on oversized `Nat.pow` and `Nat.shiftLeft`, and add `Nat.log2`.
- Decline deep declarations with a stack guard instead of overflowing.
- Bound importer memory and value core probes on large inputs.
- Report rejections over unsupported in the `nl-fast` exit code.
- Accept missing `"all"` groups like the reference loader.
- Strengthen mutation testing with stable shrinking and a `quot-axiom` operator.
- Pin Rust, elan and olean-export, and check Mathlib and corpora in CI.
- Add a Nix flake dev shell.

## 0.1.0 (2026-10-08)

- Initial release.
