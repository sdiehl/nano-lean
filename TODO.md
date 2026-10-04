# Roadmap to full Mathlib

## Phase 1 — Foundational correctness and reproducible inputs

- [x] Preserve exact inductive block boundaries and declaration visibility.
- [x] Reject self references and unauthorized forward references.
- [x] Prevent inference caches from bypassing declaration visibility.
- [x] Compare proposition universes semantically rather than by pointer identity.
- [x] Check foundational declarations, including `Eq.symm` and `congrArg`.
- [x] Add small differential fixtures and malformed-input regression tests.
- [x] Reconcile the pinned export count: 718,577 declarations.
- [x] Track the experimental source and tests in a local checkpoint.

## Phase 2 — Bounded memory and single-threaded Init

- [x] Isolate the Int32 reduction blowup to one declaration.
- [x] Resolve projections before prematurely unfolding arithmetic operations.
- [x] Bound speculative congruence attempts and fall back after exhaustion.
- [x] Free big-integer heap buffers when a declaration's arena is reset.
- [x] Release oversized bump chunks between declarations.
- [x] Add configurable declaration work and arena budgets.
- [x] Report resource exhaustion as unsupported with a nonzero process exit.
- [x] Verify that checking continues after a declaration exhausts its budget.
- [x] Add declaration tracing and terminal progress with an ETA.
- [x] Complete single-threaded Init under external memory, time, and pressure guards.
- [x] Exercise bounded Mathlib prefixes and identify the next hotspot.

## Phase 3 — Complete kernel validation

- [x] Validate inductive parameters, indices, constructor types, and metadata.
- [x] Enforce strict positivity and permitted elimination from Prop.
- [x] Reconstruct and validate recursor signatures and computation rules.
- [x] Handle mutual and nested inductive declarations without trusting export metadata.
- [x] Audit projection typing, structure eta, and proof recursor K reduction.
- [x] Audit quotient signatures, primitive reduction, and universe comparison.
- [x] Run all 193 external export fixtures against the new checker.
- [x] Add regressions for every mismatch with the existing kernel.
- [x] Verify malformed exports cannot be accepted through caches or speculative paths.

Inductive reconstruction reuses the existing kernel. Four positive stress
fixtures require a counted retry after native arena exhaustion; the fixture gate
uses an explicit 100-million-step budget. Native-only completion remains below.

## Phase 4 — Full Mathlib completion

- [x] Eliminate fallback on the application, beta, and let ladders.
- [ ] Eliminate fallback on the four magma stress fixtures.
- [x] Reduce adapter overhead while preserving shared inductive validation.
- [x] Isolate and fix `AlgebraicGeometry.ΓSpec.adjunction._proof_3`.
- [x] Avoid repeated speculative comparisons under rigid heads.
- [x] Preserve unrelated shared domains during nested-inductive discovery.
- [x] Recheck the 100,000-declaration prefix with zero unsupported declarations.
- [ ] Increase prefix sizes incrementally, recording the first failure and peak RSS.
- [ ] Reduce remaining failures to single-declaration regression cases.
- [ ] Fix reduction, universe, or allocation hotspots before increasing budgets.
- [ ] Check the complete pinned export with zero failures or unsupported declarations.
- [ ] Verify the input digest and all 718,577 declaration outcomes.

## Phase 5 — Performance and shared parallel checking

- [ ] Profile the successful full run to rank remaining costs.
- [ ] Optimize measured conversion, substitution, interning, and cache hotspots.
- [ ] Avoid reconstructing terms or environments unnecessarily during unfolding.
- [ ] Evaluate allocator and release-profile changes with comparable runs.
- [ ] Validate shared-store threaded checking against single-threaded outcomes.
- [ ] Measure scaling under a total memory budget, including worker-local arenas.
- [ ] Preserve correctness regressions and report import and checking time separately.

## Phase 6 — CI and supported integration

- [ ] Integrate the new checker into the supported CLI after correctness gates pass.
- [ ] Run its regression suite and full pinned Mathlib check in CI.
- [ ] Preserve dependency and export caches even when checking fails.
- [ ] Keep progress, resource-exhaustion diagnostics, and final counts visible in CI.
- [ ] Make success require every declaration and the expected input digest.
- [ ] Document supported behavior, remaining limitations, and reproduction commands.
