# R52 Luna source-audit handoff

Disposition: `NO_SOURCE_QUALIFIED_NATIVE_MIXED_CUT_WITNESS`; no safe code slice. Static source construction finds a qualified recursive-local Apply event, but no completed same-lineage native/scoped-consumer route. This does not prove the general mixed cut unreachable.

- Approved single local self-recursion supplies an open monomorphic initializer root. Candidate scheduling emits a direct Link for the active self Name and retains the Apply separately.
- The source Value graph gives `loop → used` from the initializer's final Name and a qualified `(used, loop)` event from `used = loop forward`.
- Scoped Apply observation requires an exact retained `LocalFreshRoute` and installed `LocalScheme`; the active self Name has no such route. R50 remains NOT ADOPTED, so no active-Link consumer interpretation is assumed.
- Conditional signed-owner analysis says a successful negative demand through the older recursive root would merge both original Function ports plus the selected closure. This is pressure evidence only, because native/scoped admission and successful completion are not established.
- The general cut remains open at `Capture::expand_row` stopping at a nonlocal/shared anchor while FreshUse independently freshens local ports. No source invariant excluding it and no completed source-qualified counterexample were found.

Parent: full inference/evaluator theorem and original Simple-sub A/B OPEN 0→0. No source-domain or expectation narrowing, semantic adoption, code/test/runtime authority or R50 adoption.

Evidence is in `notes/progress/2026-10-19-r52-mixed-capture-source.md`; no tests, builds, runtime, probes, measurements or code edits were made. Current contract is R52 revision 4. Revalidate the frozen artifact and all 24 file pins before independent review.
