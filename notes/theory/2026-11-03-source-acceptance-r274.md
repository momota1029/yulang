# R274 source acceptance: first missing constructor edge

Status: **INCOMPLETE**, stopped at the first omitted production owner. This is a bounded source-view result, not a runtime observation, accepted fixture, R71 application, or parent proof.

## Unchanged parent and finite target

The parent remains full inference/effects soundness → R70 → `R71-RAW-CANONICAL-FIBER-COVERAGE-1`, with the original accepted-source domain and quantifiers, Simple-sub A/B, independent satisfying assignments, shared witnesses, source/native correspondence, F1/FK1, and foreign continuations. Parent/A/B: **0→0**. Independent `Need_D` and R71 coverage remain OPEN.

R274 asks for the exact 87-byte fixture's classifier/transaction facts through header selection, recovery-free CST, HIR root and fourteen-slot `LocalSource`, then candidate collection and static-SCC entry. This packet stops before the first normal-return premise of `parse_file`; consequently none of those later conclusions is established.

## Authenticated input gate

- R274 contract SHA-256: `ec875f9705324e9aab328ee8aebd9bc028ab8dafffed3578d3db9fd910a72b27`.
- R274 ranges SHA-256: `4df81d44a22a22c7ea7d56d19f49bd75c6ed6061bbd06fc777cd80cfafa2debf`.
- R274 source view SHA-256: `e1e03aaa65ec15e45ca25c9998b29d366b4b6f8ef16e2d2290ea7dd03935cb2e`.
- R273 authorized input manifest SHA-256: `42040552635bb7c2652eb0bad68cb46295078d03ae70620b7edd555d3883fa5f`; its declared 229 rows are 229 distinct paths. All 229 path digests match.
- All three origin-manifest digests match the input manifest. The two exact inherited contracts match: R268 `719497ad1921be23329a8df790e942ba5c63170ed2bae4880c9656634389ad72`; R269-r4 `a5f3bd1f3bc701ce75191ec234b72264d0dd9e73d7dfd31b88f0b8da0c6009ec`.
- All 28 original whole-file digests, 28 inclusive-interval digests, and 28 source-view-to-original-interval byte comparisons match. Original source bodies were used only in memory for hash and byte-equality checks; no original source body was displayed or read for technical reasoning.

## Exact first missing implication

`R274-E001` authenticates only the literal fixture and constructor call identity. It shows a call of the form

```text
S := Arc<SourceText>(fixture)
H := yu_syntax::scan_header(S)
P := yu_syntax::parse_file(S.clone(), Arc::new(H), SyntaxEnvironment::empty())
```

`R274-E009` (`crates/yu-syntax/src/full_parse.rs:345–371`) begins `parse_file` with `assert!(Arc::ptr_eq(&source, &header.source))` before `effective_full_parse_operators`, `cursor::parse_root`, or the `ParsedFile` constructor. `R274-E008` shows that `HeaderDiscovery::into_header_info(self, source)` stores its **argument** as `HeaderInfo.source`, and `R274-E003`/`R274-E008` show the `discover_header` cursor entry. The view does **not** contain the definition or forwarding law of the called public `yu_syntax::scan_header`.

The first required sequent is therefore:

```text
H = yu_syntax::scan_header(S)
  ⇒ Arc::ptr_eq(&S, &H.source)
     ∧ H is the HeaderInfo built from the source's header discovery.
```

No displayed constructor connects the public call to `HeaderDiscovery::into_header_info` with the same `S`. The exact missing production owner is **`yu_syntax::scan_header`**, including its forwarding to header discovery and `HeaderInfo` construction. Its defining source range is omitted from the 28 excerpt intervals. One cannot discharge the pointer-equality assert or infer its normal return from the fixture call, type compatibility, or the conditional `into_header_info` constructor. This is an omitted owner, **not** an observed assertion failure or a counterexample.

Even if that bridge were supplied, header item classification in `R274-E008` calls `crate::declaration::next_use_item_lex`, whose definition is also absent from the view; its `my` output cannot be inferred from the lexical scanner alone. This is a downstream coverage warning, not a second attempted proof edge. No claim is made about omitted regions being no-ops.

## Scope and disposition

Source-view excerpts used for the first-edge analysis: `R274-E001`, `R274-E003`, `R274-E004`, `R274-E008`, `R274-E009`, `R274-E010`; `R274-E002` was inspected only to check that a scanner cannot replace the missing public header constructor. All 28 excerpts were authenticated, but no later HIR or solver constructor is used as a premise. The fixture's exact string is a datum only; the test's `unwrap`, assertions, helper body, execution and outcomes supply no evidence.

No recovery-free CST, exact HIR, fourteen-slot carrier, candidate/SCC entry, successful accepted-source consumer, source/native correspondence, `Need_D`, or R71 application follows from this result. The first falsifier of a resumed finite witness is a `scan_header` construction that does not preserve the source `Arc` and expected discovery; a distinct accepted carrier or recovery branch is likewise a finite-witness falsifier, not a whole-language refutation. Luna must supply an exact new source-view range for `yu_syntax::scan_header` before this edge can be retried. No production implementation TODO is justified by an omitted proof owner.

Verification: digest and excerpt correspondence checks only; no tests, builds, probes, Cargo, Lean, network, scratch/generated outputs, descendants, source edits, or production writes. Requested Sol/high; observed model/effort **UNKNOWN**. Trialer `/root/sol_r274_source_acceptance`, session `01a1873a-a93b-7dc3-a8ce-028a7b543a80`. Writer stopped after freezing the two leased outputs.
