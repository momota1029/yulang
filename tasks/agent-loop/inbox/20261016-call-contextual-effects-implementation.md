# LUNA-IMPLEMENTATION handoff

- Sprint / contract: `call-contextual-effects-20261016`, contract revision 1
  (visible v2-named contract SHA-256 `be26a76fcb2e4116d89d267f2cb8813dabefd14577aeb532f31b5ab8de154093`;
  parent separately dispatched continuation with unchanged lease/resources).
- Assignment / handoff revision: `LUNA-IMPLEMENTATION`, revision 1.
- Parent: original Call/contextual-effects correspondence; F1, FK1 and
  FIRST-RESULT-ADEQUACY remain open with their original quantifiers.
- Baseline: `c4f007a8abe879b0ac5bfa0c87fd55b6c159855c`.
- Worker: `/root/luna_implementation`; session ID not exposed. Requested
  implementer Luna/high; observed model/effort UNKNOWN. Current writer state:
  STOPPED WRITING after freezing this handoff; no separate cancellation receipt
  is available or needed for this completed foreground worker.
- Exact leased paths: the seven source/test paths in the sprint lease and this
  handoff. Only `crates/yu-solver/tests/candidate_effect_annotation.rs` changed.
  The other six leased source/test files remain byte-identical to their pins.
- Outcome class: provisional source/native evidence (test-only).

## Contribution and evidence

Added `source_call_native_interface_reaches_its_root_effect_consumer`. For an
authentic `tick::next()` source Apply, it checks that the retained candidate
Call points to that same LocalSource Apply, callee and argument occurrences,
and retains a distinct call demand, invocation effect and application effect.
With `[tick]`, the candidate has no conflict; with `[other]`, the propagated
effect conflict identifies the original root annotation position. The test
also confirms that original Gen-Call-0 remains an unresolved supplier.

The existing source-to-consumer path inspected is:

1. `candidate_source.rs` plans each `LocalSourceForm::Apply`, retains its
   occurrence, children, endpoints, recipe and source input, and schedules its
   candidate action.
2. `shadow_apply.rs::admit_candidate_fact` checks the recipe/source-input
   alignment, constructs the negative Function demand from the actual argument
   and argument effect, creates the fresh invocation effect row and retains the
   native interface. It admits callee-to-demand, callee-evaluation-to-Apply
   effect, and invocation-to-Apply effect constraints.
3. Existing candidate propagation and the root annotation consumer check the
   effects. The new regression links that observed conflict back to the exact
   source Apply and annotation occurrence.
4. The separate public runtime test
   `ordinary_function_application_returns_its_argument` exercises normal
   `id 7` compile/execute and returns `7`. It does not exercise contextual
   effect rows or prove correspondence to the private candidate solver.

This is intentionally test-only because original complete Call formation,
provider/whole-carrier membership and source/native adequacy remain unresolved.
It does not change inference, source admission, annotations, diagnostics,
runtime behavior or source domain. It is provisional evidence, not a theorem,
production implementation or cutover. Falsifier: either authentic Apply fails
to map to its retained candidate Call, or the allowed/rejected root rows cease
to produce the stated conflict behavior. Such a failure reopens the source or
constraint owner; it must not be repaired by changing expected semantics. Luna
owns removal of this reversible test if an independent review rejects its
source mapping.

## Prior evidence reused and limits

Reused the existing root-computation annotation tests, including accepted
`tick` and rejected `other` boundary checks; existing Call source/native
observation tests in `shadow_apply.rs`; the I26-R1 recursive Expression
owner repair receipt's use of authentic source occurrence-to-Call mapping; and
the public ordinary-application runtime test. The current candidate path and
those tests are not accepted as original Gen-Call-0 formation. No withdrawn
Simple-sub bypass was used.

Still required: original Gen-Call-0 supplier and reverse source/native
adequacy for FIRST-RESULT-ADEQUACY; authentic remaining OriginalFrame actions
and whole-grammar source coverage for F1; the separately quantified opaque
foreign continuation relation and its bridge for FK1. No production change
depending on these premises is authorized. Full original source coverage,
theorem closure, semantic soundness, principality and production cutover remain
unclaimed.

## Checks, resources and frozen outputs

Serial probes used `CARGO_BUILD_JOBS=1`; each Cargo invocation was bounded by
120 seconds, with no concurrent build. The existing focused root computation
test passed (1/1), the new source/native regression passed (1/1), and the
existing public ordinary-application runtime test passed (1/1). The first
compile of the new test reported three test-code API/type errors; those were
corrected at the test owner and the focused regression then passed. No check
failed after that repair. No broad suite, benchmark or formatter was run.

Hashes at freeze:

| Path | SHA-256 |
| --- | --- |
| `crates/yu-solver/tests/candidate_effect_annotation.rs` | `91c646237401efcce24c457381bbb9c66d72cac7426b8e4f8a5cafc9df3bfa56` |
| `tools/inference-playground/tests/runtime.rs` | `f8bebfd4eb4571e2814b83ea8473c035b429fe1eed4e07d26942a096143306ec` |
| `crates/yu-solver/src/candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| `crates/yu-solver/src/shadow_apply.rs` | `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf` |
| `crates/yu-solver/src/candidate_call.rs` | `cbad9cf51a05343eb7a29ab77aac520891467a8aa4edc3201ea3d91f978984a1` |
| `crates/yu-solver/src/candidate_effect.rs` | `44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9` |
| `crates/yu-solver/src/candidate_context.rs` | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` |

Cargo used the workspace `target/` build cache, a generated path outside this
lease; it is known disposable scratch and has not been cleaned. No other
scratch or generated files were intentionally created. The test file is the
only implementation output; this handoff is the sole receipt output.

Next related step: WAITING for the independent proof/source owners to supply
the exact original Call/first-Apply adequacy evidence. Then Luna can select a
new dependent implementation packet or close the remaining bridge. No further
safe compiler behavior change is justified within this lease.
