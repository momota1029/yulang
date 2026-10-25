# Independent review: higher-order substitution, capture and entry

Review-ID: higher-order-substitution-entry-review-astra-r1; revision 1.
Verdict: CLEAN within the exact finite HigherOrder research grammar and typed construction scope. No blocking, major or minor findings.
Reviewer: /root/higher_order_substitution_entry_review_astra_r1, fresh nonauthor; no construction, repair or counterexample contribution to the reviewed artifact. This is actual independent review, not producer certification.
Requested model/effort: gpt-6-astra/medium. Observed model/effort: UNKNOWN/UNKNOWN.
Baseline: 98118c2933694a03fcbf443a4cd638e350f76394.
Scope authority: frozen substitution-entry contract plus parallel-theory amendment permitting concurrent independent authors and this reviewer. Root operating map, base invariants, sprint/proof skills and applicable rules were read. Only this report is writable by this assignment.
Authors of final reviewed source: original worker /root/higher_order_substitution_entry_astra_r1 plus PRIMARY /root as coauthor of the three disclosed elaboration repairs. The earlier handoff's original hashes describe its historical freeze, not the final repaired bytes below.

## Proof and falsifier review

- Compared every Value/Comp/Adapter constructor and typing rule in HigherOrderSyntax with both mutual renaming and substitution definitions/proofs. RenamingTyped constrains successful lookup facts only; lift_typed supplies precisely one new binder and shifts substituted values. Arbitrary contexts and higher-order types remain quantified. Both intersection premises, both union branches, delay, view, scope, expose, fail and dynamicCall are covered.
- Lambda bodies lift once; lambda result consumers receive the OUTER substitution. Adapter bodies then lift through their own input. This matches the actual lambda typing rules and avoids capturing the parameter as a consumer variable. Bind, union and request continuation introduce their respective single binders; request payload and operation metadata remain outside the response binder. Iteration through nested lambdas follows the mutual recursion. Types, ordered operation arguments, receipt, paths and views are retained by value substitution.
- Environment.realize actually sequences address/current-store reads and aborts on failure. Captured and captured_index derive a successful read for every typed finite-layout index. CellsTyped is explicitly conditional for arbitrary stores; the filler cannot supply a typed layout entry. The resulting typed substitution is consumed by close_body, close_bound_body and close_adapter.
- fresh_function_closes supplies its CellsTyped premise from embedFunction_typed hf and push_current, then applies the real successful finite capture to an arbitrary typed higher-order body. No arbitrary native-cell typing axiom is inserted. The return, delayed argument, invocation and request examples consume this chain. fresh_lexical_read separately connects the appended binder with the same newly written current cell. The global reference in freshLayout is an address witness, not a claim about native ModuleDef allocation.
- Value entry uses force/bind; Computation entry substitutes the unforced carrier. captureEntryPlan closes body under the parameter and consumer under its own binder, retaining the caller's already closed carrier. consumeResult runs after the body. Wrap's input direction is c→a and remains under delay; output b→d follows the inner call. sourceApply binds the callee and shifts argument free indices beyond that binder before creating its delay. The var-0→var-1 equation and concrete higher-order example distinguish capture mistakes.
- LambdaEntryPlan and WrapEntryPlan retain full receipts/adapters. Their computation projections do not prove operational metadata erasure, fresh owner/receipt creation, dispatch safety or a native Wrap case. Source note states these limits explicitly. The untyped old Original wrapper substitution counterexample is valid; no false unconditional old/new commuting theorem is asserted.

## Source correspondence audit

Inspected the exact native Apply lowering/evaluation, Callee delay allocation, Closure saved environment, Value/Computation entry, ValueEntry/RecordDefault, lookup/extend/bind, ReceivedValue and ExecutableValue owners cited by the source note. The note matches these definitions: argument delay captures caller environment, closure body uses saved environment after dispatch substitution, Value forces and Computation binds the carrier, and ordinary parameter binding allocates a current cell. Native substitute_environment composes dispatch and does not syntactically substitute values. Native callbacks, unit/record/default handling, view/interface/dispatch and owner retirement are expressly outside the proved typed constructions. No full native closure-body readback or production authority is claimed.

## Recorded verification and integrity

Read-only hash/JSON inspection independently confirmed all 69 contract pins and 39 accepted prior module source/output chains across six pinned receipts. All current final sources, import artifacts and receipt inputs match recorded hashes. Every recorded invocation has equal before/after input hashes. Final source text retained in the receipt matches the actual files.

Seven recorded Lean invocations total 3.0426380339995376 seconds: failed source rows 1/3/5 remain visible; final Substitution row 2, Environment row 4, Entry row 6 and query row 7 succeed without timeout, stderr or warning. Compared the failed/final source texts: the repairs are exactly mutual unionCase indentation, explicit arena/env/store arguments in fresh_function_closes, and captureEntryPlan record-update layout. No claim or premise was weakened by repair.

The query contains 73 check/axiom pairs (69 module declarations and four named example proofs), 21 examples, and 73 corresponding axiom reports. Reported nonempty axiom sets are only [propext] and [propext, Quot.sound]. Inspected the query terms, runner command construction, dependency checks and recorded output. No sorry, Classical.choice, new axiom or native_decide shortcut is evidenced in the reviewed proof. This review did not rerun Lean or authenticate kernel execution independently of the existing receipts; those recorded runs remain primary-owned deterministic evidence.

Reviewer executions: read-only file inspection, digest comparison, JSON parsing and source diff only; zero Lean/build/test/native invocations, no Git operations, no children. One initial read-only Python invocation failed because `python` was absent; repeated with `python3`, without any file mutation. No scratch files.

## Parent application and limits

HO-SUBSTITUTION-1 is eligible for primary acceptance for the full accepted finite HigherOrder grammar, with the exact quantified renaming/substitution statements reviewed here. ENV-CALLABLE-1 gains a genuine constructed callable-current-cell/capture/body-closing instance and both modes gain typed captured entry plans. Arbitrary native layout/value/recursive-graph/body/dispatch and source pattern/schema correspondence remain OPEN at primary source/native intake. Full Call, Force, original inference A/B, original source language and operational safety are not closed by this review. Other parallel theory artifacts were not reviewed. NO_SAFE_CODE_SLICE and no production promotion remain appropriate.

Next action: PRIMARY adjudicates this review and records acceptance of these exact bytes; primary alone owns integration and parent-status synchronization. No repair request or new authority is introduced.

## Frozen byte identities

- `tasks/agent-loop/sprints/higher-order-substitution-entry-20261025-r1.md`: `b8acedd01e960b4198bacd09f4420b394613279538d3c0e5a2d94c45114a6dbc`
- `tasks/agent-loop/sprints/parallel-theory-20261025-r1.md`: `0751276e8eedf50d113475a0ef1c41b27b7ffd77cc4ccc28761e3cc9e792ff76`
- `notes/theory/lean/YulangClosure/HigherOrderSubstitution.lean`: `19910452c45b20761ec06dc7e15f94c94b95014ff00f3f5296af005b9adf6f30`
- `notes/theory/lean/YulangClosure/HigherOrderEnvironment.lean`: `84a461fdff85e7321cf090ba2bb72a7d90415515a2da1eb15e1287ef0361ab83`
- `notes/theory/lean/YulangClosure/HigherOrderEntry.lean`: `c9cb839ff6b34ed97c5d72f9e020437d32175cf517a5841a3a024764747c213b`
- `notes/theory/2026-10-25-higher-order-entry-source-map.md`: `b58c4d4a449ac9cc671e5f9c0d95a1d3345d0923b3db5db3a82f6bc1e67ac996`
- `tasks/agent-loop/inbox/20261025-higher-order-substitution-entry.md`: `5d8ce563713a04a66476ae103bc793525fd2856a2cb07099aaec62ca9cfbc1e4`
- `tasks/agent-loop/inbox/20261025-higher-order-substitution-entry-r1-verification.jsonl`: `8e5c0f3b8be37879f9009b8e5ed57a2911b6d130e3ae690fc66a3e43554a5a25`
- `notes/theory/lean/.lake/higher-order-substitution-entry-r1-check.lean`: `a188fd20c8963adc2ded621afa591cb31896b2b5d7100def2cc00331a2c7a9e4`
- `notes/theory/lean/.lake/higher-order-substitution-entry-r1-run.py`: `07fcabcf2fc3fff144dd4ba67638891607717cb5c0020abea186fcba2a3ffc11`

## Runtime and STOP

Acknowledged actual review start: 2026-10-25T06:37:50+00:00.
Review/report freeze: 2026-10-25T06:39:16.825269+00:00.
Elapsed to report freeze: 86.825269 seconds of 300-second grant.
STOPPED at report freeze; no active process, no descendants, no background work. Sole leased report is frozen; all writes cease with this receipt. Original and amended contracts remain unchanged.
