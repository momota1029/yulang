# c2 admission occurrence/phase sprint — review receipt

Date: 2026-10-17  
Sprint: `c2-admission-occurrence-and-phase-rule-20261017`, contract revision 1  
Contract SHA-256: `1b2c953011a2ffbfb7fdc8d0783869b7b85ef2e2a9824e23d284de1417fdf491`  
Baseline: `d67aa4ba8`  
Outcome: **REVIEWED-PARTIAL; concrete source gate FAILED; parent OPEN**

## Frozen artifacts

- [Source candidate](/home/momota1029/rust/yulang/notes/design/2026-10-17-c2-admission-occurrence-and-phase-rule.md), SHA-256 `e835e269207666ba25f03680c80d1c3da32f5da8883598574b344e6d0f78d5d9`.
- [Source handoff](/home/momota1029/rust/yulang/tasks/agent-loop/inbox/20261017-c2-admission-occurrence-and-phase-rule.md), SHA-256 `814f3a723664b9a48d81a282efb8c9becaca20ffaae7d0f807b15cf2695b6204`.
- [Phase/carrier proof attempt](/home/momota1029/rust/yulang/notes/theory/2026-10-17-c2-admission-phase-and-carrier-laws.md), SHA-256 `3dc2aee3594ecadbf42a6dee4b52c6767d058cbc5fcca0ee89067fd81f28c865`.
- [Proof handoff](/home/momota1029/rust/yulang/tasks/agent-loop/inbox/20261017-c2-admission-phase-and-carrier-laws.md), SHA-256 `cdea6601d58bf41c812209bb48eb385801770d976646b1fd36632d499eaab04f`.

All 22 contract dependency hashes and these five review targets matched for the three sequential reviewers.

## Finding and adjudication

All three reviewers found one **MAJOR** source-rule defect: the candidate defines `Aarg_c2^cand(tau2) := Unit+ <= arg(N2)` and describes `arg(N2)` as a negative endpoint, while the pinned native construction and observer establish that this argument child is **Positive**. The ordinary native constraint consumer requires a positive lower and negative upper endpoint. Thus this displayed native reading is not a typed relation, and it cannot discharge the contract's source gate requiring an instantiated typed predicate and constructor derivation. The proof correctly identifies this and refuses typed C-AppArg introduction. This is a defect in the candidate draft, not compiler behavior. No patch, polarity coercion, semantic adoption, or code authority follows.

The exact semantic owner must now do one of two things in a new versioned source proposal: identify the intended relation with correctly typed actual operands and an authentic c2 occurrence, or explicitly define a different relation on the positive operands and its meaning/authority boundary. Neither may be silently inferred from the native endpoint shape. The missing semantic `IF(g)[m_g]` and the full F2 introduction are still separate source obligations.

The source gate is **FAILED** for this revision. The proof attempt is retained only as a bounded partial analysis, not as proof-start eligibility, original clause construction, or theorem closure. Its useful bounded results are:

- The actual source occurrence graph remains `Scope/Lambda/Bind/Call/Ref`, with the c2 body under the c1 result binder and original Return/Request substitution order.
- For a supplied well-formed complete telescope and already typed predicate witness, identity substitution preserves its fields and witness. It constructs neither the telescope nor its typing.
- Source marker retention preserves the concrete source wrappers; the inferred F2 semantic descriptor graph is absent. No Union/Conj cases are invented, and descriptor phase validity is not proved.
- Original VIEW remains OPEN at the I2-to-full-B_in action covering every target. Original CHECK remains OPEN at semantic g-root use, actual original guards and whole-argument inlet introduction. No source-qualified counterexample or observable admission difference is established.

No compiler code slice is safe. Source T, native MODEL, F1/FK1, all original A/B quantifiers, VIncl, whole argument compatibility, CIncl, hygiene, soundness, principality and production remain OPEN.

## Independent reviews

The compiler_referee, spec_auditor and architect reviews were sequential, read-only and STOPPED. Each verified the 22 dependencies and five outputs. They independently reported the same MAJOR polarity/type issue; the spec and architect reviews found no additional conformance/architecture defect. The proof's bounded refusal and graph-retention limits were judged accurate.

Observed review intervals and charges: compiler 18s/20 charged; specification 20s/20 charged; architecture 15s/20 charged. Requested/effective model telemetry remained UNKNOWN. No tests, builds, probes or runtime execution occurred. `python3 tools/agent_sprint.py check` passed after compact-state reconciliation; it is static workflow evidence only.

Source author interval: 227s, charged 240/360. Proof author interval: 306s, charged 360/720. Total sprint charge: **660/1800 seconds** (source 240 + proof 360 + reviews 20+20+20); all unused allocation retired at closeout with no carryover. All authors/reviewers STOPPED; no descendant or unknown new lease.

## Next owner

The next action is a source-side correction of `C2-CAPPARG-POLARITY-20261017`, not another proof over its untyped formula. Preserve the graph-retention and typed-identity sub-results. Revisit semantic `IF(g)[m_g]` only with actual owner evidence. After a correctly typed instantiated rule passes an independent source/spec gate, a new proof may attempt its carrier VIEW and CHECK laws. Any new admission meaning remains unselected pending authority. The parent goal stays ACTIVE.
