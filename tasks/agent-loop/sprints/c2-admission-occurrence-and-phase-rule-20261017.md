# Sprint c2-admission-occurrence-and-phase-rule-20261017 — rooted source clause

Status: READY for Luna validation and sequential exact leases.  
Branch: `research/simple-sub-intrusion`  
Baseline: `d67aa4ba8` (prior producer-incomplete sprint closed REVIEWED-PARTIAL).  
Parent Goal: type inference and execution implementation with proof; original FORWARD-FIRST-CALL A/B remain OPEN.  
Authority: user's explicit continuation and authorization to change workflow and draft new bridge rules; governing Function-call-view direction and adopted source-interface scopes. No new semantic adoption or compiler-code authority.

## Fixed outcome and gates

Original source: `receive(f : Unit -> alpha+) = let g = f(Unit) in g(Unit)`, with `c1=f(Unit)`, `c2=g(Unit)`, original `A1`, `F2@(sigma2,Delta2)`, `xi=(nu,K,D)`, `B_in` at F2's incoming ports and original `a2`. Preserve all original FORWARD-FIRST-CALL A/B domains, providers, contexts, worlds, observations, response/resumption/future cases and source/native correspondence.

The prior sprint was `REVIEWED-PARTIAL`: its S-F2 assumed a clause set and phase partition; family placeholders did not instantiate an original predicate/occurrence; phase recursion was unspecified. Its proof correctly left original VIEW and CHECK OPEN. Do not repeat that shape.

Success requires one rooted, concrete c2 derivation containing an instantiated predicate, complete telescope, actual source occurrence, actual insertion/use substitutions and constructor graph. State whether its introduction is already authorized. If not, write an explicit **new candidate rule**, with its own meaning and observable behavior, unselected. Do not call candidate predicates original or assume equivalence.

### Source / implementation-design lane — Luna/high, max 360 active seconds, first

Exact leases:

- `notes/design/2026-10-17-c2-admission-occurrence-and-phase-rule.md`
- `tasks/agent-loop/inbox/20261017-c2-admission-occurrence-and-phase-rule.md`

Use the exact actual c2 `Apply(Name(g), Unit)` occurrence and owning Function-view/declaration rule. Distinguish native Apply/Demand allocation from semantic descriptor introduction. Produce:

1. The rooted declaration/definition/use derivation at c2, with exact source-owner judgments and a concrete predicate over its original telescope; if none exists, label it candidate and state its admission effect.
2. Complete dependent operand/evidence/provider/world/event/result telescope and actual IF-Insert/root/IF-Use substitutions for that occurrence; no marginal reconstruction.
3. The actual constructor graph containing the occurrence. Define phase behavior recursively over every Union/Conj/Bind/Scope/Ref node in that graph, retaining branch tags, dependent scopes and shared witnesses. If a node cannot be grounded in existing authority, mark it candidate and show the exact branch behavior.
4. One staged residualization or equivalent typed construction if useful: retain unready C/P clauses under their original binders; do not flatten alternatives, split a shared witness or hoist a later result/live grant.
5. At least one fully instantiated source predicate and a derivation tree; no `all guards`, desired Clause2, `WF_Dec(F2)`, desired VIncl/CIncl, or full phase graph as premise. State exact original-to-candidate behavior difference, if any, with a source-qualified tuple where available; if no such tuple exists, mark it UNVERIFIED and do not call the choice decision-ready.

Stop at 360s or if no concrete owner input is available. Passing the gate means the artifact contains the instantiated predicate and actual constructor derivation; otherwise proof does not start. Any newly selected admission meaning returns to explicit authority routing before code.

### Proof lane — Astra, max 720 active seconds, only after source gate

Exact leases:

- `notes/theory/2026-10-17-c2-admission-phase-and-carrier-laws.md`
- `tasks/agent-loop/inbox/20261017-c2-admission-phase-and-carrier-laws.md`

Use only the frozen derivation and pinned selected rules. Construct phase handling on its actual graph, retaining alternatives/tags, dependent Bind, Scope/shared witnesses and original domain. Apply it back at original c2. Attempt the occurrence's carrier VIEW action and CHECK introduction separately with complete `B_in` target-domain coverage and same-tuple guards. Separate selected-rule consequences from conditional consequences of the unselected candidate. No whole desired contract premise and no extension beyond this producer's actual graph. Success is a source-applicable construction with precise remaining premises or a source-qualified counterexample/owner law; otherwise freeze the exact first obstruction.

## Implementation path and authority

Useful implementation contribution is a rooted construction/phase specification tracing `candidate_source`, `candidate_call`, `candidate_scheme`, and `shadow_apply` through source generation, retained incidences, native propagation and checking consumer. These native owners do not establish semantic Function admission. `NO_SAFE_CODE_SLICE` remains until an applicable source rule and proof are independently reviewed and any changed meaning is adopted. No compiler edit, tests/builds/probes/runtime execution, expected-output change, semantic adoption or production promotion is authorized.

## Pinned dependencies

All inputs are rehashed before source work, at proof handoff and before review. Add an exact pin by versioned contract revision before relying on any newly discovered governing source.

| Input | SHA-256 | Limit |
|---|---|---|
| `notes/theory/2026-10-16-first-call-joint-forward-preservation.md` | `f71cc442bcccb23f7e6f1aa6221b089abb8c24d1c4ce01fecef37995541c16b6` | Original theorem/quantifiers; no narrowing. |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` | Inference authority/economy. |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` | Approved direction; detailed generator remains open. |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` | User-selected direction, no detailed clause generator. |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` | Selected IF-Insert/IF-Use scope. |
| `notes/theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` | Constructor cases; retains original law premises. |
| `notes/theory/2026-10-17-receive-inferred-function-view-formation.md` | `7cb867df64f1d931b1667f33a6c323448d687c5d0d7fdcf9bac7535577f72590` | F2 introduction frontier and owner requests. |
| `tasks/agent-loop/inbox/20261017-receive-inferred-function-view-formation.md` | `a60a7ca1e5ea6b9d30adff7f1141b183bc8b9c8f6b8eda1302664721e7081e3a` | Parent application; no constructor. |
| `notes/theory/2026-10-17-receive-c2-open-check.md` | `8ad6272b9ef0612e7d7cf6915d5bb242ab29fe3968a38124d803758f56b82f02` | Actual c2 source positions/frontier. |
| `notes/design/2026-10-17-source-formation-proposals-adoption.md` | `d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa` | Only named source proposals selected; other gates open. |
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` | Membership consumes admission, cannot form it. |
| `notes/design/2026-10-08-captured-closure-constructor-definition.md` | `6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd` | Selected Strict scope only. |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` | Generalization downstream, no missing introduction. |
| `notes/progress/2026-10-17-receive-admission-clause-construction-review.md` | `807dc9e58171fe0ddb375ed3a3db9277dbdbd376950524822b6e00f551dc2708` | Previous partial receipt and correction. |
| `notes/design/2026-10-17-receive-admission-clause-constructor.md` | `c29d6d9627188985b4189f88dc325bf0561bf674122824fb4278d638d343dfc9` | Failed producer; reuse only as rejected/partial evidence. |
| `notes/theory/2026-10-17-receive-admission-clause-view-check.md` | `6c7d42745949115aa54d23a292e8cebbd22923948a71ec632ebdb8d5ae301845` | Exact VIEW/CHECK obstruction and schema/source distinction. |
| `tasks/agent-loop/inbox/20261017-receive-admission-clause-constructor.md` | `91bbc0e2d3f92c56503079b4e670b2e007416c4d0cda31f1d6e3490936688478` | Previous producer handoff. |
| `tasks/agent-loop/inbox/20261017-receive-admission-clause-view-check.md` | `112e9e43856870cd0e70051add9479f70190da1f3c725d77add95670e4478772` | Proof handoff. |
| `crates/yu-solver/src/candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` | Read-only source Apply allocation/retained candidate generation. |
| `crates/yu-solver/src/candidate_call.rs` | `cbad9cf51a05343eb7a29ab77aac520891467a8aa4edc3201ea3d91f978984a1` | Read-only actual Apply observation and unresolved supplier ledger. |
| `crates/yu-solver/src/candidate_scheme.rs` | `52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a` | Read-only native Function graph shape. |
| `crates/yu-solver/src/shadow_apply.rs` | `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf` | Read-only native demand/admission consumer. |

## Reviews, resources and stop conditions

Fresh **1800s**: source360 + proof720 + compiler/spec/architect reviews360 (120 each) + coordination120 + reserve240. No carryover from the prior sprint. At most one Astra assignment, no descendants. Authors and reviewers run sequentially while three inherited UNKNOWN reservations remain quarantined. Unknown leases are retained; no replacement writer overlaps them.

Review order: fresh `compiler_referee`, `spec_auditor`, `architect`, after both lanes freeze. Acceptance requires a rooted predicate/constructor derivation, explicit graph phase behavior with shared/dependent evidence preserved, precise separate VIEW/CHECK results, no overclaim, and Luna adjudication. The source predicate/introduction is a proof-start gate. On failure or cap, source lane freezes exact evidence and proof does not launch. Any changed authority or dependency returns to Luna before reliance. At closeout, update durable receipt/current state, run static sprint check, consult selector and push an explicit-path coherent checkpoint.

No tests/builds/probes/runtime execution are budgeted or authorized. Checker's output is static workflow evidence only.
