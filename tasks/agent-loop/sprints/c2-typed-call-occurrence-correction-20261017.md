# Sprint c2-typed-call-occurrence-correction-20261017 — typed native call seam

Revision: 3 (pin correction and exact sequential review output leases).
Status: READY for Luna validation and sequential exact leases.  
Branch: `research/simple-sub-intrusion`  
Baseline: `8f012935e` (prior sprint REVIEWED-PARTIAL).  
Parent: original FORWARD-FIRST-CALL A/B at c2, all original quantifiers preserved and OPEN.  
Authority: user's authorization to continue and draft bridge rules; selected native constraint construction and approved Function-view direction. No semantic admission change or compiler-code authority.

## Outcome and fixed boundary

Correct the previous unselected `C-AppArg` candidate and establish exactly what the c2 source Apply generates natively. The prior candidate mistakenly called the native negative Function's argument child negative; it is Positive. Do not flip endpoint polarity by intuition. State the actual typed whole-call relation, any conditional Function decomposition child, and why neither is an original F2 admission rule. Pending call check `Q` cannot form F2 or its admission.

Original source remains `receive(f : Unit -> alpha+) = let g = f(Unit) in g(Unit)`, `c2=g(Unit)`, `a2` the original Unit argument, `F2@(sigma2,Delta2)`, `xi=(nu,K,D)`, `B_in` the original complete incoming view. Preserve all A/B domains, carriers, providers, contexts, worlds, observations, responses/resumptions/futures and source/native correspondence. VIEW/CHECK, semantic IF(g), and original F2 introduction remain OPEN.

### Source correction — Luna/high, max 180 active seconds, first

Exact leases are sequential revisions on:

- `notes/design/2026-10-17-c2-admission-occurrence-and-phase-rule.md`
- `tasks/agent-loop/inbox/20261017-c2-admission-occurrence-and-phase-rule.md`

Pin and retain predecessor artifact SHA `e835e269207666ba25f03680c80d1c3da32f5da8883598574b344e6d0f78d5d9` and handoff SHA `814f3a723664b9a48d81a282efb8c9becaca20ffaae7d0f807b15cf2695b6204`. Correct with a new artifact/handoff revision, never same-revision mutation. Map exact c2 source occurrence, owner/cause/slot, native callee-positive and Demand-negative operands, argument child polarity, and source child identities. State the actual whole-call relation and, separately, conditional Function decomposition relation only if a positive Function callee is actually supplied. Mark both as ordinary call-check constraints. Explicitly withdraw `C-AppArg` as admission. Preserve the useful Scope/Lambda/Bind/Call/Ref and identity results, with typing limits.

Gate: the correction must contain the true typed native occurrence relation and explain operand owners; it must not present `Q`, endpoint shape, or function comparison as admission. No code, semantic adoption, tests, probes or execution.

### Proof lane — Sol, max 180 active seconds after source freeze

Exact leases:

- `notes/theory/2026-10-17-c2-native-call-operand-correspondence.md`
- `tasks/agent-loop/inbox/20261017-c2-native-call-operand-correspondence.md`

Independently derive source-to-native operand correspondence for the corrected actual c2 call, and conditional function decomposition with its real premise. Reuse the previous graph-retention result only within its premises. Determine exactly what evidence this typed call relation supplies; do not turn it into F2 admission, semantic `IF(g)`, original VIEW or CHECK. A proof that it supplies none of those is an acceptable result. No source-qualified counterexample or semantic selection unless genuinely established.

## Review, implementation, resources

Fresh sequential compiler_referee and spec_auditor reviews, each max90s. Require correct polarities, source identities/causes and scope, exact conditionality, clear separation from admission, and no overclaim. Both outputs stop before review. Luna alone adjudicates and integrates.

Review outputs are exact sequential leases, opened only after each preceding reviewer STOPs:

- compiler_referee: `tasks/agent-loop/inbox/20261017-c2-native-call-operand-correspondence-compiler-review.md`
- spec_auditor: `tasks/agent-loop/inbox/20261017-c2-native-call-operand-correspondence-spec-review.md`
- Luna adjudication/closeout: `notes/progress/2026-10-17-c2-typed-call-occurrence-correction-review.md`

Reviewers are read-only against the frozen source/proof bytes and may write only their assigned receipt. They must review the typed source equations, constructor-success premises, slot/cause ownership, conditional Function decomposition, the versioned source pins, and non-promotion limits.

Useful implementation contribution is the corrected source/native correspondence only. `NO_SAFE_CODE_SLICE` remains: no compiler change until an independently reviewed/adopted semantic rule and exact end-to-end code authorization. No code, tests/builds/probes/runtime, expected-output changes or production promotion.

Fresh **600s**: source180 + proof180 + compiler/spec reviews180 (90 each) + coordination30 + reserve30. No carryover. No Astra assignment. Three inherited UNKNOWN reservations remain quarantined; authors/reviewers sequential; no descendants. Checkpoint exact frozen research artifacts promptly; update current/receipt and consult selector at closeout or a changed authority/owner seam.

## Exact pinned inputs

Rehash all 12 listed inputs before source correction, proof handoff and review. Any mismatch requires a versioned contract update before reliance.

| Input | SHA-256 | Use/limit |
|---|---|---|
| `notes/progress/2026-10-17-c2-admission-occurrence-phase-review.md` | `35536c07acd17b8531eae9e62f12c7089f712385685812814df2a58c7bea1bf2` | Prior adjudication and exact polarity finding. |
| `tasks/agent-loop/sprints/c2-admission-occurrence-and-phase-rule-20261017.md` | `1b2c953011a2ffbfb7fdc8d0783869b7b85ef2e2a9824e23d284de1417fdf491` | Failed prior source gate and assignment boundaries. |
| `notes/design/2026-10-17-c2-admission-occurrence-and-phase-rule.md` | `e835e269207666ba25f03680c80d1c3da32f5da8883598574b344e6d0f78d5d9` | Frozen predecessor; revision2 corrects it. |
| `tasks/agent-loop/inbox/20261017-c2-admission-occurrence-and-phase-rule.md` | `814f3a723664b9a48d81a282efb8c9becaca20ffaae7d0f807b15cf2695b6204` | Frozen predecessor handoff. |
| `notes/theory/2026-10-17-c2-admission-phase-and-carrier-laws.md` | `3dc2aee3594ecadbf42a6dee4b52c6767d058cbc5fcca0ee89067fd81f28c865` | Prior bounded phase/VIEW/CHECK analysis. |
| `tasks/agent-loop/inbox/20261017-c2-admission-phase-and-carrier-laws.md` | `cdea6601d58bf41c812209bb48eb385801770d976646b1fd36632d499eaab04f` | Prior proof handoff. |
| `crates/yu-solver/src/shadow_apply.rs` | `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf` | Exact Demand construction and native call admission. |
| `crates/yu-solver/src/candidate_call.rs` | `cbad9cf51a05343eb7a29ab77aac520891467a8aa4edc3201ea3d91f978984a1` | Authenticated source children and port polarity. |
| `crates/yu-solver/src/candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` | Actual Apply occurrence and candidate source emission. |
| `crates/yu-solver/src/lib.rs` | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` | Function subtype decomposition and contravariant children. |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` | Approved source direction; no semantic admission derivation. |
| `notes/theory/2026-10-16-first-call-joint-forward-preservation.md` | `f71cc442bcccb23f7e6f1aa6221b089abb8c24d1c4ce01fecef37995541c16b6` | Parent quantifiers and c1 premise limits. |

No other semantic dependency is presumed. The pin list itself is revalidated; missing direct source law returns to Luna before reliance.
