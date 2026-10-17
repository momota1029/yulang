# Sprint ordinary-hir-application-admission-implementation-20261017

Status: ADMITTED by Luna after exact user adoption of rev4. Branch
`research/simple-sub-intrusion`; baseline `5fbceb68d`; revision 1.

## Parent and fixed outcome

Parent: original Yulang type-inference/execution goal, preserving the original
Simple-sub A/B claims, quantifiers, source domain, source/native correspondence,
F1/FK1, N-Transport, Call, soundness, principality and termination.
No original parent gate is presumed discharged.

Adopted contract: design rev4 SHA-256
`2e61e2acb1a8981bb78592accc48207a24a5cc4c75278e100f63eb960acfeea3`;
exact adoption receipt is pinned in `current.json`.
Baseline: `5fbceb68d`. Parenthesized source-key audit SHA-256
`e8a320be0e78ecc2c5ee5210338476740c03a1fae61fb2747ec39636286ad501`.

Fixed outcome: implement ordinary HIR admission for the adopted structural
`Atom | Group(E) | Apply_ml(E,E) | Apply_call(E,E)` grammar and establish the
following bounded projection invariant by structural induction and regression:

> Every admitted expression preserves its associated operand tree, lexical
> resolution, exact source-key ownership, body-root identity, and dense local
> error/diagnostic references through ordinary HIR, while all existing source
> carrier outcomes and occurrence ordinals remain unchanged.

Apply the invariant to the fixed accepted source and identify exactly which
structural premise of the original Call/source bridge follows. It establishes
no Call typing, source T, semantic Call adequacy, soundness, principality,
termination or parent theorem closure. Original domains and quantifiers stay
intact.

## Proof lane — Astra first, no author overlap

Owner: one `astra_prover`, requested medium, <=720 active seconds; no descendants.
Write only:

- `notes/theory/2026-10-17-ordinary-hir-call-projection-preservation.md`
- `tasks/agent-loop/inbox/20261017-ordinary-hir-call-projection-preservation.md`

Develop explicit admission/source-projection judgments for Atom, retained
Group and both application constructors. Prove by induction: exact association
shape and operand order, lexical atom resolution, source-key uniqueness,
root/descendant occurrence lineage, atomic rejection on recovery/unsupported
children, carrier noninterference, and final dense diagnostic ownership under
rev4. Include concrete derivations for `my apply f = f 1` and
`my answer = apply id`; state the exact original Call antecedent each derivation
supports and the first still-missing source/native or semantic premise.
Proactively formulate useful derived inference interpretations where the
premises are independently available; never infer semantic callability from
structural Apply. Preserve all A/B and F1/FK1 quantifiers. STOP and freeze before
the implementation writer starts.

## Implementation lane — Luna/high after proof freeze and review

Owner: Luna/implementer, <=1800 active seconds; exact writable paths:

- `crates/yu-hir/src/module.rs`
- `crates/yu-hir/src/source_identity.rs`
- `crates/yu-hir/src/shadow.rs`
- `crates/yu-hir/tests/ordinary_application_admission.rs` (new)
- `crates/yu-solver/tests/research_accepted_call_vertical.rs`
- `tasks/agent-loop/inbox/20261017-ordinary-hir-application-implementation.md`

Implement private staging, checked root mappings, post-carrier descendant
allocation, collision/identity failure atomicity, exact operand diagnostics and
all rev4 compatibility conditions. Keep opt-in shadow behavior unchanged.
Add focused Atom, Apply_ml, Apply_call, Group(Atom), Group(Apply), nested Group,
unsupported/recovery, unresolved/ambiguous operands, collision, mixed root and
carrier ordinal regressions. Extend the accepted-call vertical to use ordinary
`lower_module`; it must establish zero structural recoveries, zero HIR errors,
ordinary `CandidateInference`, constraint propagation, exported definitions,
and source-authenticated fresh uses/call observations where existing APIs
actually provide them. If the ordinary route cannot provide one stage, report
its exact owner and keep that stage OPEN; do not fall back silently to the
shadow route.

No solver-semantic edits, blanket expected-output updates, fixture rewrites or
unleased consumers. If another owner is required, stop that change and return
its exact path and dependency to Luna before writing it. A passing vertical is
implementation evidence only, not source T or theorem proof.

## Pins and relevant prior evidence

The adopted rev4 contract and source audit retain all 48 exact pins. Direct
implementation owners at baseline `5fbceb68d`:

```text
crates/yu-hir/src/module.rs                                      2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e
crates/yu-hir/src/module/local_source.rs                         ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5
crates/yu-hir/src/module/source_annotation.rs                    b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f
crates/yu-hir/src/source_identity.rs                              aa97bc34be51644cf944b2813af47ad9243a8eb270850eeb6df34b9cddb3b3a2
crates/yu-hir/src/shadow.rs                                       2dffd7fd6542eed9fd3346e0672e76197c248be9c84334f341c4d612234b7ee9
crates/yu-hir/tests/ordinary_expression_source_carrier.rs         36ec22c58cf790ed910ed4af93d6f9a860263efe6a5fa3fdefb7291ad3c03fbf
crates/yu-solver/src/shadow_apply.rs                              bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf
crates/yu-solver/src/shadow_candidate_source_crosswalk.rs          392d665579a74810134846e1274c0c9ce975a7eb0e2cfb9ad79a07af2cd2eeb0
crates/yu-solver/tests/research_accepted_call_vertical.rs         78fd0d4c38df86def4cd4aefb37e164f71269eb58cd9a53b370bc42e42f9a963
notes/progress/2026-10-17-original-goal-minimal-cut.md             ee28746816f843e9e5729a879492c7b7415dcbf6a85d96e81f3eee439f5dcb8c
```

Reuse the reviewed dependency cut at
`notes/progress/2026-10-17-original-goal-minimal-cut.md` (bounded map, not a
global minimality theorem). The projection proof does not resolve the earlier
OPRESP-DEFAULT/ENTRY semantic cut. Keep F1 distinct from FK1; both remain OPEN.

## Review and verification

After Astra STOP/freeze, primary checks handoff hashes and assigns fresh,
sequential reviews of the immutable proof: compiler referee <=180s, spec auditor
<=120s. Then Luna implementation begins. Freeze the combined proof, applied
source diff and source manifest. Obtain sequential fresh reviews: compiler
referee <=180s, spec auditor <=120s, architect <=180s. A separate regression
auditor <=120s reviews the exact pre-run diff and commands. Only after CLEAN
pre-run acceptance, one primary verification owner runs these commands
sequentially, each with a 120s wall cap and no implicit retry:

```sh
cargo test -p yu-hir --features shadow --test ordinary_application_admission
cargo test -p yu-solver --features shadow-apply-candidate --test research_accepted_call_vertical
```

A fresh regression auditor <=120s checks the post-run frozen receipt and result;
no reruns or unreviewed changed bytes. Record known formatter/CI failures
separately from the two exact new command outcomes.

## Resources, runtime truth, and stop conditions

Fresh cap 4020s: selector/primary coordination120, Astra720, proof reviews300,
implementation1800, applied reviews480, pre/post regression reviews240, Cargo
verification240, reserve120. Reconcile prior assignments; charge real current
runtime receipts. At most one author runs at once. Three inherited UNKNOWN
assignments retain quarantined leases and capacity; reserve two slots for
review/integration. One Astra assignment only, <=8 substantive stages, no
children. One heavyweight Cargo process at a time. Do not exceed the two listed
Cargo invocations or 120s each.

Stop at cap, counterexample, dependency/pin mismatch, recovery outside the
adopted grammar, conflicting identity, allocation/publication failure with no
specified recovery, need for an unleased owner, or any proposed semantic change
outside the adoption receipt. Continue the other lane only if its exact lease and
inputs remain independent. No blanket cleanup, reset/stash, unknown-lease
reclamation, theorem weakening or production promotion.

At sprint close report: original theorem conditions genuinely discharged (0
unless a reviewed result applies directly); new implementation/test behavior;
remaining unproved and the next single cut. Commit/push only a reviewed
coherent milestone after checking the full outbound range.
