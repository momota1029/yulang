# Sprint ordinary-hir-application-admission-implementation-20261017

Status: IMPLEMENTATION-READY; revision 3. Rev1 remains frozen in commit
`b1f15a81a`; rev2 remains frozen in commit `a949c2807`. Branch
`research/simple-sub-intrusion`; authority/adjudication baseline `606416278`.
The user adopted the reviewed resource-only correction to rev4 §2; exact receipt
is `notes/progress/2026-10-17-ordinary-hir-application-error-reference-adoption.md`.
Implementation may start under the exact leases below; no production promotion.

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
> carrier outcomes and occurrence ordinals remain unchanged. Resource accounting
> counts every physically retained aggregate error-ID reference R; the adopted
> output-sensitive bound is O(V+E+R), with a quadratic worst case in V.

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

## Implementation lane — Luna/high after amendment and pre-code review

Owner: Luna/implementer, <=1710 active seconds; the amendment and pre-code
architect review are CLEAN, and Luna has recorded user adoption. Exact writable paths:

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

## Adopted resource correction and implementation obligations

Astra's frozen proof candidate: `notes/theory/2026-10-17-ordinary-hir-call-projection-preservation.md`, SHA-256 `226d389d8fb68b6ddec328dd0f6ece4a4f3f2e344eff3f434d10b0a3d02b37ad`; handoff rev1 SHA-256 `28cc30876831203661ea237c20925249ac48ed5a9cc7fa648c36491dcb51d062`. Its family falsifies rev1's uniform linear bound on all retained flat Apply error references. It does not refute an original Call theorem or authorize narrowing. The exact frozen amendment candidate is `notes/design/2026-10-17-ordinary-hir-application-error-reference-accounting-amendment.md`, SHA-256 `e8b53a773675ba54f0cb5dcc4d62a993e8dd16954e0c92c58fdfc80c620d411e`; handoff SHA-256 `23f637cdb64ef6ab237fef6dacb4abeec06bf19efa75d8f8f2d0202c09a67d80`.

The user adopted this resource-only correction after the sequential compiler, spec and architect reviews. Exact adoption is recorded in the receipt above. Implementation must materialize each Apply list once; Group forwards its child errors without cloning complete lists; checked arithmetic covers child lengths, cumulative R, byte sizes and occurrence ordinals; each complete destination is fallibly reserved before writing/publication; any count/allocation failure aborts the unpublished module/stage with no partial list or duplicate/truncated diagnostic. Report R and actual reference allocation/storage counts for clean and unresolved spines and Group-wrapping cases. Any API, diagnostic, observable-ID or source-grammar change returns to the semantic/architecture boundary.

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

The immutable proof and amendment passed sequential compiler, spec and architect
reviews; Luna adjudicated the resource correction after explicit user approval.
After implementation, freeze
the combined proof, applied source diff and source manifest. Obtain sequential fresh reviews: compiler
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

Fresh cap 4020s: coordination120 charged; Astra450 charged and270 retired;
proof reviews210 charged and unused90 retired; amendment author90 charged;
pre-code architect90 charged; implementation1710; applied reviews480; regression
pre/post240; two Cargo invocations240; reserve30. Current actual charges960,
retired360, remaining named allocation2700; these sum to4020. Charge actual
runtime; no prior sprint budget carries over. At most one
author runs at once. Three inherited UNKNOWN
assignments retain quarantined leases and capacity; reserve two slots for
review/integration. One Astra assignment only, <=8 substantive stages, no
children. One heavyweight Cargo process at a time. Do not exceed the two listed
Cargo invocations or 120s each.

Stop at cap, another counterexample, dependency/pin mismatch, recovery outside
the adopted grammar, conflicting identity, allocation/publication failure with
no specified recovery, need for an unleased owner, or a proposed semantic
change outside the adoption receipt. The known R lower bound is adopted and handled under the output-sensitive
resource account; it does not stop implementation under the explicit obligations above. Continue the other lane only if its exact lease and
inputs remain independent. No blanket cleanup, reset/stash, unknown-lease
reclamation, theorem weakening or production promotion.

At sprint close report: original theorem conditions genuinely discharged (0
unless a reviewed result applies directly); new implementation/test behavior;
remaining unproved and the next single cut. Commit/push only a reviewed
coherent milestone after checking the full outbound range.
