# Local raw-continuation certificate: dependency and guard audit

Date: 2026-10-16
Status: independently reviewed complementary static feasibility audit; no parent closure
Baseline: primary-pinned `4dbf6fe1e`; source owners unchanged from the reviewed `1b`/`ddda` inputs
Lease: this new note only; concurrent producer proof and shared records untouched

Review provenance: mathematical `capture_math_review` and source/scope
`capture_source_review` independently reviewed frozen audit SHA-256
`be3d31a45f3280f01e9535bd4cd63c946a615e68cd0a1c158bb5367d6561d0b1`
alongside the independently produced local T_e proof. No blocking/major audit
finding. The primary applies that proof only under its original valid
Gamma/d0/full-f premises; this census does not independently construct them.

## 1. Scope and new bounded evidence

Audit the concrete source case with `choose:Unit->alpha`,
`alpha=Unit->[ctrl]Int`, f calling choose, and
`receive(f:Unit->alpha){my g=f();g()}`. The outside shallow arm binds k,
constructs zero()=0 and h()=k(zero), then calls k(h). The prior capture audit
established the control path through the actual first return h and g=h;
this pass concerns the independent typing dependencies, not that control trace.

Two local facts are useful beyond the previous registration audit:

1. A legitimate source description choice for the original A1 declaration
   gives a finite identity checking leaf, rather than an inference from
   equal denotations. This makes the caller's F_g suffix independently
   typable under its hypothetical result binder without k, h or an actual
   first result.
2. Handler arm checking is an OPEN derivation under its declared hypothetical
   raw-k interface. Its conditional proof can be part of an independently
   formed caller context before actual k membership is proved. Importing the
   future actual k certificate into that context would introduce a cycle.

No source-qualified counterexample or complete accepted-source certificate is
claimed. The actual pending-response contract and all carrier/phase/guard
leaves identified below must still be consumed by the independent producer.
This audit does not construct or certify its theorem, and the producer's
new local-certificate note was not read.

Governing sources: [SourceGeneralize](../theory/2026-10-08-source-generalize-definition-and-proof.md),
[Unit inlet/context assembly](../theory/2026-10-16-written-unit-arrow-inlet-construction.md),
[semantic input and Bind](../theory/2026-10-08-call-semantic-input-realization.md),
[Strict pending clauses](../theory/2026-10-08-captured-call-closure-introduction.md),
[operation arm binding](../design/2026-10-02-operation-instance-binding-package.md),
and the frozen repaired [raw-callable construction](../theory/2026-10-16-source-raw-callable-validation-construction.md).
The last result is used only conditionally on its stated original T_e.

## 2. Finite source checking at the original A1

Let q_c remain the actual first Apply's original Desc declaration, at its
original component/type scope. For this ONE source witness, choose the
well-scoped description term alpha for q_c. Alpha precedes q_c at this
local cut. This uses SourceGeneralize §3.4's independent source description
choice (lines 305–311), not a change of the source occurrence or root.
Section7.1's identity-closure example independently illustrates a source
endpoint assignment followed by an actual checking derivation.

After that source substitution, the comparison at the original checking
position has the finite rule derivation:

```text
Desc-choice(q_c := alpha), at q_c's original scope
Identity(alpha, alpha), by source checking §3.2 item1
--------------------------------------------------
the original alpha-to-A1 checking obligation in this source instance
```

The declaration remains q_c=A1, its constraints remain active, and its final
source root is not replaced by alpha. This licenses the corresponding
valuation equality; valuation equality by itself would not license the proof.
It supplies no theorem for another valuation or independent description
frame. In particular it establishes no absence of free A1 in J_raw and no
copy/generalization eligibility claim.

## 3. Backward dependency census of the local T_e

The independently formed Unit inlet d0 retains F_g under hypothetical
`g:Value(A1)` (Unit construction §4, lines 177–245). This is a source
continuation judgment, not an actual g entry or a prediction about f's return.
Under the description choice above its membership hypothesis is full alpha.

| Required local judgment | Independent source of its premises | What it must not assume |
| --- | --- | --- |
| F_g's Name(g) | Its hypothetical full hereditary value binder; Lemma W/Name | No actual first-return packet, h, k or completed f call |
| Whole Unit argument for g() | Unit/Return/Delay and original alpha inlet/context guards | No provider acceptance inferred from Unit shape |
| Complete invocation of the hypothetical g | Full alpha Function membership at the actual supplied provider and independently admitted challenge | No assumption that the body merely has scalar result Int |
| F_g's original final checking/result root | Its actual local result/effect checking proofs and full same-return maps | No replacement of a complete root by printed `[ctrl]Int` |
| Inner pending f/consumer telescope at the choose request | SAME f's full P_F(d0), unfolded at its actual typed pending response/consumer branch; source f is the known choose call | No extraction of a suffix theorem from an untyped Request or whole-scrutinee membership |
| Actual later response/current world | Original declared response alpha, independent compatible history and current-world evidence | No historical-state snapshot, premature response or g binding |
| Rebind and append F_g | Original typed Bind: inner Return's same value/world, full alpha-to-A1 check, actual ResultBind projection and F_g's open derivation | No use of the desired full k Function certificate |
| Further requests/pending/futures | The original inner pending contract plus the same typed Bind rule recursively at its retained event indices | No response-domain filtering, new witness per alias or nominal effect-only substitute |
| Prefix gluing and remaining root R_e | Original phase/operator equations and the typed continuation's actual remaining root | No equation R_e=R_whole and no re-evaluation of completed prefix code |

Semantic-input §6 (lines 476–528) explains exactly the full same-provider
elimination being used. The generic Strict pending clause (captured-call
closure §3.1, lines 162–173) explicitly retains the typed response/raw handle
and unfinished suffix. Semantic-input lines 562–569 then compose the two
typed children by Bind. This is the local combination to inspect; an IF slot
or a raw control equation is not a typed child.

The delicate leaf is the **inner** pending contract, at the actual original
f/consumer root, BEFORE appending F_g. It must give its response-dependent
remaining judgment at the original root and current-state telescope. An
observation-only guarantee or an assertion that all complete f returns are
alpha is insufficient. This audit does not replace that leaf with a whole-
source-to-T_e theorem. The concrete operation/declaration consumer and full
P_F pending clause are its owners.

## 4. Handler checking without a circular actual-k premise

Operation-instance binding §7, lines 311–327, generates the arm body once
under the ORIGINAL declared hypothetical binder

```text
Gamma_arm, k : (Btheta => J_raw).
```

In this case Btheta is alpha; there is no declaration-local binder which can
stand for q_c. Keep the entire J_raw, its exact substitutions and original
scope. This hypothetical binder is a legitimate assumption of the arm
typing rule. It is not a claim that capture has already produced a value
satisfying it.

The finite dependency order is therefore:

```text
open caller F_g derivation, original entry/context guards
open arm derivation under its declared hypothetical k interface
    -> independent context d0
same-f full pending contract at d0 + open F_g
    -> original local T_e
T_e + original raw-response entry/carrier premises
    -> actual k membership (conditional raw-callable theorem)
actual k substituted into the independently checked arm derivation
```

Within the OPEN arm proof, zero's full alpha proof is independent of k.
h's alpha proof may use its captured hypothetical k with its ENTIRE interface;
the final k(h) uses that hypothetical binding and those response proofs.
Neither requires the future actual k membership as an import. The actual
binder is discharged only after T_e establishes the capture's certificate.

An apparent dependency `context admission -> actual k -> T_e -> context
admission` is thus avoidable by the existing open arm rule. This is not
permission to assume the arm accepted or to assume any desired extra
property of k. Its hypothetical interface must already be independently
formed and retain all the real J_raw obligations.

## 5. Full h/zero alpha leaves which cannot be skipped

The public results Int and ctrl are insufficient for the response proofs.
Their complete source Lambda/Strict derivations must cover:

* the original alpha whole-carrier inlet and every admitted Unit carrier,
  including divergence, zero/admin prefixes and any independently allowed
  pending behavior;
* actual Unit Value entry, receipt/Force/rebind/body/return order and original
  immediate context/authority/profile guards;
* zero's primitive Int Return and genuine guarantee weakening from empty
  body support to the declared ctrl bound;
* h's captured FULL hypothetical k certificate, pure Name(zero) carrier,
  original declared response admission, complete k invocation at its actual
  remaining root and its independently justified outward ctrl guarantee;
* full return/world/provider/future clauses, with current history and no
  revival of the selected shallow handler or an old receiving boundary.

In particular arbitrary effects of a Value-entry argument are part of the
COMPLETE invocation. A body-only ctrl bound cannot erase them. The source
alpha entry contract must be shown explicitly. Native operation formation
offers a useful consistency check: `candidate_effect.rs:1534–1542` forms
the nested argument effect without the outer family, and `:1587–1588`
uses ground empty for an omitted operation-context effect port. This is
not a semantic proof of the whole source inlet, nor authority to drop any
existing source guard. It is a concrete owner to compare with the declared
alpha input, instead of silently treating an arbitrary Value argument as pure.

Likewise the raw-k entry contract must admit the particular pure Name carriers
for zero and h at the original response alpha. Name Delay supplies the whole
carrier at `Comp(empty,alpha)`; the declared raw-response entry law supplies
its checking/admission, with the original scope/history guards. The Unit-
inlet theorem alone is not a theorem about every possible alpha carrier.

## 6. Outcome and exact next action

The audit identifies a finite legitimate checking instance and a noncircular
source dependency order. It supports the feasibility of the local
construction; it does not certify all its source leaves. No complete source
acceptance or counterexample follows until the inner pending-field
elimination, exact remaining root, full response entry and h/zero proofs
above are supplied with their actual guards.

Next action: review the independent local producer against the exact inner
P_F pending branch plus F_g composition, and ensure arm compatibility is
proved OPEN under its declared k binder. Do not replace either child by the
whole Catch's desired typing. Keep the entire installed J_raw in the fixed
walk, including every real free dependency. No free-A1 conclusion follows
from the description choice, proof separation, IF incidence or this audit.
Original generalization, full typed-witness, native and production parents
remain OPEN.

## 7. Static evidence and freeze

One bounded static leaf, approximately six minutes to initial drafting; no
tests/builds/probes/Git, runtime execution or primitive changes, children,
code/shared-record writes or measurements. CPU/RAM unmeasured. Only the
leased note changed. Local source reads, hashes and note fence/whitespace
checks are the verification; no independent oracle/checker is claimed.
The repaired raw-callable note is an input at the frozen hash below; its
historical pending-review header is not a producer certification of review.
No new local-certificate producer note was read.

```text
9f41b8c6fc78067d0d454544e20957430abe1ecd01dc0064053e885898aef12c notes/theory/2026-10-16-source-raw-callable-validation-construction.md
ce0846a783af6029c346a6bc82664bd920b6a46429601a4030dd656a3fb07099 notes/theory/2026-10-16-written-unit-arrow-inlet-construction.md
fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a notes/theory/2026-10-08-call-semantic-input-realization.md
0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f notes/theory/2026-10-08-captured-call-closure-introduction.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 notes/theory/2026-10-08-source-generalize-definition-and-proof.md
1eb2cbdb49368b0839d839d6a5e72698bb06252813b00200098e70371645c7c9 notes/design/2026-10-02-operation-instance-binding-package.md
44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9 crates/yu-solver/src/candidate_effect.rs
```

Commit packet: sole new path is this note; baseline `4dbf6fe1e`; no dependency
edits. Initially unreviewed bounded audit, now independently reviewed as above;
no theorem/parent closure. Original proposed checkpoint:
`research: audit local raw-continuation certificate dependencies`.
Shared-record deltas remain primary-owned after independent review.
