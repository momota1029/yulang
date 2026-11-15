# Cycle 209: current-frame evidence reconstruction

Status: checkpoint, not completion of I38. Source: fresh I38 and cycle208.

The installed-plan theorem in cycle208 needs a current `Frame` for the stored
plan. A historical plan carries the old context, while installation changes the
current context. Stored membership alone therefore does not discharge that
premise. No context-equality assumption is to be hidden in the final field.

First establish a model-independent fact: for any checked registry, current
state, focus and key, any two current Frames have equal ordered children. This
uses registry declaration-key uniqueness and deterministic argument inspection,
not injectivity of type constructors. Then derive unique source readback and
exact node inversion for the total-expression/default Evidence. These are
soundness/representation lemmas, not unconditional EvidenceNode.

The central remaining work is historical-plan reinspection (or construction of
a fresh jointly compatible plan). Keep current Frames and old stored plans
separate. Full evidence and fresh production remain explicitly open.

## Verified checkpoint

Six modules / 36 theorem declarations: checked current-frame children are
model-independent; exact source-tree readback is unique even across assignments;
all total expression constructors preserve full-carrier equivalence; explicit
and default bodies transport through equivalent actual values. Stored-parent
reinspection now uses a NEW current frame and OLD stored plan, with equality of
persistent report data rather than impossible current-context identity.
Trace-derived configuration removes registry/seed/constructors/interpretation
from the remaining hypotheses: only declaration, input-site and erased report
equality remain in `Configuration209.reinspection_data`.

This is a real restricted replay result, not the unrestricted field. Improving
reobservation can replace report data. Arbitrary reobservation and fresh parents
remain open; no closed counterexample to I38 was found.

## Second checkpoint / final scope (10:14 UTC)

The cycle did not stop after the first checkpoint. Continued work removed the
syntactic input-center equality hypothesis: `SemanticReplay209.nominal_certificate`
requires checked registry, corrected-boundary reachability, current Frame, stored
historical parent at the same occurrence/key, point focus, nominal/variable head
syntax, descriptor-preserving Refines, and the specified current model. It derives
the current certificate without assuming a new certificate, same center names,
same declaration, or report equality. Output expressions remain unrestricted.
`nominal_generated_children` in that module needs no model or point premise.

`HeadTransport209` transports actual head schemas for all query forms from semantic
root/binder agreement. `FrameSemantics209` derives binder equality between current
frames; `CurrentCertificate209.node_iff` fixes a chosen current witness frame in the
exact node-evidence characterization. These do not establish evidence existence.

`CollapsedCenters209` additionally replaces syntactic point endpoints by their
semantic equivalence in the fixed model, with a complete restricted replay
certificate. `CollapsedExamples209` proves a positive non-syntactic-point case.
`TransportExamples209` proves distinct-center positive defaults and a negative
noncollapsed interval case; `ReplayExamples209` tests complete packet recentering
for a scalar head. The negative case refutes an omitted lemma hypothesis, NOT the
assigned EvidenceNode target or the language design.

Still open: arbitrary improving reobservation (not Refines), noncollapsed input
intervals, and fresh selected parents without a matching historical plan.
No new closed refutation of the assigned target. No change to Local, Models,
Evidence, Step or selected-input semantics. The original global target remains.
All 102 checked declarations, with quantified types: [inventory](2026-11-15-cycle209-declarations.md).
