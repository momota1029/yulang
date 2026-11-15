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
