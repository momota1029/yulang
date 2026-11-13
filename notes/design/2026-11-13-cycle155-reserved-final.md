# Cycle155 reserved output final semantics

Goal: use the general installed-packet instance and ordinary context-extension transport
lemmas for a real reserved-output install. For every final assignment satisfying the
installed state's Models, prove the current-context Instance and dictionary Evidence.
No final stability is assumed by this proof. Inspect whether refresh can newly expose
the previously unallocated output before asserting Stable; if so report that boundary.
This addresses the current-context part of evidenceNode, not the general B4 field.

## Verified result and boundary

The existing installed packet plus current-context transport proves Instance and Evidence
for every final journal model, and for any ordinary-only continuation. A general
finite-arity repeated-scalar nominal test lemma recovers output2 = nominal(0,int,int,int).
The raw source0 has the same value, so the journal entails output2 = source0.
However the raw context permits a countermodel where output2 is int. Therefore the
actual equality-feedback rule is still enabled: the installed state is NOT Stable.
The next actual Value step preserves the whole journal model set and its current
Evidence, and is reachable from the original empty-journal source. Its terminality
is not claimed. The selected Classify judgment is proved for the installed snapshot,
showing explicitly that selected classification plus a dictionary does not imply
saturation has finished. No source or declaration semantics changed.

Soundness: current_instance/current_evidence/final_evidence.
Auxiliary: arbitrary finite repeated-scalar nominal semantic reconstruction,
classification and trace reachability, exact model preservation, and nonstability.
Completeness/principality/general evidenceNode remain outside this result.

## Further verified continuation

The actual equality successor is itself nonstable: a certified carrier extension
from2 to3 slots makes reserved source2 a Known ternary nominal. Snapshot validity
is proved for every journal model using source/output equality; it adds no model
constraint. The refresh preserves Models exactly and the positive model survives.
This is the second post-install Value step (third from the initial state); the final refreshed state's stability is open.
