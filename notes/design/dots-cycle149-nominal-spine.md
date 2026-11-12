# Arbitrary finite nominal spine exploration

Use an indexed inductive source shape. A leaf records a nominal descriptor
with arbitrary finite linear binder intervals. A wrapper records a nominal
unary descriptor whose sole interval is the point at the next spine slot.
The query is derived recursively from these actual descriptors.

The intended induction quantifies over observation origins whose observed
values are equivalent to the current slot value. This supports nested nominal
paths without assuming resulting projection models. Remaining integration
steps are exact capture bindings, checked intervals, and candidate-private
source models, followed by packet-free terminal evidence.

## Verified result

The structural induction is complete for arbitrary finite unary nominal point
spines. `spine_projection` handles all intermediate tests/anchors and leaf
capture coherence, `spine_bindings` identifies the exact finite allocation list,
`spine_checked` validates every self-check, and `private_models` derives both
private source models and projection validity in the unchanged assignment.
`SpineLeafShape` adds terminal/no-output/actual-lookup conditions, yielding
packet-free selected Instance and Evidence. `linear_covered` embeds the previous
one-level shape. Branching nested constructors, row parameters, repeated binder
names, and nonpoint intermediate slots remain outside this fragment.
