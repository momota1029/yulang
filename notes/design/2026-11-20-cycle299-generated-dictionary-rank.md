# C299: same-model composition from selected generated edges

Distinguish (A) the B4 raw kernel's steps, (B) semantic selected dependency
edges at one frozen reachable state, and (C) a finite table's listed edges.
A decreasing measure for (B) gives no measure for (A). A supplied
`Classify` derivation already includes the finite tree; this cycle will not
use an assumed derivation or child evidence as its tree producer.

Design a scoped table whose key lookup denotes **one actual demand** in a
single source state. The table's checked side certifies each selected node
and contains every ordered child entry, including repetitions. Allow an
explicit unknown/missing entry; no completeness by negation of a lookup.
A constructive Nat rank strictly decreases on all child table entries, not
on observations or generated membership alone. A fuelled reader consumes one
unit per level and traverses children in order; show sufficient fuel of
rank+1 and exact source classification (at least for the table scope).
Show the same input model reaches every child evidence proof: do not splice
unrelated existential witness models. For the actual mixed boundary, separate
the local `Current` provider from recursion: if a child has a current effect,
its local evidence consumes only partner proofs for children already reached
under the same saturation root. No Rust parser changes, no general raw
termination or full-source `InhabitedAvailable`.

Prefer a concrete depth-2 **dictionary** fixture (not constructor output
depth alone). If not supported by an existing real raw execution, keep any
deep synthetic or proof-local table clearly distinguished from the C277
actual one-edge regression, and look for an existing two-install boundary.
