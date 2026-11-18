# Actual singleton-to-many reserved-slot example

Use an actual zero-node nominal State with seed10. Propagate a declaration
whose head is var7 with one binding (7,(0,1)); this reserves all owner keys but
adds no merge block. Its actual active reads are0 and1. Propagate again with
an added binding(7,(1,0)). For any assignment satisfying the fresh cross bounds,
construct a model of the actual second propagation while keeping0 and1.
No new key/nonallocated condition is needed; active pool stays bounded by seed.
The old full-source pool fails248's protected-pool condition, when declaration
membership supplies the reserved slots. These are actual allocation primitive
states, not a claim that the solver's source scheduler reaches this transition.
