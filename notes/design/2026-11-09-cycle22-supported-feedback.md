# Cycle 22: first-hit stability and supported final equations

Partial goal: determine whether the first-hit source producer justifies cycle21's
monotonicity, and isolate exactly the equations supported by final source reachability.

`production` takes the first hit, even if `frontier` is pending/ambiguous. An earlier
literal head can become a hit after a slot materializes and displace a later capture
head. Thus ordinary information growth alone cannot justify Reach persistence.
This is an implementation issue, not a new language choice.

Data: arbitrary checked unary registry, computed source closure, annotations with
fixed associated receivers, arbitrary ordinary observation state. Independent judgment:
for every Reach node and each annotation, every Computed associated result satisfies
its output equation. Executable observation: enumerate actual reachable nodes,
concatenate their annotations, run actual associated batch from the original seed.
Prove exactness for every assignment without EmissionMonotone. This is a one-pass
revalidation view, NOT a convergent replacement driver: revalidation can change Reach.
Also prove actual emission monotonicity iff annotated-node Reach persists under
list inclusion, making the remaining assumption exact rather than hiding it.

No existing semantics or theorem is changed. First-hit candidate resolution must be
replaced by frontier-aware guarded derivations before claiming full B4. Five general
B4 bridges remain; this work diagnoses and repairs the observation boundary of bridge2,
not its fixed-point or independent classification obligations.
