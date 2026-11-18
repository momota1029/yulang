# Cycle251: fixed slots are not a termination measure

Status: Internal representation regression, not a source counterexample.

A single private target updated by union(var target,var target) has a fixed name
domain and safe snapshot definitions at every stage, yet the expanded syntax
can double at each refresh. It remains semantically equivalent by union idempotence.
A proof of source Acc therefore still needs a source-driven finite measure or
canonical/shared expression representation; target count alone cannot serve.

The regression below concerns arbitrary raw finite updates, not source reachability
or violation of I45. It does not change language semantics. A local idempotent
union constructor is proposed and verified for this narrow duplication family;
it is not a complete normal form or an arbitrary-cycle canonicalizer.
