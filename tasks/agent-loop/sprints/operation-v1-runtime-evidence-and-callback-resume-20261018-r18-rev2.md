# r18 revision 2 — clarify callback execution order

This is an execution-order clarification to r18 revision 1 only. It changes no goal, source domain, success predicate, exact lease, model lane, budget, parent scope or production status. Revision 1 remains frozen as historical authority.

The exact order for the specimen is:

1. The matched handler arm evaluates `k response` using the exact source-linked callback value.
2. The raw saved continuation returns that closure as the catch expression's value.
3. While the enclosing outer catch remains active, the surrounding source Apply invokes that returned closure with its captured environment.
4. The callback issues `outer::next`; the live outer catch selects and evaluates its actual matching arm, which returns integer `42`.

The callback Apply is required to be an actual source/runtime application joined to the exact response definition. It is **not** asserted to occur inside the raw saved suffix. Do not identify static HIR occurrence IDs with dynamic continuation, closure or request IDs; retain an explicit checked bridge. The closure must be produced by the same HIR and successful v1 candidate whose exact r17 field receipt was supplied.

All r18 revision 1 constraints continue to hold: explicit research-only entry, function response admitted only by exact source/candidate evidence at both runtime response gates, existing `local_grant` preserved, live outer-handler evidence, no completed receipt before actual completion at 42, and no success on mismatch, conflict, absent handler, exhaustion or other result. The parent theorem remains OPEN/closure0.

This amendment stays within the five playground source/test paths and the existing implementation handoff already leased in revision 1. The current implementation author was notified of the changed contract hash before continuing. No solver file lease or additional resource is granted.
