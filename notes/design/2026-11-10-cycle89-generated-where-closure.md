# Cycle89: finite actual where-declaration closure

Status: Draft. Date: 2026-11-10. Scope: first-order fragment of bridges 2/3.

Objective: compute all recursively generated where goals from the actual
`Roles.Impl.constraints`, not a caller-supplied finite visit list, fuel or graph.
Use the existing unique-head policy and matching substitution. At zero or
multiple matching heads, retain the goal and stop expanding that goal. At a
unique head, expand every child, including siblings after a failing child.
Preserve source order and multiplicity. Termination follows the existing checked
Paterson theorem at each recursive call, without a cutoff or reachability oracle.

The independent edge judgment quantifies an actual registry declaration and
an arbitrary substitution that matches its head, with uniqueness expressed by
membership and `Matches`, before any resolver is consulted. The recursive path
judgment is then independent of the closure function. Prove for arbitrary finite
registries satisfying `WellFormed` and arbitrary root/target goals that computed
membership is equivalent to this path judgment. Prove closure under real child
edges and that every generated node has a root provenance. Connect all generated
goals to independent `RoleConstraints.Resolves`, with exact preservation of
root success and explicit retention of missing and overlapping obligations.

This is not the full interval-based B4 source carrier. It does not synthesize
associated annotations absent from `Roles.Impl.constraints`, infer unknown scalar
receivers, validate source parser lowering, choose invocation identities, or
claim arbitrary Common normalization is Paterson-safe. The existing first-order
carrier and its declaration WF are explicit inputs. Five B4 bridges stay open.

Spec 6.2 and 6.3 supply unique-head selection, all-where conjunction and strict
size decrease. The audit oracle C3-PARENT and C3-PARENT-NEG provide existing
concrete acceptance/rejection cross-checks; they are not a new runtime run.


Implemented boundary: finite closure also has exact missing/overlap/success
classification and an executable classifier equal to `Roles.resolve`. The
checked source entry agrees with its existing version. `checkedClassify`
computes the declaration certificate using `CheckedRoles.checkDatabase`.
The source-head function remains an input to source execution; this cycle does
not connect closure registration to the inferred scalar expression entry.
