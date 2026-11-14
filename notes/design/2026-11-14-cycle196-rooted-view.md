# Cycle196 rooted reinspection support

Design before proof: avoid registry-wide `Rechecks`. Attach a structural
certificate to a *finite source dictionary*: at each node, compare only visible
declarations whose id is that node's key, and only bounds actually returned by
source argument lookup for that node's occurrence. Traverse its actual children,
including repetitions. This certificate mentions neither semantic Evidence nor
Models. Transport an existing derivation by induction over this finite support,
retaining source occurrences, keys, children and raw payload exactly. Unused
registry declarations and unrelated argument bounds incur no reinspection duty.

Implementation: `GeneralNominalRootedView196.AtNode` uses declaration membership,
key equality, and the real argument lookup equation. `Support.node` carries that
condition plus recursive support for each actual child. `node_transport` opens
the actual old Instance witness to obtain its declaration and lookup bounds;
`tree_transport` inducts on Support and pairs each case with old source Evidence.
`readback_transport` packages the exact same source tree and readback relation.
`node_of_variables` automatically discharges local checks for variable-only
matching declarations. `support_of_global` recovers the earlier stronger case.

Remaining: a support certificate is still required for the transported tree;
this theorem does not synthesize source evidence or discover reachable source
trees. It does not prove that every actual refresh preserves queried reports.
The new-state model remains explicit, as required for branch semantic transport.

Audit: `Audit/Cycle196Rooted.lean` checks five theorem types/axioms and the
allowed-axiom gate. Focused target only; frozen checkpoint files remain unchanged.
