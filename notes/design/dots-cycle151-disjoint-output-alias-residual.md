# Cycle151: disjoint named-output alias selections, an unproved test case

Status: investigation / partial kernel-checked obstruction. No actual reachable
stable counterexample, no failure of the language specification, and no V5
bridge refutation is claimed. The general V5 count remains6/14supplied,8open.

## What is proved

`GeneralDictionarySelectedAliasConflict` proves four universally quantified
implications for the existing boundary, without changing it:

1. `branch_selected_key`: any `BranchAt registry state focus key model` agrees
   with an actual current `Local.selected selectedKey children` at that focus.
2. `joint_related_selected_key`: a `Joint` key agrees with the selected key at
   every actually Related site.
3. `different_selected_no_joint`: if a focus and a Related site actually select
   different keys, no Joint key exists for the focus.
4. `support_different_selected_no_joint`: the same implication for support Local.

The first proof uses Prepared from BranchAt to form a genuine Survivor, then
actual uniqueness. The other proofs project the same Joint assignment. No
recorded packet, Coherent, Scheduled, missing-packet assertion, or speculative
counterexample is a premise. These results are necessary-condition lemmas only:
they do not supply premises exhibiting different selected keys.

## Why the original same-binder sketch is insufficient

`GeneralNominalAllocation.capture.outputs` uses origin
`(root.identity, declaration.id, 2, binder, 0)`. Distinct alias occurrences do
not automatically share their private output binder source. Demand aliasing is
not equality of every allocated frame source. Merge adds `outputAtoms` for
matching requested output names. Two disjoint name sets alone therefore do not
force the two private binders to have the same value. An argument that merely
assigns their private binders different values does not refute Joint.

The sharper candidate uses different **selected declaration keys**, rather
than assuming identical private sources across aliases. Checked requires
unique declaration IDs, not disjoint heads. Current Prepared includes
materialization Consistent for the actual named requests, so it is necessary
to test whether disjoint named demands can select different same-head branches.

## Concrete construction route, NOT yet established

Use three roles P, C, Producer and a source with the point nominal chain
`list(list int)`. A P declaration has two where clauses with the same captured
`list int` input to C but different occurrence identities:

- C_A requests x=int and p=int.
- C_B requests y=str and q=str.

The requested name sets are disjoint, so their merge would add no cross-name
outputAtoms. Give C two checked declarations with the same `list a` input:

- d1 has associated x=int and y=int.
- d2 has associated x=str and y=str.
- Both have associated p=z and q=z, with output-only z produced by
  `where Producer a (out=z)`.

All four names must be declared by role C and have complete associated equations
in both declarations. Producer descends to `a`, so the intended normalized
Paterson comparison is strict; this must still be checked by Lean, not assumed.

The proposed finite path is P install, same-input C_A/C_B merge, then certified
refresh and equality completion for P's four scalar output targets. The hoped-for
classification is d1 uniquely selected at C_A and d2 uniquely selected at C_B.
If established, the new implication excludes Joint at either focus even before
any C packet exists. The installed P journal would remain inhabited because it
only constrains its own four requested targets, not either C frame's future z.

For an EvidenceNode test, let Producer's terminal declaration return str.
A proposed bad current assignment sets C_A's unrecorded private z to str while
P's p target remains int. Child Producer Evidence could then hold in that same
assignment, but C_A's required p=z equation would fail. This is only a proposed
same-model construction. EvidenceNode also requires stability of its immediate
children; it is not enough to show the parent cannot install.

`GeneratedChildren` may be the simpler first target to test: C_A would be
selected with nonempty children while its nonexistent packet contributes no
child edge. That too requires the entire actual reachable-and-stable certificate.
A failed bridge of this form would not by itself establish a false final
language soundness theorem or a successful complete recursive classification.

## Exact outstanding proof obligations

- Actual declarations, role signatures, output binder Produced/Scoped fields,
  constructor scope, and all checked normalized descent fields.
- InitialSource, exact deterministic source IDs, no allocation collisions,
  P's guarded installation and model, real same-input merge guard/novelty.
- A certified refresh using only already registered parent targets; source
  support and every model-preservation direction, not a manually populated raw
  journal. Existing OutputMergeRefresh/ContextComplete modules are templates,
  not certificates for this new configuration.
- Actual Local selections at both sites: eliminate the opposite discriminator
  via Consistent failure, establish metadata/linkage/freshness, non-K2, no other
  pending candidate, and actual DecisionGuard. Shared source-supported list
  heads suggest empty support, but this is unproved for the new state.
- Full Stable: parent installs already Committed; every C install contradicts
  different-selected-no-Joint; sites are present; all same-input pairs already
  aliased; no novel equality; no possible Known-improving refresh; point-closed
  nominal descriptors exclude reobserve. Unknown unused reserved IDs need
  explicit flexible-model arguments. Merely blocking installs is insufficient.
- For EvidenceNode, additionally construct child Evidence and child Stable,
  prove the bad model satisfies the full journal, and derive parent non-Evidence
  from the actual materialization equation. An unlisted future z may block
  enqueue by failing Linked, but this must be proved for exact IDs.

No safety/semantic restriction should be added to force this candidate to work
or to rule it out. The next step is a bounded formal fixture proving or failing
one of these concrete premises, not another wrapper assuming the desired Joint.
