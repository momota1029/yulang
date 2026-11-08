# Sol B4 outer protocol result — partial, not E1

Date: 2026-11-08. Work was confined to this clone; no branches, commits,
pushes, archived source restoration, or changes to `spec/` were made.

## Outcome and exact stopping point

The requested full interval resolver and X6/X8–X12 conformance are **not
finished**. The self-contained result is a conditional, fixed-frontier outer
protocol with one recursive entry and independent tree/classification
exactness theorems. Its input is an abstract request and an executable
frontier producer with a separate local judgment. No concrete Yulang interval
producer has been supplied. Thus the theorem is a generic recursion result,
not `common_role_registry_exact` or B4 E1 under the approved interval statement.

The design was written before the Lean module:
[`2026-11-08-b4-outermost-resolver.md`](../design/2026-11-08-b4-outermost-resolver.md).
It specifies the intended demand, centreless bounds, visible declarations,
ordinary constraint state, K2 priority, merged capture substitution, all where
children, and finite dictionaries, and explicitly marks the missing bridges.

Code: `lean/Yulang/CommonRoleOutermostResolver.lean`.
`resolve` recurses on accessibility of the **independent** where-child
relation. It retains every child, in order, in a finite tree. Its projection
returns a finite dictionary only if every child succeeds. The producer's
frontier correspondence and accessibility are explicit theorem hypotheses,
not axioms or implicit source assumptions.

The artificial execution check in
`lean/Yulang/CommonRoleOutermostResolverChecks.lean` retains two identical
children and constructs two identical leaf dictionaries. It is intentionally
not labeled as any X case and provides no source conformance evidence.

An independent read-only reviewer found no defect in the conditional theorem.
The review identified documentation errors and a lifecycle limitation; those
were recorded/fixed before the final gate. Specifically, children return trees,
not updated ordinary states. Their constraints are not threaded into siblings
or recollected at parents. Also, cross-child rejection/ambiguity/pending
summary priority is a generic protocol policy, not the spec's K2 rule about
competing candidates for one demand. Neither point is claimed solved.
The configured `prover` role and its config files were absent in this clone;
no prover agent ran. The primary constructed this bounded derivation and a
separate available agent reviewed it. Full B4 remains open.

## New theorem statements, with quantifiers and hypotheses

Names below have prefix `Yulang.CommonRoleOutermostResolver` unless otherwise
specified. Let `P : Protocol Request`; `P.Local` is the independent local
judgment. `FrontierExact P` abbreviates

```
∀ q f, P.frontier q = f ↔ P.Local q f
```

`Child P.Local c q` means there exist a declaration key `k` and child list
`cs` such that `P.Local q (selected k cs)` and `c ∈ cs`.

* `resolve_tree_exact_of_frontier_exact`: for every type `Request`, every
  `P`, every `exact : FrontierExact P`, every `q : Request`, every
  `a : Acc (Child P.Local) q`, and every proposed `tree : Tree`,
  `resolve P exact q a = tree` iff `Resolves P.Local q tree`. `Resolves` is
  independently inductive; selected keys and all ordered child derivations
  must agree. There is no successful-output premise.
* `resolve_exact_of_frontier_exact`: for every type `Request`, every `P`,
  every `exact : FrontierExact P`, every `q`, every
  `a : Acc (Child P.Local) q`, and every proposed `r : Result`,
  `classification (resolve P exact q a) = r` iff `Classify P.Local q r`.
  `Classify` means there exists an independent finite resolution tree with
  an independent summary derivation yielding `r`. It never calls `resolve`.
* `resolve_unfold`: for every `Request`, `P`, `exact : FrontierExact P`,
  `q`, and `a : Acc (Child P.Local) q`, the entry equals one frontier
  inspection, immediately returning a terminal tree or recursively mapping
  the same entry over the complete selected child list.
* `classification_exact`: for every finite tree `t` and result `r`,
  `classification t = r` iff the independent `Summarizes t r` derivation
  exists. No hypotheses.
* `classifications_exact`: for every list of finite trees `ts` and result
  list `rs`, `classifications ts = rs` iff `All₂ Summarizes ts rs`.
  No hypotheses; lengths and order are exact.
* `combine_exact`: for every key `k`, result list `rs`, and result `r`,
  `combine k rs = r` iff independent `Combine k rs r`. No hypotheses.
  Success requires exactly a list of selected dictionaries, one per result.
* `all_successful`: for every result list `rs`, if rejected, ambiguous and
  pending are all absent from `rs`, then `rs` equals the map of `selected`
  over its extracted dictionary list. These three absence hypotheses are
  explicit and are the only hypotheses.
* `any_rejected_exact`, `any_ambiguous_exact`, `any_pending_exact`: each
  quantifies every result list `rs`, with no hypotheses. The corresponding
  executable `any` flag is true iff that outcome belongs to `rs`.

Names with prefix `Yulang.CommonRoleOutermostResolverChecks` concern only
the artificial Boolean-request protocol in that module:

* `frontier_exact`: for every Boolean request `q` and proposed frontier `f`,
  that fixture's executable frontier equals `f` iff its independent `Rule q f`.
* `leaf_accessible`, `root_accessible`: the fixture's false and true requests,
  respectively, are accessible in `Child Rule`, with no hypotheses.
* `duplicate_children_retained`: the entry on the fixture root equals key 1
  with exactly two key-0 leaf trees, with no hypotheses.
* `complete_finite_dictionary`: classification of that entry equals the
  key-1 dictionary with exactly two key-0 leaf dictionaries; no hypotheses.
* `independent_classification`: the independent fixture judgment classifies
  its root as that same completed dictionary; no hypotheses. This uses the
  single outer exactness entry, not a hand-written expected-answer assertion.

All these theorem names are registered in `lean/Audit.lean`.

## Per-goal status and exact remaining work

| Task/goal | Status in this task | Remaining work |
| --- | --- | --- |
| Step 0 design | Written, Draft | Concrete source state representation and actual producer still absent |
| Step 1 outer entry/exactness | Partial | Only the fixed-frontier conditional protocol is implemented |
| Step 2 X6, X8–X12 | Not started as source conformance | Instantiate an actual Yulang interval producer and resolve these concrete inputs through it |
| Step 3 declaration-derived descent | Not started | Derive accessibility on the richer carrier from checked declarations and K2 |
| B4 E1 | Partial, open | The definitions and bridges listed below; conditional theorem is not completion |
| B1/B5, B2, B3 | Not worked on here; existing partial results unchanged | Their pre-existing source/cast/effect/pattern obligations remain |
| B6 | Not started | Await the complete source boundaries |

The remaining work is **not only a list of unproved small lemmas**. The
concrete producer and state lifecycle still need definitions:

1. Define the full source interval protocol over the actual finite visible
   declarations, ordinary graph/slot allocation and source demand. Then
   prove `source_frontier_exact`: for **every** checked visible registry,
   admitted source snapshot and demand, and proposed frontier, its computed
   frontier equals that proposal iff the independent interval propagation
   rules classify it that way. The rules must include root/head interval
   consistency and both cross directions, same-head lifting recursively in
   inherited invariant context, repeated/merged captures, deferred record
   subtraction, K2 before ambiguity, and the entire substituted ordered
   where/associated list. No existential head-point assignment replaces
   this producer. This is the concrete instance of `FrontierExact` that is
   missing; it is **not** asserted as a theorem in this change.
2. Implement and prove `where_state_recollection`: for **every** such shared
   state and selected declaration, updates produced by every child flow to
   siblings and parents and trigger the appropriate recollection. Either
   supply a state-threading driver or prove that the shared snapshot is
   saturated/stable before invoking this fixed-frontier theorem. This cannot
   be inferred from the arbitrary `Request` type.
3. Prove `checked_interval_children_accessible`: for **every** source registry
   accepted by the actual declaration checker and every admitted starting
   request, the corresponding independent generated-where relation is
   accessible, using stable Paterson descent and K2 on the richer interval
   carrier. The finite-Form arithmetic theorem alone is insufficient. No
   assumed role rank, fuel or depth cutoff may replace this proof.
4. Prove source adequacy and the qualified result-family connection for
   **every** admitted source request and proposed result, under the actual
   source visibility, sharing, kinds and levels. Align the four-way outcome
   policy with the source judgment. No such source theorem is claimed here.

## X1–X24 status after this task

No conformance status changed. `lean/SpecExamples.lean` was kept unchanged,
both because no additional source case was proved and because the task's
hard rule prohibits editing existing Lean modules outside its explicit list.

| ID | Status |
| --- | --- |
| X1 | PROVED (existing) |
| X2 | PROVED (existing) |
| X3 | PROVED (existing) |
| X4 | NOT-EXPRESSIBLE-YET |
| X5 | PROVED (existing) |
| X6 | NOT-EXPRESSIBLE-YET |
| X7 | NOT-EXPRESSIBLE-YET |
| X8 | NOT-EXPRESSIBLE-YET |
| X9 | NOT-EXPRESSIBLE-YET |
| X10 | NOT-EXPRESSIBLE-YET |
| X11 | NOT-EXPRESSIBLE-YET |
| X12 | NOT-EXPRESSIBLE-YET |
| X13 | NOT-EXPRESSIBLE-YET |
| X14 | NOT-EXPRESSIBLE-YET |
| X15 | NOT-EXPRESSIBLE-YET |
| X16 | NOT-EXPRESSIBLE-YET |
| X17 | NOT-EXPRESSIBLE-YET |
| X18 | PROVED (existing) |
| X19 | PROVED (existing) |
| X20 | PROVED (existing) |
| X21 | NOT-EXPRESSIBLE-YET |
| X22 | MISMATCH (existing) |
| X23 | NOT-EXPRESSIBLE-YET |
| X24 | NOT-EXPRESSIBLE-YET |

## Verification

Initial unchanged checkout:

```
cd lean && lake build --wfail
Build completed successfully (1099 jobs).
cd lean && lake env lean --trust=0 Audit.lean
Axiom allowlist passed for 80077 declarations from Yulang modules
Axiom allowlist passed for 41 declarations from SpecExamples modules
```

The combined command exited 0. Focused module build and execution check also
passed. The check actually evaluated to the finite key-1 dictionary with
two key-0 children, rather than only proving a proposition about a callback.

Final required combined command exited 0:

```
cd lean && lake build --wfail && lake env lean --trust=0 Audit.lean
```

Build tail:

```
✔ [1100/1101] Built Yulang (3.2s)
Build completed successfully (1101 jobs).
```

Audit allowlist and tail:

```
Axiom allowlist passed for 80376 declarations from Yulang modules
Axiom allowlist passed for 41 declarations from SpecExamples modules
'Yulang.CommonRoleOutermostResolver.resolve_exact_of_frontier_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleOutermostResolverChecks.frontier_exact' does not depend on any axioms
'Yulang.CommonRoleOutermostResolverChecks.leaf_accessible' does not depend on any axioms
'Yulang.CommonRoleOutermostResolverChecks.root_accessible' depends on axioms: [propext]
'Yulang.CommonRoleOutermostResolverChecks.duplicate_children_retained' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleOutermostResolverChecks.complete_finite_dictionary' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleOutermostResolverChecks.independent_classification' depends on axioms: [propext, Quot.sound]
```

`git diff --check` passed. Searches of the new Lean modules found no
`sorry`, axiom declaration or `native_decide`. Every new theorem uses only
the permitted axiom allowlist. The final gate ran after the last Lean edit;
only this report was added afterward.

No new question notes were created. No unapproved source semantics were
adopted. Actual source resolution, X6/X8–X12 conformance, declaration-derived
termination, source state recollection and qualified-family adequacy could
not be verified because they have not been implemented/proved by this prefix.
