# Astra: concrete settled frontier and outer exactness

Date: 2026-11-08. Status: **exactness closed for the settled fragment below;
full B4 E1 remains open**. All changes are uncommitted in this clone.
No branch, commit, push, other checkout, existing theorem, or specification
was changed. Existing Lean edits are append-only imports/audit entries;
README and the lakefile library list also received only additions.

## What is now proved

The real executable local producer is
`CommonRoleSettledFrontier.frontier`. Its request contains a role, separate
lower/upper endpoints, and a finite ordinary state. `Local` is an independent
inductive judgment: it uses `Scan`, `TrialRule`, independent `Inspect` and
`Rigid` judgments, and ordinary-constraint model existence. It does not call
`frontier`, `resolve`, or `classify`.

`CommonRoleSettledFrontier.frontier_exact` proves, for every natural slot
count `n`, every finite declaration list `visible`, every `Request n` `q`,
and every proposed frontier `f`, that `frontier visible q = f` iff
`Local visible q f`. No correspondence hypothesis is supplied. The source
interpretation of counting distinct identities applies to the admitted
`Registry` domain, whose declaration keys are pairwise distinct.

`CommonRoleSettledResolver.accessible` proves, for every slot count `n`,
every `Registry R`, and every `Request n q`, `Acc (Child (Local R.declarations)) q`.
A registry includes proofs that **every declaration passes the actual
stable Paterson/name-coverage check** and that declaration keys are distinct.
A request does not carry an accessibility certificate, rank, fuel, success
certificate, or precomputed frontier. `selected_origin` identifies the actual
visible head and captured payload; `child_decreases` derives strict descent
for every actual generated child from `CommonRoleStablePaterson.check_sound`.
K2 prevents opening regular leaves, including finite unrollings recognized
by graph bisimulation. This proof covers pending and rejecting children too.

`CommonRoleSettledResolver.resolve_exact` proves, for every such `n`, `R`,
`q`, and every proposed outer `Result r`, that `classify R q = r` iff
`CommonRoleOutermostResolver.Classify (Local R.declarations) q r`.
Its companion `resolve_tree_exact` quantifies every proposed tree instead,
and characterizes independent `Resolves`. **Neither theorem assumes
FrontierExact or accessibility.** They instantiate the existing outer
recursion with the newly proved bridges. They do not replace that recursion.

## Exact fragment and exclusions

Included:

- One role argument. Its endpoints are stored separately. If the lower
  endpoint is present, it equals the upper endpoint; this equality is part
  of the admitted request type. The lower endpoint may instead be absent,
  with any concrete upper endpoint, and resolution then defers.
- Arbitrary finite unary constructor spines: variants, required one-field
  records, and nominal constructors with one explicit argument; `int` and
  opaque zero-argument named nominal types; unresolved leaves; structural
  variant/record self-loop leaves and arbitrary finite wrappers/unrollings.
  There is no recursion-depth cutoff. Nominal declaration bodies are never
  opened. Numeric variant identities are even and record labels odd.
- A head has one leaf: a literal or a nonempty list of plain variable names.
  All names at that leaf capture the same entire endpoint pair. The list can
  contain repeated names. `bindings` deduplicates names; the actual generator
  retains all repeated self/cross comparisons. The merged interval meaning
  equals the captured singleton interval. `every_where_substituted` proves
  named lookup for every variable occurrence of every admitted where template.
- Every ordered where clause is preserved, including duplicates. Templates
  can rebuild arbitrary unary prefixes and use captured names or literals,
  subject to the finite stable Paterson and name-coverage checks. The stable
  test is sufficient, not claimed complete for every semantically decreasing
  source declaration. In particular it may reject variable children of a
  distinct-name merged head; X6 has no where clause and is admitted.
- A finite visible registry with unique declaration identities, fixed for
  the entire outer tree. Role mismatches and ordinary incompatibility are
  eliminated before K2; K2 precedes unresolved inspection and candidate
  counting; singleton survivors generate the complete where list.
- Every original atom expressible in the existing family solver grammar,
  in an **auxiliary namespace disjoint from the role type graphs**. All old
  slots are shifted by `Fin.succ`; slot 0 is fresh for the captured payload.
  The candidate path calls `CommonRoleCandidateConstraints.solve`, retaining
  all original atoms and generated self/cross atoms. Known rigid clashes
  compile to an inconsistent ordinary atom. No existential head-substitution
  search defines applicability. The existentials in the proof are models of
  generated ordinary constraints, as permitted by the contract.

Excluded, deliberately:

- Non-singleton intervals, unequal endpoint heads, general interval merging
  and invariant endpoint simplification, and ordinary variables shared with
  role type graphs. Thus this does **not** settle X13–X17 or the full owner's
  arbitrary nested-interval rules. Arbitrary spine depth here is not a proof
  of arbitrary non-singleton interval normalization.
- Multiple role arguments, branching payloads, captures at distinct payload
  positions, arbitrary mutually recursive finite graphs, record tails,
  general records/rows, associated equations, effect/level/generalization
  state, or mutations of the role graph during a resolution.
- Parsing/inference of the example expressions, file/module loading,
  nominal-body interpretation in Common, source slot/origin/level allocation,
  returned qualified-family adequacy, or `Core.infer` integration.

This is a narrower settled subfragment than the full interval carrier proposed
in the request. All six requested lowered role goals and their actual impl
heads/where clauses lie in it. General interval-state discharge is not claimed.

## Correspondence with the design note's four cases

A missing lower head, an unresolved root, or a surviving unresolved required
inspection gives pending. A regular root rejects before scanning. At a ready
root, the actual family pass eliminates ordinary inconsistency; surviving
regular inspection produces rejection before counting; zero survivors reject;
two or more successful identities are ambiguous; one successful identity
selects its actual key and every substituted where child. Associated equations
are the empty list in this fragment. An outer selected dictionary exists only
if every child completes. The inherited cross-child failure summary is still
the outer protocol's stated policy, not a newly inferred diagnostic rule.

The refinement makes no new meaning for the four outcomes. Restricting the
input domain is explicit. No question note was needed.

## Lifecycle and Common graph bridges

For every original state, every original assignment, every list of captured
names, and **every actual Common payload**, `generated_state_exact` says the
fresh-slot extension satisfies the retained original plus generated capture
atoms iff the original assignment satisfies the original atoms. Original rows
and slots are unchanged literally. `merged_binding_exact` uses the actual
`CandidateConstraints.arguments (slots names) name`, not an unrelated example
list, and characterizes its merged meaning for every occurring name.

For every request, declaration, payload, and child in the complete generated
where list, `child_state_unchanged` proves equality of child and parent ordinary
states. `where_state_recollection` combines that equality with the universal
model-preservation result. Consequently recollection is a no-op within this
fragment: there are no associated updates, no shared mutable role/ordinary
slots, and successful captures add only valid self/cross constraints. This
is **not** an implementation or proof of general child-to-sibling/parent state
threading. That bridge remains open for the full carrier.

`CommonRoleSettledGraphBridge` connects self-loop and boxed-loop graphs to the
existing unary/record Common bridges at **every observation depth** and proves
the boxed Common unfolding equations. List shells retain their nominal name
and original payload edge. Named atoms never open a body. The repeated-tag
lowering maps the literal X6 source head to the head used by its concrete
registry. The numerical tag encoding is explicit, so importing an older
bridge is not being mistaken for a proof about the new graph representation.

## X status and executable evidence

The hard edit rule forbids changing existing `SpecExamples.lean`, despite the
request also asking for a table update there. The replacement table is
`lean/SpecExamplesSettled.lean`, imported by `Yulang.lean` and registered as a
library. The historical table is unchanged; this additive table supersedes
its six affected rows.

| ID | Current status | New outer-entry theorem |
| --- | --- | --- |
| X1–X3 | PROVED, existing | unchanged |
| X4 | NOT-EXPRESSIBLE-YET | unchanged |
| X5 | PROVED, existing | unchanged |
| X6 | PROVED, settled fragment | `x6_single_selected`, `x6_ambiguous` |
| X7 | NOT-EXPRESSIBLE-YET | unchanged |
| X8 | PROVED, settled fragment | `x8_len_selected` |
| X9 | PROVED, settled fragment | `x9_where_tree`, `x9_show_rejected` |
| X10 | PROVED, settled fragment | `x10_inspection_rejected` |
| X11 | PROVED, settled fragment | `x11_rejection_before_ambiguity` |
| X12 | PROVED, settled fragment | `x12_named_selected` |
| X13–X17 | NOT-EXPRESSIBLE-YET | unchanged |
| X18–X20 | PROVED, existing | unchanged |
| X21 | NOT-EXPRESSIBLE-YET | unchanged |
| X22 | MISMATCH, existing | unchanged |
| X23–X24 | NOT-EXPRESSIBLE-YET | unchanged |

Names in the last column have prefix `Yulang.CommonRoleSettledExamples`.
Every concrete example theorem has **no hypotheses**. X6 selects key 0 alone
and is ambiguous with the concrete key-1 candidate. X8 constructs key 2's leaf
dictionary. X9 constructs the key-3 tree with an actual rejected child. X10
and X11 reject. X12 constructs the named tree's key-7 leaf dictionary.
`all_six_independent` derives all six independent `Classify` judgments by the
same unconditional `resolve_exact` entry.

Direct `#eval` executions, using `lake env lean --trust=0` in a temporary file
subsequently removed, returned:

```text
X6 alone: selected (node 0 [])
X6 both: ambiguous
X8: selected (node 2 [])
X9, X10, X11: rejected
X12: selected (node 7 [])
X9 tree: selected 3 [rejected]
duplicate where list: selected (node 3 [node 8 [], node 8 []])
folded and unrolled K2: [rejected, rejected]
```

Regressions also prove upper-only pending, actual ordinary-solver conflict
rejection, elimination of incompatible candidates before K2, preservation of
all repeated self/cross atoms, and retention of duplicate where children.

## Counterexample, repair and review

Independent read-only review found a real defect in the initial rigid
prepass: it stopped at an explicit regular leaf but could descend through a
finite unrolling of the same regular type. With safe `Check {box: 'a}` and
inspecting `Check {box: {next: int}}`, folded and unrolled presentations could
then differ. The repaired prepass stops at **every bisimulation-recognized
regular wrap**, and independent `Rigid.wrapRegular` states that rule.
`folded_unrolled_k2` proves the repaired outer entry rejects both presentations.
The general exactness and accessibility proofs were rebuilt on the repair;
the counterexample was not treated as an ending.

The final independent reviewer found no further material gap within the
stated domain, and explicitly reviewed independent Local, identity checking,
selected-child provenance, accessibility and no-op recollection. The reviewer
performed source inspection, not an independent kernel/audit run. The primary
performed those runs. The registered `prover` role/configuration was absent
in this clone; no prover-role agent ran. The primary constructed this bounded
derivation and a separate available agent reviewed it, as the skill fallback
allows. No resident workers or self-directed sprint were used.

## Remaining full B4 E1 bridges and unverified work

The six tests and settled-fragment exactness are proved; full B4 E1 is not.
Full source frontier generation still needs ordinary graph/slot provenance,
nontrivial lower/upper propagation, inherited invariant nesting, repeated
captures at distinct positions, record-tail scheduling, and associated
constraint substitution. Accessibility must be extended from this closed
unary measure to that richer stateful interval domain. General
`where_state_recollection` must thread updates or prove actual saturation.
Source/qualified-family adequacy, kinds, levels, visibility generation and
nominal declaration interpretation remain outside this proof. Parser/Rust
checks were not run because no parser/Rust implementation changed.

New question notes: **none**. Existing specifications and theorem statements
were neither edited nor weakened.

## Final verification

The final combined gate, after the last Lean theorem and audit addition,
exited **0**:

```sh
cd lean && lake build --wfail && lake env lean --trust=0 Audit.lean
```

Logs are in `lean/.lake/settled-build.log`, `settled-audit.log`, and
`settled-eval.log`. The audit imports all new modules and audits every Yulang
declaration, including private helpers, against only `propext`,
`Classical.choice`, and `Quot.sound`. Every public theorem added here is also
registered by name. No `sorry`, new axiom, or `native_decide` occurs in the new
Lean source. `git diff --check` passed. Only documentation was written after
the final gate.

Build tail:

```text
✔ [1102/1108] Built Yulang.CommonRoleSettledConstraints (963ms)
✔ [1103/1108] Built Yulang.CommonRoleSettledFrontier (954ms)
✔ [1104/1108] Built Yulang.CommonRoleSettledResolver (799ms)
✔ [1105/1108] Built Yulang.CommonRoleSettledExamples (1.5s)
✔ [1106/1108] Built SpecExamplesSettled (692ms)
✔ [1107/1108] Built Yulang (775ms)
Build completed successfully (1108 jobs).
```

Audit allowlist and tail:

```text
Axiom allowlist passed for 81393 declarations from Yulang modules
Axiom allowlist passed for 41 declarations from SpecExamples modules
'Yulang.CommonRoleSettledSyntax.checked_names' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSettledSyntax.every_where_bound' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSettledSyntax.checked_child_decreases' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSettledSyntax.binding_lookup' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSettledSyntax.substitute_all_names' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSettledSyntax.every_where_substituted' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSettledConstraints.merged_binding_exact' depends on axioms: [propext, Quot.sound]
```

## Complete public theorem inventory

Every entry below is registered in Audit.lean. Each statement universally quantifies every displayed argument and every implicit free parameter of its Lean type (in particular the natural slot count `n`). The embedded request, registry and ordinary-state admission conditions are exactly those listed above; no other caller obligations are suppressed. The full Lean type records every proof premise. Private frontier calculation lemmas are covered by the module-wide audit and are not separate public claims.

### `Yulang.CommonRoleSettledConstraints.bounds_slots`

For every generated capture-slot table, name and pair belonging to that name’s actual occurrence list, the pair is the reserved fresh slot paired with itself.

```lean
theorem bounds_slots (names : List Nat) (name : Nat) (pair : Fin (n + 1) × Fin (n + 1))
    (h : pair ∈ CommonRoleCandidateConstraints.bounds (slots names) name) : pair = (0, 0)
```

### `Yulang.CommonRoleSettledConstraints.captures_compatible`

For every list of captured names and every assignment to all fresh/original slots, all generated pairwise occurrence comparisons are compatible; no hypothesis.

```lean
theorem captures_compatible (names : List Nat) (assignment : Fin (n + 1) → Comp Common.model) :
    CommonRoleCandidateConstraints.Compatible (slots names) assignment
```

### `Yulang.CommonRoleSettledConstraints.generated_state_exact`

For every admitted ordinary state, capture-name list, original assignment and actual payload computation, the fresh-slot extension satisfies retained original atoms plus generated checks exactly when the original assignment satisfies the original atoms.

```lean
theorem generated_state_exact (s : State n) (names : List Nat)
    (assignment : Fin n → Comp Common.model) (payload : Comp Common.model) :
    All Common.model (Fin.cases payload assignment)
      (s.atoms.map (PresenceNormalForm.Atom.rename Fin.succ) ++ CommonRoleCandidateConstraints.generate (slots names)) ↔
      All Common.model assignment s.atoms
```

### `Yulang.CommonRoleSettledConstraints.rigid_sound`

For every pattern/type pair, a true executable rigid-compatibility result implies the independent Rigid judgment.

```lean
theorem rigid_sound (p : Pattern) (t : Ty) (h : rigid p t = true) : Rigid p t
```

### `Yulang.CommonRoleSettledConstraints.rigid_complete`

For every independent Rigid derivation, executable rigid compatibility is true.

```lean
theorem rigid_complete (h : Rigid p t) : rigid p t = true
```

### `Yulang.CommonRoleSettledConstraints.rigid_exact`

For every pattern and type, executable rigid compatibility is true exactly when the independent Rigid judgment holds.

```lean
theorem rigid_exact (p : Pattern) (t : Ty) : rigid p t = true ↔ Rigid p t
```

### `Yulang.CommonRoleSettledConstraints.clash_impossible`

For every assignment, the ordinary int-subtype-str clash atom has no model.

```lean
theorem clash_impossible (assignment : Fin (n + 1) → Comp Common.model) :
    ¬ All Common.model assignment clash
```

### `Yulang.CommonRoleSettledConstraints.clash_grammar`

For every original slot count, the clash atom satisfies all three required existing family-solver grammar properties.

```lean
theorem clash_grammar : PresenceGeneratedChildGrammar.GoodAtoms (clash (n
```

### `Yulang.CommonRoleSettledConstraints.original_grammar`

For every admitted ordinary state, pattern and input type, the shifted original atoms with any generated rigid clash satisfy all three solver grammar properties.

```lean
theorem original_grammar (s : State n) (p : Pattern) (t : Ty) :
    PresenceGeneratedChildGrammar.GoodAtoms (original s p t) ∧
    PresenceGeneratedWidth.WidthAtoms (original s p t) ∧
    PresenceSourceConstraintSupport.GoodAtoms (original s p t)
```

### `Yulang.CommonRoleSettledConstraints.propagate_exact`

For every admitted ordinary state, head pattern and type, the actual candidate family solver has a surviving family exactly when the original state has a model and independent rigid compatibility holds.

```lean
theorem propagate_exact (s : State n) (p : Pattern) (t : Ty) :
    propagate s p t = true ↔ s.Models ∧ Rigid p t
```

### `Yulang.CommonRoleSettledConstraints.merged_captures_exact`

For every positive occurrence count and every Common payload and comparison type, the coalesced repeated singleton interval has exactly the same Fits predicate as the original singleton interval.

```lean
theorem merged_captures_exact (count : Nat) (positive : 0 < count)
    (payload actual : Common.Ty) :
    CommonRoleIntervals.Fits
      (CommonRoleIntervals.coalesce (List.replicate count (payload, payload))) actual ↔
      CommonRoleIntervals.Fits (payload, payload) actual
```

### `Yulang.CommonRoleSettledConstraints.merged_binding_exact`

For every name occurring in the actual captured-name list, every original assignment and every Common payload/comparison type, the actual generated occurrence list coalesces to exactly the original singleton Fits predicate.

```lean
theorem merged_binding_exact (names : List Nat) (name : Nat) (member : name ∈ names)
    (assignment : Fin n → Comp Common.model) (payload actual : Common.Ty) :
    CommonRoleIntervals.Fits
      (CommonRoleIntervalGeneration.meaning (Fin.cases (Comp.pure Common.model payload) assignment)
        (CommonRoleCandidateConstraints.arguments (slots names) name)) actual ↔
      CommonRoleIntervals.Fits (payload, payload) actual
```

### `Yulang.CommonRoleSettledExamples.propagate_empty`

For every slot count, head pattern and type, the actual family pass on empty ordinary state returns exactly the rigid-compatibility flag.

```lean
theorem propagate_empty (p : Pattern) (t : Ty) :
    propagate (State.empty : State n) p t = rigid p t
```

### `Yulang.CommonRoleSettledExamples.tick_finite`

The concrete tick-int goal is not regular; no hypotheses.

```lean
theorem tick_finite : tickInt.regular = false
```

### `Yulang.CommonRoleSettledExamples.list_finite`

The concrete nominal-list root containing the regular payload is not regular; no hypotheses.

```lean
theorem list_finite : listLoop.regular = false
```

### `Yulang.CommonRoleSettledExamples.box_finite`

The concrete boxed-loop root is not regular; no hypotheses.

```lean
theorem box_finite : boxedLoop.regular = false
```

### `Yulang.CommonRoleSettledExamples.loop_cyclic`

The concrete anonymous recursive payload is regular; no hypotheses.

```lean
theorem loop_cyclic : loop.regular = true
```

### `Yulang.CommonRoleSettledExamples.x6_merged_capture`

For the actual X6 merged head and tick-int goal, inspection captures the entire int payload and the binding table maps both original names to the int/int pair; no hypotheses.

```lean
theorem x6_merged_capture :
    inspect mergedTick.head tickInt = .hit int ∧
      bindings mergedTick.head int = [(0, (int, int)), (1, (int, int))]
```

### `Yulang.CommonRoleSettledExamples.x6_single_selected`

The single outer entry selects key 0 with a completed leaf dictionary for X6’s merged head alone; no hypotheses.

```lean
theorem x6_single_selected : classify x6Single (request 0 tickInt) = .selected (.node 0 [])
```

### `Yulang.CommonRoleSettledExamples.x6_ambiguous`

The single outer entry reports ambiguity for X6 with both the merged and concrete tick-int declarations visible; no hypotheses.

```lean
theorem x6_ambiguous : classify x6Registry (request 0 tickInt) = .ambiguous
```

### `Yulang.CommonRoleSettledExamples.x8_len_selected`

The single outer entry builds Len’s key-2 leaf dictionary for the nominal list of the regular payload; no hypotheses.

```lean
theorem x8_len_selected : classify x8Registry (request 1 listLoop) = .selected (.node 2 [])
```

### `Yulang.CommonRoleSettledExamples.x9_where_tree`

The single outer entry returns key 3 with exactly one rejected child for Show of the list of the regular payload; no hypotheses.

```lean
theorem x9_where_tree : resolve x9Registry (request 2 listLoop) = .selected 3 [.rejected]
```

### `Yulang.CommonRoleSettledExamples.x9_show_rejected`

The single outer entry classifies that actual X9 child tree as rejected; no hypotheses.

```lean
theorem x9_show_rejected : classify x9Registry (request 2 listLoop) = .rejected
```

### `Yulang.CommonRoleSettledExamples.x10_inspection_rejected`

The single outer entry rejects the actual nested record head attempting to inspect the recursive payload in X10; no hypotheses.

```lean
theorem x10_inspection_rejected : classify x10Registry (request 3 boxedLoop) = .rejected
```

### `Yulang.CommonRoleSettledExamples.x11_rejection_before_ambiguity`

The single outer entry rejects X11 with both the opaque and inspecting record heads visible; no hypotheses.

```lean
theorem x11_rejection_before_ambiguity : classify x11Registry (request 3 boxedLoop) = .rejected
```

### `Yulang.CommonRoleSettledExamples.x12_named_selected`

The single outer entry builds the key-7 leaf dictionary for the named recursive tree identity; no hypotheses.

```lean
theorem x12_named_selected : classify x12Registry (request 2 tree) = .selected (.node 7 [])
```

### `Yulang.CommonRoleSettledExamples.all_six_independent`

All six concrete outputs have independent outer Classify derivations through resolve_exact; no hypotheses.

```lean
theorem all_six_independent :
    Classify (Local x6Registry.declarations) (request 0 tickInt) .ambiguous ∧
    Classify (Local x8Registry.declarations) (request 1 listLoop) (.selected (.node 2 [])) ∧
    Classify (Local x9Registry.declarations) (request 2 listLoop) .rejected ∧
    Classify (Local x10Registry.declarations) (request 3 boxedLoop) .rejected ∧
    Classify (Local x11Registry.declarations) (request 3 boxedLoop) .rejected ∧
    Classify (Local x12Registry.declarations) (request 2 tree) (.selected (.node 7 []))
```

### `Yulang.CommonRoleSettledExamples.x6_source_lowered`

The literal two repeated tick-tag/plain-variable branches lower to exactly the head used by the X6 registry; no hypotheses.

```lean
theorem x6_source_lowered :
    CommonRoleSettledGraphBridge.lowerRepeatedTag [(0, 0), (0, 1)] = some mergedTick.head
```

### `Yulang.CommonRoleSettledExamples.upper_only_pending`

The single outer entry defers the concrete upper-only named-tree request despite a visible matching declaration; no hypotheses.

```lean
theorem upper_only_pending :
    classify x12Registry (Request.waiting 2 tree (State.empty : State 0)) = .pending
```

### `Yulang.CommonRoleSettledExamples.all_where_children_retained`

The single outer entry preserves both identical where clauses and constructs the key-3 dictionary with two key-8 leaf dictionaries; no hypotheses.

```lean
theorem all_where_children_retained : classify duplicateRegistry (request 2 listInt) =
    .selected (.node 3 [.node 8 [], .node 8 []])
```

### `Yulang.CommonRoleSettledExamples.incompatible_eliminated_before_k2`

The single outer entry selects the safe key-5 candidate after ordinary propagation eliminates the incompatible box-int candidate against box-loop; no hypotheses.

```lean
theorem incompatible_eliminated_before_k2 :
    classify incompatibleRegistry (request 3 boxedLoop) = .selected (.node 5 [])
```

### `Yulang.CommonRoleSettledExamples.folded_unrolled_k2`

The repaired single outer entry rejects both folded and finitely unrolled presentations with the same safe/inspecting registry; no hypotheses.

```lean
theorem folded_unrolled_k2 :
    classify unrollingRegistry (request 3 boxedLoop) = .rejected ∧
    classify unrollingRegistry (request 3 boxedUnrolling) = .rejected
```

### `Yulang.CommonRoleSettledExamples.ordinary_conflict_rejected`

The single outer entry rejects Len of the concrete list-loop when the retained original ordinary state contains int-subtype-str; no hypotheses.

```lean
theorem ordinary_conflict_rejected :
    classify x8Registry (Request.known 1 listLoop conflict) = .rejected
```

### `Yulang.CommonRoleSettledExamples.repeated_self_and_cross_generated`

Two occurrences of the same captured name generate all four self/cross ordinary atoms, including duplicates; no hypotheses.

```lean
theorem repeated_self_and_cross_generated :
    CommonRoleCandidateConstraints.generate (slots (n
```

### `Yulang.CommonRoleSettledFrontier.encode_exact`

For every declaration, input type and optional trial output, encoding the executable observation equals the proposed output exactly when an independent Inspect observation has that encoding.

```lean
theorem encode_exact (d : Declaration) (t : Ty) (out : Option Trial) :
    encode d (inspect d.head t) = out ↔
      ∃ observation, Inspect d.head t observation ∧ encode d observation = out
```

### `Yulang.CommonRoleSettledFrontier.trial_exact`

For every ordinary state, requested role, input type, declaration and optional trial output, trial execution equals that output exactly when independent TrialRule holds.

```lean
theorem trial_exact (s : State n) (role : Nat) (t : Ty) (d : Declaration) (out : Option Trial) :
    trial s role t d = out ↔ TrialRule s role t d out
```

### `Yulang.CommonRoleSettledFrontier.scan_sound`

For every state, role, type and finite visible list, independent Scan derives the complete executable survivor list.

```lean
theorem scan_sound (s : State n) (role : Nat) (t : Ty) (ds : List Declaration) :
    Scan s role t ds (scan s role t ds)
```

### `Yulang.CommonRoleSettledFrontier.scan_complete`

For every independent Scan derivation, the executable scanner returns exactly the derived ordered list.

```lean
theorem scan_complete (h : Scan s role t ds results) : scan s role t ds = results
```

### `Yulang.CommonRoleSettledFrontier.scan_exact`

For every state, role, type, visible list and proposed survivor list, scanner equality is equivalent to independent Scan.

```lean
theorem scan_exact (s : State n) (role : Nat) (t : Ty) (ds : List Declaration) (results : List Trial) :
    scan s role t ds = results ↔ Scan s role t ds results
```

### `Yulang.CommonRoleSettledFrontier.summarize_sound`

For every request and survivor list, the independent four-case Decision derives the executable summary.

```lean
theorem summarize_sound (q : Request n) (results : List Trial) :
    Decision q results (summarize q results)
```

### `Yulang.CommonRoleSettledFrontier.summarize_complete`

For every independent Decision derivation, executable summarization returns that exact frontier.

```lean
theorem summarize_complete (h : Decision q results result) : summarize q results = result
```

### `Yulang.CommonRoleSettledFrontier.summarize_exact`

For every request, survivor list and proposed frontier, executable summary equality is equivalent to independent Decision.

```lean
theorem summarize_exact (q : Request n) (results : List Trial) (result : Frontier (Request n)) :
    summarize q results = result ↔ Decision q results result
```

### `Yulang.CommonRoleSettledFrontier.frontier_sound`

For every finite visible list and admitted request, independent Local derives the actual executable frontier.

```lean
theorem frontier_sound (visible : List Declaration) (q : Request n) : Local visible q (frontier visible q)
```

### `Yulang.CommonRoleSettledFrontier.frontier_complete`

For every independent Local derivation, the executable frontier returns its exact result.

```lean
theorem frontier_complete (h : Local visible q result) : frontier visible q = result
```

### `Yulang.CommonRoleSettledFrontier.frontier_exact`

For every slot count and finite visible declaration list, every admitted request and every frontier, executable frontier equality is equivalent to independent Local; no correspondence or termination premise.

```lean
theorem frontier_exact (visible : List Declaration) :
    CommonRoleOutermostResolver.FrontierExact (protocol (n
```

### `Yulang.CommonRoleSettledGraphBridge.lower_repeated_same_tag`

For every tag, first plain variable and remaining plain variables, lowering those repeated same-tag branches returns the corresponding whole-payload merged binder.

```lean
theorem lower_repeated_same_tag (tag first : Nat) (rest : List Nat) :
    lowerRepeatedTag ((tag, first) :: rest.map (fun name => (tag, name))) =
      some (.wrap (.variant tag) (.bind first rest))
```

### `Yulang.CommonRoleSettledGraphBridge.variant_graph`

For every variant tag, the settled self-loop graph is the existing unary bridge graph with the explicit encoded tag.

```lean
theorem variant_graph (tag : Nat) :
    (Ty.variantLoop tag).graph = CommonRoleUnaryGraphBridge.graph (variantCycle tag)
```

### `Yulang.CommonRoleSettledGraphBridge.record_graph`

For every record label, the settled self-loop graph is the existing record bridge graph with the explicit encoded label.

```lean
theorem record_graph (label : Nat) :
    (Ty.recordLoop label).graph = CommonRoleRecordGraphBridge.graph (recordCycle label)
```

### `Yulang.CommonRoleSettledGraphBridge.variant_common_observations`

For every variant tag and every observation depth, decoding the settled loop graph observation equals the Common carrier observation at that depth.

```lean
theorem variant_common_observations (tag depth : Nat) :
    CommonRoleUnaryGraphBridge.viewFinite
      (observe (Ty.variantLoop tag).graph (depth + 1) (Ty.variantLoop tag).root) =
    Common.observeTy depth (CommonRoleUnaryGraphBridge.common (variantCycle tag) 0)
```

### `Yulang.CommonRoleSettledGraphBridge.record_common_observations`

For every record label and every observation depth, decoding the settled loop graph observation equals the Common carrier observation at that depth.

```lean
theorem record_common_observations (label depth : Nat) :
    CommonRoleRecordGraphBridge.viewFinite
      (observe (Ty.recordLoop label).graph (depth + 1) (Ty.recordLoop label).root) =
    Common.observeTy depth (CommonRoleRecordGraphBridge.common (recordCycle label) 0)
```

### `Yulang.CommonRoleSettledGraphBridge.boxed_graph`

For every outer and recursive record label, the actual settled boxed-loop graph equals the explicit two-node graph supplied to the existing Common record bridge.

```lean
theorem boxed_graph (boxLabel loopLabel : Nat) :
    (Ty.wrap (.record boxLabel) (.recordLoop loopLabel)).graph =
      CommonRoleRecordGraphBridge.graph (boxedCycle boxLabel loopLabel)
```

### `Yulang.CommonRoleSettledGraphBridge.boxed_common_observations`

For every outer label, recursive label and depth, the settled boxed-loop graph and the bridged Common type have the same finite observation.

```lean
theorem boxed_common_observations (boxLabel loopLabel depth : Nat) :
    CommonRoleRecordGraphBridge.viewFinite
      (observe (Ty.wrap (.record boxLabel) (.recordLoop loopLabel)).graph (depth + 1)
        (Ty.wrap (.record boxLabel) (.recordLoop loopLabel)).root) =
    Common.observeTy depth (CommonRoleRecordGraphBridge.common (boxedCycle boxLabel loopLabel) 0)
```

### `Yulang.CommonRoleSettledGraphBridge.boxed_common_unfolds`

For every outer and recursive record label, the bridged root is Common-equivalent to the outer field containing the recursive node, and that node is equivalent to its own recursive field unfolding.

```lean
theorem boxed_common_unfolds (boxLabel loopLabel : Nat) :
    Common.Equivalent (CommonRoleRecordGraphBridge.common (boxedCycle boxLabel loopLabel) 0)
      (Common.required (2 * boxLabel + 1)
        (CommonRoleRecordGraphBridge.common (boxedCycle boxLabel loopLabel) 1)) ∧
    Common.Equivalent (CommonRoleRecordGraphBridge.common (boxedCycle boxLabel loopLabel) 1)
      (Common.required (2 * loopLabel + 1)
        (CommonRoleRecordGraphBridge.common (boxedCycle boxLabel loopLabel) 1))
```

### `Yulang.CommonRoleSettledGraphBridge.list_payload_graph`

For every nominal name and recursive record label, the actual two-node graph has the nominal root pointing to the structural self-loop payload; no body is opened.

```lean
theorem list_payload_graph (name label : Nat) :
    (Ty.wrap (.nominal name) (.recordLoop label)).graph
      ⟨0, by simp [Ty.nodes]⟩ = .nominal name [⟨1, by simp [Ty.nodes]⟩] ∧
    (Ty.wrap (.nominal name) (.recordLoop label)).graph
      ⟨1, by simp [Ty.nodes]⟩ = .structural (2 * label + 1) [⟨1, by simp [Ty.nodes]⟩]
```

### `Yulang.CommonRoleSettledGraphBridge.named_body_opaque`

For every nominal name, the named atom graph is exactly that nominal node with no explicit arguments and is not anonymous regular.

```lean
theorem named_body_opaque (name : Nat) :
    (Ty.atom (.named name)).graph (Ty.atom (.named name)).root = .nominal name [] ∧
      (Ty.atom (.named name)).regular = false
```

### `Yulang.CommonRoleSettledResolver.trial_hit_origin`

For every actual trial returning a declaration/payload hit, the returned declaration equals the tried declaration and independent Inspect derives that payload.

```lean
theorem trial_hit_origin (s : State n) (role : Nat) (t : Ty) (source d : Declaration) (payload : Ty)
    (h : trial s role t source = some (.hit d payload)) :
    source = d ∧ Inspect d.head t (.hit payload)
```

### `Yulang.CommonRoleSettledResolver.scan_hit_origin`

For every hit in the executable survivor list, its declaration belongs to the actual visible list and its payload has an independent successful inspection derivation.

```lean
theorem scan_hit_origin (s : State n) (role : Nat) (t : Ty) (visible : List Declaration)
    (d : Declaration) (payload : Ty) (h : Trial.hit d payload ∈ scan s role t visible) :
    d ∈ visible ∧ Inspect d.head t (.hit payload)
```

### `Yulang.CommonRoleSettledResolver.mem_hits`

For every survivor list, declaration and payload, membership of the projected successful pair is exactly membership of the corresponding hit trial.

```lean
theorem mem_hits (results : List Trial) (d : Declaration) (payload : Ty) :
    (d, payload) ∈ hits results ↔ Trial.hit d payload ∈ results
```

### `Yulang.CommonRoleSettledResolver.selected_origin`

For every independently selected frontier, there exist its actual lower type, visible declaration and captured payload, with independent successful inspection, the actual declaration key, and exactly the complete instantiated where list.

```lean
theorem selected_origin (visible : List Declaration) (q : Request n) (key : Nat)
    (cs : List (Request n)) (h : Local visible q (.selected key cs)) :
    ∃ t d payload, q.lower = some t ∧ d ∈ visible ∧ Inspect d.head t (.hit payload) ∧
      key = d.key ∧ cs = children q d payload
```

### `Yulang.CommonRoleSettledResolver.child_decreases`

For every admitted registry and every independently generated parent/child edge, child weight is strictly less than parent weight; no child-success premise.

```lean
theorem child_decreases (registry : Registry) (q child : Request n)
    (h : Child (Local registry.declarations) child q) : weight child < weight q
```

### `Yulang.CommonRoleSettledResolver.accessible`

For every admitted registry and every admitted request at every slot count, the independent where-child relation is accessible; no accessibility or rank hypothesis.

```lean
theorem accessible (registry : Registry) (q : Request n) :
    Acc (Child (Local registry.declarations)) q
```

### `Yulang.CommonRoleSettledResolver.resolve_tree_exact`

For every admitted registry, request and proposed tree, the concrete outer entry returns that tree exactly when independent Resolves derives it; no frontier/accessibility hypothesis.

```lean
theorem resolve_tree_exact (registry : Registry) (q : Request n) (tree : Tree) :
    resolve registry q = tree ↔ CommonRoleOutermostResolver.Resolves
      (Local registry.declarations) q tree
```

### `Yulang.CommonRoleSettledResolver.resolve_exact`

For every admitted registry, request and proposed result, classification of the concrete outer entry equals that result exactly when independent Classify derives it; no frontier/accessibility hypothesis.

```lean
theorem resolve_exact (registry : Registry) (q : Request n) (result : Result) :
    classify registry q = result ↔ Classify (Local registry.declarations) q result
```

### `Yulang.CommonRoleSettledResolver.resolve_eq`

For every admitted registry and request, the concrete outer entry unfolds to its computed frontier, recursively evaluating the same entry on every selected child in order.

```lean
theorem resolve_eq (registry : Registry) (q : Request n) :
    resolve registry q = match frontier registry.declarations q with
      | .pending => .pending
      | .rejected => .rejected
      | .ambiguous => .ambiguous
      | .selected key cs => .selected key (cs.map (resolve registry))
```

### `Yulang.CommonRoleSettledResolver.child_state_unchanged`

For every request, declaration and payload, every child in their complete generated list has exactly the parent’s original ordinary state.

```lean
theorem child_state_unchanged (q : Request n) (d : Declaration) (payload : Ty)
    (child : Request n) (member : child ∈ children q d payload) : child.state = q.state
```

### `Yulang.CommonRoleSettledResolver.where_state_recollection`

For every request, declaration, payload and generated child, every original assignment and every actual Common payload computation, the child state is unchanged and fresh generated capture checks preserve exactly the original models.

```lean
theorem where_state_recollection (q : Request n) (d : Declaration) (payload : Ty)
    (child : Request n) (member : child ∈ children q d payload)
    (assignment : Fin n → Core.PresenceGeneration.Comp Common.model)
    (actualPayload : Core.PresenceGeneration.Comp Common.model) :
    child.state = q.state ∧
      (PresenceNormalForm.All Common.model (Fin.cases actualPayload assignment)
        (q.state.atoms.map (PresenceNormalForm.Atom.rename Fin.succ) ++
          CommonRoleCandidateConstraints.generate (slots d.head.names)) ↔
        PresenceNormalForm.All Common.model assignment q.state.atoms)
```

### `Yulang.CommonRoleSettledSyntax.Ty.nodes_pos`

For every fragment type, its finite graph has at least one node; no hypothesis.

```lean
theorem Ty.nodes_pos (t : Ty) : 0 < t.nodes
```

### `Yulang.CommonRoleSettledSyntax.regular_exact`

For every fragment type, the executable regularity flag is true exactly when the independent graph RegularAt judgment holds; no hypothesis.

```lean
theorem regular_exact (t : Ty) : t.regular = true ↔ t.Regular
```

### `Yulang.CommonRoleSettledSyntax.loop_regular`

For every numeric label, both its variant self-loop and its record self-loop are recognized as regular; no hypothesis.

```lean
theorem loop_regular (tag : Nat) : (Ty.variantLoop tag).regular = true ∧
    (Ty.recordLoop tag).regular = true
```

### `Yulang.CommonRoleSettledSyntax.unknown_not_regular`

The unresolved leaf is not a regular root; no hypotheses.

```lean
theorem unknown_not_regular : Ty.unknown.regular = false
```

### `Yulang.CommonRoleSettledSyntax.atom_not_regular`

For every scalar or named atom, its root is not anonymous regular; no hypothesis.

```lean
theorem atom_not_regular (a : Atom) : (Ty.atom a).regular = false
```

### `Yulang.CommonRoleSettledSyntax.form_normal`

For every fragment type, its size-counting Form is already normalized; no hypothesis.

```lean
theorem form_normal (t : Ty) : t.form.normalize = t.form
```

### `Yulang.CommonRoleSettledSyntax.template_form`

For every where template and payload, the form of its actual instantiation equals normalized form substitution; no hypothesis.

```lean
theorem template_form (t : Template) (payload : Ty) :
    (t.instantiate payload).form = (t.form.subst (fun _ => payload.form)).normalize
```

### `Yulang.CommonRoleSettledSyntax.merged_form_subst`

For every first variable, additional variable list and payload, substituting the same payload into all merged variables normalizes to that payload form; no hypothesis.

```lean
theorem merged_form_subst (first : Nat) (more : List Nat) (t : Ty) :
    ((mergedForm first more).subst (fun _ => t.form)).normalize = t.form
```

### `Yulang.CommonRoleSettledSyntax.inspect_sound`

For every head pattern and type, the independent Inspect judgment derives the actual executable observation; no hypothesis.

```lean
theorem inspect_sound (p : Pattern) (t : Ty) : Inspect p t (inspect p t)
```

### `Yulang.CommonRoleSettledSyntax.regular_false`

For every type, absence of independent regularity implies that its executable regularity flag is false.

```lean
theorem regular_false {t : Ty} (h : ¬ t.Regular) : t.regular = false
```

### `Yulang.CommonRoleSettledSyntax.inspect_complete`

For every independent Inspect derivation, the executable inspector returns exactly its observation; the derivation is the only premise.

```lean
theorem inspect_complete (h : Inspect p t result) : inspect p t = result
```

### `Yulang.CommonRoleSettledSyntax.inspect_exact`

For every pattern, type and proposed observation, executable equality is equivalent to the independent Inspect judgment; no hypothesis.

```lean
theorem inspect_exact (p : Pattern) (t : Ty) (result : Observation) :
    inspect p t = result ↔ Inspect p t result
```

### `Yulang.CommonRoleSettledSyntax.hit_form`

For every independent successful capture of a payload from a pattern and type, normalized substitution into the pattern form equals the actual type form.

```lean
theorem hit_form (h : Inspect p t (.hit payload)) :
    (p.form.subst (fun _ => payload.form)).normalize = t.form
```

### `Yulang.CommonRoleSettledSyntax.checked_names`

For every declaration accepted by its checker and every original where member, every variable used by that member occurs in the head.

```lean
theorem checked_names (d : Declaration) (checked : d.check = true)
    (r : Nat × Template) (member : r ∈ d.requirements) :
    ∀ name ∈ r.2.names, name ∈ d.head.names
```

### `Yulang.CommonRoleSettledSyntax.every_where_bound`

For every accepted declaration, original where member, payload, and name used by that member, the actual deduplicated binding table contains the name and both original equal endpoints.

```lean
theorem every_where_bound (d : Declaration) (checked : d.check = true)
    (r : Nat × Template) (member : r ∈ d.requirements) (payload : Ty)
    (name : Nat) (used : name ∈ r.2.names) :
    (name, (payload, payload)) ∈ bindings d.head payload
```

### `Yulang.CommonRoleSettledSyntax.checked_child_decreases`

For every accepted declaration, original where member, input type and payload successfully captured by independent Inspect, the instantiated child has strictly smaller weight than the input.

```lean
theorem checked_child_decreases (d : Declaration) (checked : d.check = true)
    (r : Nat × Template) (member : r ∈ d.requirements)
    (t payload : Ty) (matched : Inspect d.head t (.hit payload)) :
    (r.2.instantiate payload).weight < t.weight
```

### `Yulang.CommonRoleSettledSyntax.binding_lookup`

For every pattern, payload and name, actual lookup returns the equal endpoint pair exactly when the name is in the head; otherwise it returns none.

```lean
theorem binding_lookup (p : Pattern) (payload : Ty) (name : Nat) :
    CommonRoleCanonicalRows.lookup name (bindings p payload) =
      if name ∈ p.names then some (payload, payload) else none
```

### `Yulang.CommonRoleSettledSyntax.substitute_all_names`

For every head pattern, payload and template whose names are all in the head, actual template instantiation has an independent named-lookup Substitute derivation.

```lean
theorem substitute_all_names (p : Pattern) (payload : Ty) (template : Template)
    (bound : ∀ name ∈ template.names, name ∈ p.names) :
    Substitute (bindings p payload) template (template.instantiate payload)
```

### `Yulang.CommonRoleSettledSyntax.every_where_substituted`

For every accepted declaration, every member of its original ordered where list and every payload, actual instantiation has the named-lookup substitution derivation.

```lean
theorem every_where_substituted (d : Declaration) (checked : d.check = true)
    (r : Nat × Template) (member : r ∈ d.requirements) (payload : Ty) :
    Substitute (bindings d.head payload) r.2 (r.2.instantiate payload)
```
