# Independent review: finite structural row saturation

Date: 2026-10-26. Review revision: 1.
Reviewer: `/root/finite_row_solver_review`, fresh generic leaf, not an author
or contributor to the reviewed construction. No children.
Mode: M3 mathematical/specification review under the primary's exact lease.
Primary-reported branch/head: `yulang3`,
`f5b947056f23fb50236463d86738bdea579c1514`; no Git command was used.

## Verdict and frozen scope

**ACCEPT. No blocking or major finding; no mandatory repair.**

The executable procedure really constructs a finite clause closure, proves the
five existing syntactic saturation fields after concrete local checks, and
applies the accepted canonical model construction to the original input
clauses. The finite iteration bound, exact constructor children, original-list
retention, same-table extension converse, and original Store/history premises
agree between the source, checked types, paper and producer receipt.

Acceptance is for this finite structural component. The unchanged original
`SourceProblem.InferenceSoundness` remains **OPEN**. This review does not
establish actual native-success correspondence, full source typing, ordinary
inference completeness, principality, native termination or production cutover.

The primary supplied the final paper/receipt freeze and producer write-cessation
message before this verdict. Independently recomputed hashes match:

| Frozen artifact | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/NativeRowSaturation.lean` | `9f8e2cf43ade40c17a09387d5888833002ee42791eff0d2d608f83d6ca39e974` |
| `notes/theory/2026-10-26-finite-native-row-saturation.md` | `c16cabe5a514ef0a99ecbe983961a148a70f54117e7830d923cb580fb89a7577` |
| `tasks/agent-loop/inbox/20261026-inference-native-row-saturation.md` | `9923888ec4abaaa9073cda9a49e6b43745316cfa735647cb083190df26742a95` |
| Accepted `NativeRowModel.lean` dependency | `30016f40295a803df2ed3d9b46efd256d1427400f55bda1810e22a00f89d7780` |
| Frozen source/configuration manifest | `01ecf6cfe27bbc2a2e8b0d0c49e2123044bec00055826ed28e871141311d6a1e` |
| Final source build, `check05.log` | `1c6b48ea37ddee4821a39158a165710cb3d7730733ebb4ff1204d959e331221b` |
| Complete originating-declaration audit, `check06-all-origin.log` | `04cd41210b825319e63396f7c881d84a5148b060ab9e256892d216a81ddc6264` |
| Complete type/axiom records, `all-origin-records.json` | `24c1bfdfd2e567300b5f41d9839841d8a95548c906d9a3d8ca7f96aaeb1dc763` |
| Origin audit program | `7cad236eae3997d3f64c9cf274b46c8d005303f8f6cab250c74db56af81059de` |

Evidence paths in the last four rows are under
`/workspace/scratch/f98087c7ac1a/inference-native-row-saturation/`; the audit
program is `project/AuditNativeRowSaturationAll.lean`.
All 17 entries in the frozen Lean/configuration manifest match both the current
repository and the producer's isolated project. Every entry in
`evidence-hashes.json` also matches its actual file. The historical
`input-hashes.json` intentionally records the dependency before its accepted
three-LF normalization; the final manifest records the actual checked bytes.
The accepted dependency review explains this exact mechanical delta.

## Authority and original claim

Read the root operating map and pre-sprint map, the proof skill and its
source/execution references, design-authority and top-level inference
principles, applicable sprint/review rules, the native-correspondence progress
record, accepted model evidence, and the actual defining Lean sources. The
original claim in `YulangClosure/Contracts.lean` is still:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

The new module neither changes these judgments nor constructs their concrete
whole-source instance. The paper and receipt preserve the supported source
domain, original scope and shared witness. The relevant research manuscript's
record-boundary rules and nontransitivity example were also inspected; they
are not replaced by the structural relation used here.

## Mathematical review

### Finite bound and retention

`pairUniverse` is the union of the two kind-indexed Cartesian squares on
row-plus-head addresses. `mem_pairUniverse` exactly identifies membership with
both endpoint bounds. The finite enumeration includes every possible bounded
generated comparison; the value and effect universes remain distinct.

`remaining` is a filter of the current pending list. If it differs from that
list, equal lengths would force the filter to be the identity, contradicting
the changed-round hypothesis. Thus `remaining_strict` proves a strict length
decrease without assuming semantic consistency, distinctness or saturation.

`close_correct` maintains three substantive invariants: all retained pairs are
bounded, all pending pairs are bounded, and every bounded pair occurs in one
of the two lists. The maintained inequality is `pending.length ≤ fuel`.
After a changed round, strict decrease makes the recursive fuel sufficient.
At a stable round no pending pair is demanded. At fuel zero, pending must be
empty and coverage gives closure directly. In particular, consuming the last
unit of fuel cannot hide a remaining bounded demand. Out-of-universe demands
are handled by the later explicit child-bounds check.

The absent-pair initialization and separation lemmas correctly establish that
new additions were absent from the previous retained list. Separation is not
an undeclared premise of `close_correct`; closure only needs the invariants
stated in its type. Input duplicates are harmless and remain in order.
`close_prefix`/`clauses_prefix` prove literal append-prefix retention, which is
stronger than the membership retention used by the model theorem.
`withClauses` changes only the clause field, so row counts and head tables are
definitionally stable throughout.

The paper's bound of at most the initial pending length of changed rounds is
justified. Its finite universe has size
`n_value² + n_effect²` by the displayed range/map/flatMap enumeration. No
native hot-path complexity or production implementation claim is attached to
this exhaustive reference construction.

### Actual closure and malformed cases

For a retained row-to-target pair, the procedure enumerates exactly the
retained structural lower heads of the source row and emits their comparisons
with that target. This supports both `rowRow` and `rowHead`. A head-to-row
pair is already one such lower bound and requires no additional child rule.
A head-to-head pair uses actual finite-table lookups and the existing
`Regular.expandNodes` result.

Natural-number subtraction in `headExpansion` cannot reinterpret a row as a
head on the operational path: `consequences` handles the row cases first, and
`compatible` only consults expansion when both endpoints are heads. Initial
bounds and output boundedness rule out invalid head addresses on success.
The head-index reconstruction used in the converse is justified by the same
row/head split and the saturated extension's bounds.

The finite formation check covers every head, even one unused by any clause.
It checks unique record labels/variant tags and every kind-correct child
reference. The final compatibility check distinguishes an unsuccessful
expansion from a successful empty child list. Although `getD []` emits no
children for an incompatible pair during iteration, that parent is retained
and rejected by `checkCompatible`; it cannot become a false successful leaf.
The final generated-child bounds check prevents accepting a demand silently
excluded from the finite universe. Diagnostic head references use head-table
indices, as the paper and receipt explicitly state.

`completed_saturated` directly fills all five original fields. Boundedness
comes from the iteration theorem, formation from its executable equivalence,
row closure from `row_consequence`, and head closure from a successful exact
expansion plus `head_consequence`. `NodeRel` here is the finite constructor
relation with clause membership as its parameter. Inspection of its actual
definition and equivalence with `HoldsExpansion` confirms that it is not a
hidden `RegularSub`, chosen model, successful decision or semantic-consistency
assumption.

### Constructor coverage and shared interpretation

The four Function obligations are exactly
`upper.argument ≤ lower.argument`,
`upper.argumentEffect ≤ lower.argumentEffect`,
`lower.resultEffect ≤ upper.resultEffect`, and
`lower.result ≤ upper.result`, with kinds value/effect/effect/value.
The native Function dispatch in `crates/yu-solver/src/lib.rs` constructs the
same signed children. This local agreement is not a proof of all native
execution paths.

Records use the existing exact ordered label/optionality comparison. Tuples
require equal ordered arity. Variants retain exact tag order and complete
payload arities/order. Bottom, top and atoms follow the unchanged expansion
definition. The discriminating computations in the new module actually test
optional-bit, tuple-arity and variant-payload mismatch, rather than discarding
those distinctions.

The canonical graph uses the one `out.names` map for every original endpoint
and structural child, including negative Function ports. It retains the
accepted distinction between lower joins and upper meets. Alias-only cycles
have no rigid lower heads and are interpreted as structural bottom; no
unguarded alias node is introduced. The recursive example starts with only
four original clauses, computes missing closure clauses by reflexivity, and
decodes the original four-element Store by reflexivity. It does not assume
the earlier `recursive_saturated` proof or inherit its choice dependency.

### Leastness and converse

`demands_in_extension` uses an extension with exactly the same row/head tables.
Its current-list inclusion transports lower-head membership; the extension's
row rules supply row-generated demands, and its exact head expansion supplies
every structural child. Induction then places all computed clauses in every
such saturated extension containing the input.

The proof of `solve_complete` derives every local Boolean check from that
extension: original bounds, unchanged-table formation, compatibility of all
computed clauses and bounds of all final demands. `solve_exists_iff` therefore
has precisely the advertised syntactic meaning. The extension premise occurs
only in leastness/converse theorems. `solve`, `completed_saturated`,
`solve_success` and `solve_original_model` do not assume its existence.
Neither the theorem nor the accompanying text equates membership leastness
with list equality, a semantic least model, or completeness for arbitrary
lattice valuations or native adaptation.

## Checked types, premises and applications

All names below have prefix
`YulangClosure.SimpleSub.NativeRowSaturation`. Parameters not displayed in the
table remain universally quantified exactly as in the source and full audit.
Every theorem in this table uses exactly `propext, Quot.sound`.

| Declaration | Substantive hypotheses and exact conclusion |
| --- | --- |
| `remaining_strict` | `remaining s prior pending ≠ pending` implies strict decrease of pending length. No boundedness or model premise. |
| `close_correct` | Sufficient fuel, bounded prior, bounded pending and coverage of every bounded pair imply bounded returned clauses and `Closed s` of that returned list. |
| `clauses_correct` | Bounded original clauses imply bounded computed clauses and `Closed s (clauses s)`. |
| `clauses_prefix` | For every `s`, some `extra` satisfies `(completed s).clauses = s.clauses ++ extra`; no success premise. |
| `completed_saturated` | The four actual Boolean equalities for original bounds, head formation, computed-clause compatibility and final generated bounds imply `Saturated (completed s)`. |
| `solve_success` | `solve s = .ok out` implies `out = completed s`, exact row/head table equality, original-clause membership retention and `Saturated out`. |
| `solve_original_model` | The same sole success hypothesis implies `out.graph.Valid`, `out.graph.Guarded`, `RegularSub` for every original clause renamed by `out.names`, and `decideDemands out.graph` equal to true for the original mapped list. |
| `solve_original_store` | Success and exactly `decodeStore out.graph out.names store = some (s.clauses.map (renamePair out.names))` imply `StoreSatisfied out.graph out.names store`. |
| `solve_original_history` | Success and an actual `ConstraintHistory out.graph ref birth first` ending at the original mapped clauses/events imply validity, guardedness and `Holds out.graph first.obligations`. |
| `demands_in_extension` | `Saturated (withClauses s target)` and inclusion of `prior` in `target` imply inclusion of every `demands s prior` element in `target`. |
| `clauses_least` | The same-table saturated extension plus original-clause inclusion implies computed-clause membership inclusion. |
| `solve_complete` | The same saturated extension and original-clause inclusion imply `solve s = .ok (completed s)`. |
| `solve_exists_iff` | Successful output exists iff a finite target clause list contains every original clause and is saturated under the unchanged tables. No extra hypothesis. |

The actual guard Boolean is supplied by the accepted
`NativeRowModel.canonical_guard_checked out`; `solve_original_model` uses it
in the exact decision equivalence and derives guardedness as a conclusion.
It does not presume a successful final decision. The Store decoder is
structural readback, not a semantic satisfaction test. The graph-indexed
history is an explicit input, not something established by this wrapper.
Consequently no source/history reconstruction premise disappears behind the
application theorems.

## Complete axiom and execution evidence

Inspected the origin-audit implementation. It selects declarations by the
actual originating module index, includes private/generated constants,
rejects project axioms/duplicates and unapproved dependencies, requires all
40 authored roots, and prints each full type and axiom closure. Independently
parsed the raw log rather than relying only on `audit-summary.json`.

The raw records contain 142 distinct matching begin/end blocks: 81 theorem
constants, 55 definitions, four constructors, one inductive type and one
recursor. Three constants are private generated `close` match lemmas.
All 40 authored source theorem names are present as theorem constants.
The stored `all-origin-records.json` type/axiom text matches all 142 raw log
blocks exactly. Complete axiom distributions are:

| Axiom set | Theorem constants | All originating declarations |
| --- | ---: | ---: |
| Empty | 14 | 54 |
| `propext` | 26 | 47 |
| `propext, Quot.sound` | 41 | 41 |

No new declaration depends on `Classical.choice`, a project axiom, `sorryAx`,
unchecked native evaluation or another unapproved axiom. The direct source
scan of the new module and accepted model found no hole or bypass; the
producer's retained cone scan agrees. These are standard-axiom-dependent
proofs where listed, not a claim that every theorem is axiom-free.

The pin is Lean 4.35.0, the manifest has no external packages, and the project
sets `-j1 -M1024`. The saved version receipt identifies the pinned native Lake
and Lean. `check05.log` records successful construction of the exact frozen
source, 15 jobs, exit 0, 5.075 seconds. The full origin audit records exit 0,
1.664 seconds. Earlier failures and their repairs remain in separate logs;
the producer used six focused calls totaling 74.215 seconds, with its runner
setting one thread and a 120-second process-group timeout.

This reviewer used **zero of the two optional focused Lean calls**. Direct
proof reading, exact types/axioms, and hash comparison left no concrete
checker discrepancy requiring a rerun. This receipt reviews the producer's
checked evidence and does not claim independent re-execution of its six
calls. No broad build, native test, Cargo invocation or Git command was used.
The complete integration build/audit remains primary-owned.

## Original/native exclusions and next evidence

Native record dispatch looks up target fields by name and permits absent
optional targets; this is not the formal exact ordered `recordPairs` rule.
Native variant dispatch also matches keyed alternatives rather than the
formal exact zipped lists. The finite structural grammar and same-table
characterization are explicit, and the packet makes no native-success
implication that would wrongly identify these behaviors.

The original record-boundary manuscript preserves direct comparison,
intermediate visible views and non-resurrection of hidden fields. Its
nontransitive `{foo?:string} → {} → {foo?:int}` example cannot be replaced by
one transitive endpoint inequality. This component does not make that
replacement. Optional/open/width adaptation, method/Call plans, distinct
adaptation outputs, contextual effects, occurrence/scope identities, full
world/continuation contracts and every original supported source constructor
remain obligations of the original theorem.

The first missing application evidence remains at the native/source owners:
faithful all-eight-lane original input extraction and transport; a proof that
actual successful native execution supplies successful or soundly related
reference closure; actual output/reference/history alignment with the one
computed interpretation; and original publication/source-scoped witness
reconstruction. Neither the inventory fixture nor the restricted replay
component supplies those universally. These are retained parent obligations,
not repairs required for acceptance of this component.

## Write boundary and cessation

The sole reviewer-created repository file is this receipt. No producer source,
paper or handoff, imported proof, Rust file, shared status, root import,
configuration, question or Git state was changed. No scratch project/cache was
created, and no child or checker subprocess was launched.

**All reviewer writes stopped after this receipt.** Primary owns adjudication,
integration, subsequent native/source assignments, commits and pushes.
