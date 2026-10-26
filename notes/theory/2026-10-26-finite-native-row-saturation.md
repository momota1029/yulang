# Executable finite saturation of structural row constraints

Date: 2026-10-26.
Status: constructed and kernel-checked component; frozen for independent review.
Lean source: `notes/theory/lean/YulangClosure/NativeRowSaturation.lean`.
SHA256: `9f8e2cf43ade40c17a09387d5888833002ee42791eff0d2d608f83d6ca39e974`.

**The original whole-Yulang `SourceProblem.InferenceSoundness` remains OPEN.**
This component replaces the previously supplied `NativeRowModel.Saturated`
premise with an executable finite clause construction and local checks. It
derives the canonical graph, one shared reference interpretation, and actual
finite decision for the original input clauses. No native `Ok` is asserted to
imply success of this reference construction, and no production checking pass
is added.

## 1. Original obligation and exact advance

The unchanged parent in `YulangClosure/Contracts.lean` is

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

It retains every original supported source constructor, original scope and
shared witness, optional records, method selection, complete Call, contextual
effects, publication, fresh uses, extrusion and intrusion. The reference
solver below does not redefine any of those judgments or narrow that parent.

The accepted [canonical row model](2026-10-26-native-row-model-construction.md)
constructs a guarded regular graph from finite row/head tables and a
syntactically saturated clause list. Its five saturation fields were still
inputs. The new component constructs that list from arbitrary finite input
syntax, checks malformed syntax and incompatible structural heads, and proves
all five fields for successful output. Its additional converse characterizes
success exactly by the existence of a finite syntactically saturated extension
with the same row/head tables.

This is a solver for that precise finite syntactic closure problem. The
converse does not assert completeness for every semantic valuation, full
native record adaptation, an enlarged disjunctive type grammar, or the original
source language.

## 2. Finite syntax and constructor rules

The input is the existing `NativeRowModel.System`:

```lean
rows : Kind → Nat
heads : (k : Kind) → List (Regular.Node k)
clauses : List Regular.Comparison
```

For kind `k`, indices below `rows k` are rows, and index `rows k + h` is head
`h`. Both kinds have independent finite tables. Every structural child uses
this same source numbering, including negative Function ports.

For a retained list `C`, `consequences s C p` implements three cases:

| Retained clause | Generated obligations |
| --- | --- |
| Row `x → y`, where `y` can be a row or a head | For every head `h` with `head(h) → x` retained in `C`, emit `head(h) → y`. |
| Head → row | None; the retained clause itself is a structural lower bound. |
| Head → head | Look up both heads and emit the exact list from `Regular.expandNodes`. |

`demands s C` concatenates these finite lists over every retained clause.
Constructor decomposition is the existing executable definition, rather than
a new relation approximating it. Its Function case emits exactly

```lean
[⟨.value, upper.argument, lower.argument⟩,
 ⟨.effect, upper.argumentEffect, lower.argumentEffect⟩,
 ⟨.effect, lower.resultEffect, upper.resultEffect⟩,
 ⟨.value, lower.result, upper.result⟩]
```

Thus the signs are `(-,-,+,+)`, with the corresponding value/effect kinds.
Records preserve the full field order, label and optional bit. Tuples preserve
the whole ordered element list and arity. Variants preserve tag order and each
complete ordered payload list. Atoms, bottom and top follow exactly the existing
structural expansion rules. Duplicate record labels or variant tags are
malformed inputs under the existing formation condition.

No semantic `RegularSub`, valuation, graph, satisfying model, or terminal
certificate appears in the clause-generation procedure. There is no general
head transitivity rule added to the native boundary relation.

## 3. Proven finite stabilization

Let

\[
  n_k = \mathrm{rows}(k)+|\mathrm{heads}(k)|,
  \qquad U=n_\mathrm{value}^2+n_\mathrm{effect}^2.
\]

`pairUniverse` enumerates all same-kind pairs of source indices below `n_k`.
The checked `mem_pairUniverse` theorem states that membership is exactly the
two endpoint bounds. `initialPending` filters out pairs already in the original
input. Each round partitions pending pairs by membership in the current
generated demands:

```lean
additions = pending.filter (fun p => p ∈ demands s prior)
remaining = pending.filter (fun p => p ∉ demands s prior)
```

If `remaining = pending`, the procedure stops. Otherwise it appends the
additions and recurses on the remaining list. `initial_separate`,
`additions_new`, and `remaining_separate` establish and preserve that pending
pairs are absent from the retained list. Every addition therefore supplies a
new comparison membership; original duplicates are retained unchanged.

The decisive termination theorem is

```lean
remaining_strict
  (changed : remaining s prior pending ≠ pending) :
  (remaining s prior pending).length < pending.length
```

The recursive implementation uses the initial pending length as its fuel.
`close_correct` proves this bound is sufficient. Its invariant consists of
bounded retained/pending lists and coverage of every bounded pair by one of
them. A changed round strictly decreases the finite pending length. A stable
round has no pending demanded pair. If the fuel reaches zero, the maintained
length inequality forces pending to be empty, and coverage itself supplies
closure. No caller chooses an unexplained cutoff or assumes stabilization.

The result is

```lean
clauses_correct
  (bounded : ∀ p, p ∈ s.clauses → Bounded s p) :
  (∀ p, p ∈ clauses s → Bounded s p) ∧ Closed s (clauses s)
```

Here `Closed s C` means every bounded generated demand is retained in `C`.
The remaining finite child-bound check below makes this sufficient for all
actual emitted obligations. `clauses_prefix` proves the stronger retention
statement

```lean
∃ extra, (completed s).clauses = s.clauses ++ extra
```

`completed s` has definitionally the same `rows` and `heads` as `s`. It changes
only the clause list. This enumeration is a proof-side reference algorithm;
its exhaustive pair table is not proposed as the native hot-path design.

## 4. Local checks and successful saturation

`solve s : Except Diagnostic System` performs these concrete finite checks:

1. Check every original endpoint against its kind's row-plus-head bounds.
2. Check every head's unique labels/tags and every child reference bound.
3. Compute the finite clause closure.
4. Check each resulting head/head obligation has a successful exact constructor
   expansion. Row-involving obligations do not need a constructor match.
5. Check bounds of every final generated obligation.

Failures carry finite offending lists: `malformedBounds` contains the original
bad comparisons; `malformedHeads` contains kind/head-index references;
`incompatibleHeads` contains failing retained comparisons; and
`malformedChildren` contains generated comparisons outside the finite universe.
The last check explicitly diagnoses any generated obligation outside that
universe. No completeness claim depends on silently dropping such a demand.

A failed structural expansion generates no children during iteration, but the
compatibility check still rejects its parent comparison. This keeps failure
distinct from a successfully expanded leaf such as equal atoms or bottom.
None of these checks decides `Saturated` as an opaque proposition; the three
closure fields are proved from the actual generated clause table.

`completed_saturated` constructs the five fields directly. `bounded` follows
from `clauses_correct`; `formed` follows from `checkFormation_iff`. Both
`rowRow` and `rowHead` follow from `row_consequence` and the closure theorem.
For `headHead`, compatibility provides an actual child list, `head_consequence`
puts every child in the generated demands, and closure retains them. The
existing `nodeRel_iff` converts this exact expansion into the required
`NodeRel` conclusion.

The main successful-output theorem is:

```lean
solve_success {s out : System} (success : solve s = .ok out) :
  out = completed s ∧ out.rows = s.rows ∧ out.heads = s.heads ∧
    (∀ p, p ∈ s.clauses → p ∈ out.clauses) ∧ Saturated out
```

The success premise is the return of this executable finite construction,
not the original native solver's return and not a supplied semantic model.

## 5. Leastness and exact syntactic completeness

`demands_in_extension` proves every emitted obligation belongs to any
same-table saturated extension containing the current list. The row cases use
that extension's precise `rowRow` and `rowHead` fields. The head case uses its
actual `NodeRel` expansion, including all signed children.

Induction through the executable iteration gives

```lean
clauses_least
  (sat : Saturated (withClauses s target))
  (included : ∀ p, p ∈ s.clauses → p ∈ target) :
  ∀ p, p ∈ clauses s → p ∈ target
```

This is leastness of comparison membership, not equality of list ordering or
multisets. It is also not a semantic least-model theorem.

The same inclusion supplies every local check from any saturated extension:
its boundedness covers the original and generated clauses, its formation
covers the unchanged head tables, and its structural condition establishes
every required successful expansion. Therefore:

```lean
solve_exists_iff (s : System) :
  (∃ out, solve s = .ok out) ↔
    ∃ target : List Comparison,
      (∀ p, p ∈ s.clauses → p ∈ target) ∧
      Saturated (withClauses s target)
```

This converse uses saturation only to characterize the exact syntactic
problem. Neither `solve` nor its successful-output soundness assumes a
saturated extension. Rejection excludes such an extension; this result does
not exclude every possible model of a different semantic system.

## 6. Original input interpretation and examples

Applying the accepted canonical construction to the proved output saturation
gives the following theorem for the **original input clauses**:

```lean
solve_original_model {s out : System} (success : solve s = .ok out) :
  out.graph.Valid ∧ out.graph.Guarded ∧
    (∀ p, p ∈ s.clauses →
      Lattice.RegularSub out.graph (renamePair out.names p)) ∧
    LatticeDecision.decideDemands out.graph
      (s.clauses.map (renamePair out.names)) = true
```

Graph validity, actual guard checking, model existence, and actual finite
decision acceptance are conclusions. All original references use the same
computed `out.names`; negative and positive occurrences are not assigned
independent interpretations.

`solve_original_store` applies this result to the existing `StoreSatisfied`
judgment under its exact syntactic `decodeStore` equation for the original
clause list. `solve_original_history` applies it to the existing graph-indexed
`ConstraintHistory` with that original list at the terminal state, deriving
the initial obligations. The decoder/history inputs remain genuine
correspondence obligations; an arbitrary final graph reconstruction does not
supply them.

The concrete recursive input has one value row, one effect row, a Function
using the same value row in both value ports and the same effect row in both
effect ports, and effect atom `7`. Its original four constraints are the two
directions of Function/row and atom/row comparison. It does **not** start with
the self/head comparisons needed for saturation. `recursive_solved` computes
successful closure by reflexivity. The original four-element `Store` decodes
by reflexivity, and `recursive_original_store_constructed` proves its
valid/guarded/shared interpretation. `recursive_original_decided` derives the
actual decision for those original four demands.

`alias_solved` computes success for the two-row alias cycle. Both interpreted
rows look up as structural bottom, and `alias_cycle_computed` derives the
actual original-clause decision. Separate reflexive computations reject
incompatible atoms, an out-of-bounds original comparison, and duplicate
record labels. Exact expansion computations retain Function signs, optional
metadata, tuple arity and variant payload arity.

## 7. Original scope and first remaining bridge

The reference construction covers every finite input of the existing
`System` grammar and checks its formation. It preserves the accepted exact
structural relation. No contradiction with that relation was encountered.
It does not claim that full native optional/width record adaptations or
contextual effects have this exact structural relation. The original
nontransitive producer/consumer boundary obligations, method plans, complete
Call, adaptation output ports, absence/non-resurrection, effect contexts and
authentic occurrence/scope identities remain in the parent.

The next native correspondence owner must derive the following from actual
successful native execution:

- A faithful finite row/head/original-clause readback from all eight physical
  lanes, preserving raw identities, representative transport and row kinds.
- Compatibility with this reference construction, including a proof of its
  success or equivalent original-demand interpretation. A native `Ok` is
  not itself `solve s = .ok out`.
- Actual output/reference/history transport into the one computed graph, or
  a proved relation preserving the needed source and consumer operations.
- Original publication metadata and source evidence covering every original
  source constructor and one shared scoped witness.

The accepted local replay component and inventory adapter are useful inputs
to those bridges. They do not globally establish them. No production
promotion, ordinary-inference completeness, principality, or original
algorithm termination is inferred from this finite reference result.

## 8. Verification and frozen evidence

Pinned Lean 4.35.0 accepted the final 557-line source. Six focused calls were
used: three retained failed checks, the first full construction success, the
final pending-separation refinement success, and the complete origin audit.
Every call had a 120-second process-group timeout, one thread, and `-M1024`;
no timeout occurred. No full/default integration build is claimed.

The final origin audit includes every declaration originating in this module,
including private/generated declarations: 142 declarations comprising 81
theorem constants, 55 definitions, four constructors, one inductive type and
one recursor. Three declarations are private. All 40 authored theorem roots
were required by the audit.

| Axiom dependencies | Theorem constants | All originating declarations |
| --- | ---: | ---: |
| None | 14 | 54 |
| `propext` | 26 | 47 |
| `propext, Quot.sound` | 41 | 41 |

No `Classical.choice`, project axiom, proof hole, unchecked native evaluation,
or kernel bypass occurs in the new component's audited dependency closures.
The complete printed types and axiom lists, actual commands/exits, source and
dependency hashes, retained failure details and cessation statement are in
the [handoff](../../tasks/agent-loop/inbox/20261026-inference-native-row-saturation.md).
Checker acceptance remains distinct from independent review and full
native/source correspondence.
