# Canonical regular models of saturated finite structural row stores

Date: 2026-10-26.
Status: constructed and kernel-checked component; pending independent review.
Assigned baseline: `yulang3`, `bf81a1bd444b3bcbecca6b754ea6fb603262f368`.
Scope: the exact structural `Regular.Node` / `Lattice.RegularSub` interpretation
already used by the inference proof modules. This is not a new definition of
native inference success or original source typing.
Lean source: `notes/theory/lean/YulangClosure/NativeRowModel.lean`.
Frozen Lean SHA256:
`16835744153d05150992175ddb866ccc202e0f31781ed1a5a26c3e55c54a26bb`.

**The full original `SourceProblem.InferenceSoundness` remains OPEN.** This
construction removes graph/model existence and final finite-decision success
from a precisely stated structural component. Native normalization and
saturation, actual history/allocation alignment, original metadata, optional
record boundary semantics, contextual effects and complete source/Call
reconstruction remain separate obligations. None is silently restricted out of
the parent theorem.

## 1. Original obligation and the removed premise

The original parent, from `YulangClosure/Contracts.lean`, remains

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

The already accepted
`LatticeGrowingInference.completed_decided_growing_publication_with_clients`
constructs original Store decoding and uses locally indexed graph-growth and
constraint histories. It still needs a faithfully chosen terminal graph and
the fact that its computed terminal decision is true. A raw native row number
does not provide that graph node or its meaning.

The new theorem starts from finite **syntax**: row counts, finite structural
head tables, and a finite normalized inequality table. Its syntactic saturation
conditions mention only bounds, table membership, exact constructor labels,
and structural child comparisons. It computes one graph and one reference map,
proves every retained inequality in the independent all-depth relation, proves
graph validity and the actual guard Boolean, and derives the actual finite
decision result. No graph, variable valuation, `RegularSub`, supplied
certificate, or successful terminal checker is a construction premise.

This is a satisfying model construction, not principality, preservation of
every previously chosen model, or proof of a least fixed point in a semantic
order. Negative Function occurrences make a naive monotone fixed-point
argument inappropriate. The proof instead uses the existing guarded
structural relation and explicit finite lattice derivations.

## 2. Exact finite input

`NativeRowModel.System` contains:

| Field | Meaning |
| --- | --- |
| `rows : Kind → Nat` | Finite number of source row references, separately for value and effect kinds. |
| `heads : (k : Kind) → List (Regular.Node k)` | Finite structural syntax, whose child references use the source numbering below. |
| `clauses : List Regular.Comparison` | Finite same-kind directed inequalities; duplicates are harmless. |

For kind `k`, source numbers below `rows k` denote rows. Source number
`rows k + h` denotes structural head `h`. These are source-table addresses,
not final semantic-node numbers. `System.names` computes the latter.

The structural head grammar is exactly the existing one: atoms, bottom, top,
Function with four kind-correct ports, finite records with labels and optional
bits, ordered tuples, and variants with tags and complete ordered payloads.
`renameNode` changes references only; `rename_unique` and `rename_references`
prove that metadata and child incidence are retained.

For a row `x`, let

\[
 L(x)=\{h\mid h<|\mathrm{heads}_k|\ \land\
                 (\mathrm{head}(h)\le x)\in C\},\qquad
 U(x)=\{u\mid u<|\mathrm{heads}_k|\ \land\
                 (x\le\mathrm{head}(u))\in C\}.
\]

The executable lists enumerate head indices in increasing order. They are
constructed by finite range/filter operations, not selected by a semantic
existence theorem.

### Independent syntactic saturation

`Saturated s` has five concrete fields:

1. **`bounded`.** Both endpoints of each retained clause lie in the finite
   row-plus-head source table of its own kind.
2. **`formed`.** Every head has unique record labels/variant tags and every
   child reference lies in the corresponding kind's finite source table.
3. **`rowRow`.** A retained row inequality `x ≤ y` implies
   `L(x) ⊆ L(y)`. This is lower-anchor propagation along a row edge.
4. **`rowHead`.** A retained `x ≤ head(u)` and any `h ∈ L(x)` imply that the
   direct head comparison `head(h) ≤ head(u)` is retained in `C`.
5. **`headHead`.** Every retained head-to-head comparison passes the existing
   `Regular.NodeRel` constructor test with **clause membership** as its child
   relation. In particular, Function generates exactly
   `(upper.a ≤ lower.a)`, `(upper.ae ≤ lower.ae)`,
   `(lower.re ≤ upper.re)`, `(lower.r ≤ upper.r)`.

These fields are finite syntactic closure/consistency obligations. They do not
assert that the resulting clauses already have a model. Neither the fields nor
the construction import an arbitrary transitivity rule for native concrete
comparison. Pure row reachability may be closed first, and the resulting
finite `C` may contain both original inequalities and their syntactic routing
and constructor descendants.

An implementation connection must prove these fields from the actual finite
history, including the full physical inventory. Merely packaging them in the
record does not prove that connection. The independent saturation lane reports
a complete-block replay result for a restricted actual path; it does not yet
establish these fields for all native histories.

## 3. Computed graph and one shared row meaning

The graph uses three finite slot forms:

```lean
Slot.head h
Slot.lower row suffix
Slot.upper row suffix
```

All head slots are listed first. For each row, the construction lists every
suffix of `L(row)` and `U(row)`. The first occurrence index of a slot gives its
deterministic semantic reference; `lookup_idxOf` and `lookup_slot` prove the
actual lookup equation. No injectivity assumption about incidental native IDs
is used.

The emitted nodes are:

\[
\begin{aligned}
\mathrm{emit}(\mathrm{head}(h))
  &=\mathrm{structural}(\mathrm{renameNode}(\mathrm{names},H_h)),\\
\mathrm{emit}(\mathrm{lower}(x,[]))&=\bot,\\
\mathrm{emit}(\mathrm{lower}(x,h::t))
  &=\mathrm{head}(h)\ \cup\ \mathrm{lower}(x,t),\\
\mathrm{emit}(\mathrm{upper}(x,[]))&=\top,\\
\mathrm{emit}(\mathrm{upper}(x,h::t))
  &=\mathrm{head}(h)\ \cap\ \mathrm{upper}(x,t).
\end{aligned}
\]

`names(k,x)` for a row is the index of `lower(x,L(x))`.
`names(k,rows(k)+h)` is the index of `head(h)`.
**Every occurrence of one source row uses this same map**, including both
negative Function ports, both positive ports, repeated fields and shared
payloads. There is no polarity-indexed independent valuation.

The chosen row meaning is the lower join. Its upper meet is also represented
in the graph, but is a separate node. `canonical_interval` proves that the
chosen row lies below that meet; it does not identify them. The checked
`lower_join_upper_meet_need_not_equal` discriminator has one unconstrained row:
its lower node is bottom, its upper node is top, and the computed reverse
comparison is false.

### Alias-only and recursive components

Pure aliases are not emitted as edges. Saturation propagates their reachable
structural lower roots into `L`; a component with no such root has an empty
list and is represented by bottom. `empty_lower_bottom` proves this directly,
and `alias_cycle_constructed` checks a two-row cycle without a supplied graph.

A Function may refer back to the row that includes that Function among its
lower roots. Such a cycle crosses a real structural constructor. Every
lattice-only traversal strictly shortens a finite suffix. `check_lower` and
`check_upper` prove acceptance with more fuel than the suffix length;
`canonical_guard_checked` proves the existing graph-wide checker succeeds
using its actual finite fuel. Guard acceptance is a theorem of the
construction, not an assumption that native syntax was already guarded.

This normalization assigns a satisfying model to alias-only bound cycles. It
does not claim equivalence with every unguarded recursive source type or with
the reference paper's syntactic types such as `mu a. a`.

## 4. Proof of every retained bound

Use one shared relation

\[
 R=\{\mathrm{renamePair}(\mathrm{names},c)\mid c\in C\}.
\]

`postfixed` proves `R p → Lattice.Layer graph R p` by four endpoint cases:

| Endpoints | Finite derivation |
| --- | --- |
| Head → row | Membership in that row's lower list gives a finite chain of union injections. |
| Row → row | `rowRow` gives lower-list inclusion. Inject each lower head into the target join, then eliminate the source join. Empty lower lists use bottom. |
| Row → head | `rowHead` supplies every concrete lower-head/upper-head comparison. Each one uses the structural expansion below; eliminate the finite source join. |
| Head → head | `headHead`, `nodeRel_rename` and `nodeRel_iff` produce the actual structural expansion, with every child in the one relation `R`. |

Only the last case consults the recursive relation, and it does so across
structural expansion. Union/intersection/transitivity reasoning at the
current structural depth is a finite proof. In particular, a row-to-head
obligation does not discharge itself by an immediate cyclic hypothesis.

Existing `Lattice.coinduction` now gives

```lean
canonical_bounds (sat : Saturated s) :
  ∀ p, p ∈ s.clauses →
    Lattice.RegularSub s.graph (Regular.renamePair s.names p)
```

`canonical_valid` separately proves every emitted graph reference exists and
all structural metadata is lawful. Together with the actual guard result,
the accepted exact finite decision theorem gives

```lean
canonical_decided (sat : Saturated s) :
  LatticeDecision.decideDemands s.graph
    (s.clauses.map (Regular.renamePair s.names)) = true
```

Thus both the regular model and finite terminal evidence are consequences of
finite syntax and saturation. No finite derivation certificate is supplied.

## 5. Application to original inference consumers

`canonical_completed_publication` directly instantiates
`completed_decided_growing_publication_with_clients`. It retains the original
lawful constructor inventory, bounded publication metadata, inactive images,
stopping closure, actual use bounds, coverage and interleaved `GrowingHistory`.
The terminal graph is the computed `s.graph`, terminal comparisons are the
computed renamed `s.clauses`, and `canonical_decided` discharges the former
terminal-success premise.

The exact alignment still matters: the actual completion/history must end in
that constructed graph with those comparison references. This theorem does
not infer prefix compatibility between an arbitrary operational graph and the
new canonical numbering. In particular, reconstructing a final graph after a
mutable trace does not itself give the required growing history. The native
correspondence owner must either construct the history with the known final
interpretation or prove its exact transport. This is an explicit syntactic
correspondence obligation, not an assumed satisfying model.

`canonical_decoded_store` also applies the result directly to the existing
`LatticeInference.decodeStore` / `StoreSatisfied` definitions when the exact
readback equation is known. The concrete `recursiveStore` includes the
original four-port Function term, actual value/effect variable terms, atom
terms and inequalities in both directions. `recursive_decoded` computes its
readback by reflexivity. `recursive_store_constructed` proves validity,
guardedness and satisfaction under the one computed interpretation. This
worked instance is not a replacement grammar for the whole source language.

## 6. Exact native correspondence boundary

The actual source owners inspected were:

- `crates/yu-solver/src/lib.rs`: endpoint kinds, candidate application and
  structural comparison branches.
- `candidate_extrusion.rs`: row memoization before selected-bound traversal,
  retained parent/copy links, all four Function ports and selected bounds.
- `candidate_intrusion.rs`: representative forests, original parents, groups,
  later reuses and qualification-dependent equality.
- `candidate_scheme.rs`: canonical row keys, polarity-bearing captured nodes,
  Function/record/variant/tuple rebuilding, effect operands and stored bounds.
- `term.rs`: native constructor views and the four distinct Function terms.

The companion inventory lane normalizes **all eight physical lanes**:
value/effect × lower/upper × direct-row/structural entry. A lower entry means
`item ≤ owner`; an upper entry means `owner ≤ item`. Both sides are necessary,
because native row/row storage chooses an owner partly by levels. Enumerating
only canonical representatives' lower vectors loses retained inequalities.
Raw owner, lane, slot index, current representative and canonical endpoints
must remain distinct in the source receipt. Source rows can then be assigned
dense kind-correct indices; raw row IDs are never themselves semantic nodes.

For this component the proposed adapter performs exact structural readback,
normalizes both bound directions, closes unchanged-view row flow, and retains
the concrete lower/upper root queries and structural children. It must prove
the five `Saturated` fields, original-clause coverage, and the actual
history/publication alignment. Completed replay records, fresh-use maps,
extruded bounds, later reuse qualifications and canonical merges cannot be
recovered merely from a successful final scalar return.

### Why this is not all native record/effect semantics

`Regular.recordPairs` requires matching finite labels, order and optional
bits; `variantPairs` preserves exact tags and payload shape. The native
record comparison in `lib.rs` supports width and presence behavior that this
relation does not represent. The original manuscript
`docs/yulang-whole-language-semantics-ja-expanded-20261023.tex`, sections
“省略可能レコードを解釈する境界意味論” and
“型変数の伝播と、具体変換の境界を接続する”, explicitly distinguishes
unchanged-view variable flow from an actual typed adaptation at boundary `j`.

Its discriminator is `A={foo?:string}`, `B={}`, `C={foo?:int}`. The adaptations
`A→B` and `B→C` can succeed while direct `A→C` fails. An intermediate choice
`row=B` must not bypass the original concrete endpoint query. This construction
does not claim such a bypass: its exact structural `headHead` field does not
admit those optional/width comparisons in the first place. Calling this
fragment the complete native relation would be false.

The concrete stronger continuation is therefore the original one: preserve
producer anchors and unchanged-view row routes; retain each consumer demand's
actual boundary identity; require the direct endpoint query at that boundary;
retain its exact record/cast/method/Call evidence constructor and typed child
plans. An adaptation creates a separate output port and producer view instead
of an identity row edge. Record plans must preserve absence, target field
order, child effects and non-resurrection of hidden fields. Effect operands
also retain authentic context/scope/occurrence identities. Those existing
source operations require their own finite realization proof; replacing them
by a wider transitive `RegularSub` rule is not justified.

This proposal selects no new language semantics or production representation.
It names the actual missing evidence and its owning construction. No opaque
`LocalLaws` parameter is presented as the completed native bridge.

## 7. Reference and verification boundary

Parreaux, *The Simple Essence of Algebraic Subtyping*, §§5.1–5.3, Fig. 10 and
Figs. 11–12, was read from the pinned local paper/text copies. The paper's
unifying-coalescing discussion motivates the need for correlated occurrences;
the present construction proves its own lower-join model theorem and does not
assert identity with ordinary or unifying reference coalescing. The paper's
non-let theorem and footnote 15 do not prove Yulang let/extrusion/intrusion,
contextual effects or complete Call.

Pinned Lean 4.35.0 accepts the final 600-line module. The complete module-origin
audit prints types and axiom dependencies for **all 209 originating
declarations**, including 17 private declarations: 137 theorem constants,
61 definitions, five constructors, three inductive types and three recursors.
All 18 required result roots are present. The theorem axiom sets are 41 empty,
35 `propext`, 55 `propext, Quot.sound`, and 6
`propext, Classical.choice, Quot.sound`. The six choice-dependent declarations
are confined to the recursive example proof chain; every generic canonical
construction theorem uses only `propext, Quot.sound`. No project axiom,
`sorryAx`, unchecked native evaluation or checker bypass is present.

Commands, retained failed checks, complete printed theorem types/axioms,
input/artifact hashes and write-cessation are recorded in
`tasks/agent-loop/inbox/20261026-inference-native-row-model.md`. Checker
acceptance is not independent review or full native/source correspondence.
