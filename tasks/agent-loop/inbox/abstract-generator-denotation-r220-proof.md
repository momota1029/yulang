# R220 constructive handoff — exact structural leaf readout and source cut

Sprint: R220, frozen contract SHA-256
`42ca0a85107b13af019dd6049e5b92d8bc03dadf51317ada45036af9120db79b`.
Assignment: `abstract-generator-denotation-r220-proof`; revision **1**.
Author/worker: `/root/abstract_generator_denotation_r220_proof`, sole author,
no descendants. Requested role/model/effort: Astra core producer / Astra /
medium. Observed effective model/effort: **UNKNOWN / UNKNOWN**.
Baseline supplied by Luna: `6f3656d9ae0214721df9e160e7ae69ba29ee773f`;
no Git operation used to inspect or change it.
Outcome: **candidate structural construction and exact source-interface stop**.
No new checked theorem, independent review, or production authority.

## Parent and application

The unchanged parent is `YulangClosure.SourceProblem.InferenceSoundness`,
`Contracts.lean:128`:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

The literal edge must use the same source, site, scope, generated constraints,
assignment and witness; L1 additionally fixes the original root and ambient
event. The structural reasoning below reaches the exact graph atom and bottom
at the chosen variable references. Its application stops before obtaining a
source descriptor/value row: the frozen model has no corresponding embedding
or source endpoint interpretation. Therefore parent-premise delta **0**,
roots **0/4**, packages **0/5**, hygiene theorem delta **0**.

## Concrete structural construction for the registered Lean prover

This is a proposed fragment of the independent generator, not a definition of
the missing full `generates`, `solves`, or `sameScoped` fields. The two variable
identities below are fragment inputs. They are not an assumed map from original
source endpoints. No source endpoint allocation or original denotation is
claimed by the fragment.

The following definitions are a precise Lean construction plan, **not checked
declarations**. They require the existing `OriginalSourceSyntax` and structural
syntax/publication imports, with their pinned meanings unchanged.

```lean
def literalCode : OriginalSource.Literal → Nat
  | .unit => 0
  | .bool _ => 1
  | .int _ => 2
  | .floatBits _ => 3
  | .string _ => 4
  | .bytes _ => 5
  | .path _ => 6
  | .character _ => 7

def literalStructuralFragment (valueVar effectVar : Nat)
    (literal : OriginalSource.Literal) : SimpleSub.Store :=
  [⟨.value, .atom (literalCode literal), .var valueVar⟩,
   ⟨.value, .var valueVar, .atom (literalCode literal)⟩,
   ⟨.effect, .var effectVar, .bottom⟩]
```

The tags are a proposed explicit eight-way type code, not payload encodings or
an assertion about existing native IDs. `literalCode (.int 1) =
literalCode (.int 2)` is intentional; the raw literal is retained separately
and its value is syntax-fixed. No payload is truncated: `floatBits` retains
`Nat`, `bytes` retains `List Nat`, and path/character retain `String`. The
eight-code agreement still needs its definition-level case proof when a
descriptor decoder is eventually defined; this note does not assume such a
decoder exists.

Exact intended theorem type, with `Regular` and `RegularPublication` referring
to the namespaces under `YulangClosure.SimpleSub`:

```lean
∀ (graph : Regular.Graph) (refs : RegularPublication.References)
    (valueVar effectVar : Nat) (literal : OriginalSource.Literal),
  RegularPublication.StoreSatisfied graph refs
    (literalStructuralFragment valueVar effectVar literal) →
  graph.lookup .value (refs .value valueVar) =
      some (.atom (literalCode literal)) ∧
  graph.lookup .effect (refs .effect effectVar) = some .bottom
```

This theorem has a genuine independently defined structural-satisfaction
premise. It has no source-law, solver-success, `LiteralDeclaration`,
`Kernel.atom`, source-judgment, or preselected readout premise. It does not
assert that these variable references are the original source coordinates.
There is no proposed theorem argument that assumes the missing source result.

### Exact local proof route

`SimpleSubRegularSolutions.lean:162` defines `expandNodes` by these relevant
clauses, in order:

```lean
| _, .bottom, _ => some []
| _, _, .top => some []
| _, .atom lower, .atom upper =>
    if lower = upper then some [] else none
```

The remaining successful clauses compare Function with Function, record with
record, tuple with tuple, and variant with variant; unmatched shapes yield
`none`. `expand` first obtains both nodes by `graph.lookup`. `RegularSub graph
pair` means every finite `Approx`; `regular_unfold` yields `Layer`, hence a
successful expansion. `regular_no_failed_expansion` rules out every `none`.

First auxiliary target, for either kind:

```lean
∀ {graph : Regular.Graph} {k : SimpleSub.Kind} {anchor target code : Nat},
  graph.lookup k anchor = some (.atom code) →
  Regular.RegularSub graph ⟨k, anchor, target⟩ →
  Regular.RegularSub graph ⟨k, target, anchor⟩ →
  graph.lookup k target = some (.atom code)
```

Use `regular_unfold` and `expand_endpoints_exist` to obtain the target node.
Case-split that node, or split the indexed kind first if elaboration requires:

| Target node | Forward atom-to-target expansion | Reverse expansion | Result |
|---|---|---|---|
| missing | `none` | immaterial | impossible |
| bottom | `none` | `some []` | impossible |
| top | `some []` | `none` | impossible |
| atom `other` | succeeds iff `code = other` | same equality | exact atom |
| Function/record/tuple/variant | `none` | `none` | impossible |

Thus the pinned graph grammar forces **exact node shape and atom code**, stronger
than only mutual-subtyping equivalence. It does not force reference-index
equality: `[.atom code, .atom code]` has distinct indices with the same node,
and mutual comparison between them succeeds. The theorem retains `refs` and
concludes a lookup equation, never `target = anchor`. This relies on the exact graph grammar, which
has no aliases or lattice nodes. It is not an exact-syntax theorem about finite
`SimpleSub.Sub` terms: e.g. a union of an atom with itself must not be excluded
from the whole language. `RegularPublication.decodeTerm` explicitly rejects
union/intersection, so this lemma cannot substitute for full lattice semantics.

Second auxiliary target (Effect alone suffices for the fragment):

```lean
∀ {graph : Regular.Graph} {target empty : Nat},
  graph.lookup .effect empty = some .bottom →
  Regular.RegularSub graph ⟨.effect, target, empty⟩ →
  graph.lookup .effect target = some .bottom
```

Obtain the target node from successful expansion. Effect nodes are only atom,
bottom and top. With upper node bottom, only the lower-bottom clause succeeds.
This explains why the one-sided upper bound `effectVar <: bottom` is enough;
the opposite `bottom <: effectVar` does not restrict a present node. Adding
that opposite clause is redundant for this local conclusion.

To prove the main target, specialize `StoreSatisfied` to its three literal
members. Unpack `ClauseSatisfied` and `decodeConstraint` using the existing
`RegularPublication.bind_some`. `decodeTerm (.atom code)` is `findNode`, whose
exact-node equation is given by `findNode_sound`; `.bottom` is analogous.
`decodeTerm (.var identity)` uses `checkedReference` on the very same
`refs k identity`; inspect the lookup to recover that same index. Combine the
first two comparisons with atom rigidity and the third with bottom rigidity.
There is no need to construct or choose a different graph/reference assignment,
and no need to assume `graph.Valid` beyond what local decoding already supplies.

Nonvacuity plan: the Value table `[atom 0, ..., atom 7]` and Effect table
`[bottom]` contain every required leaf. For one literal fragment, assign its
Value variable to `literalCode literal` and Effect variable to zero. Every
demand expands to `some []`. This is a construction argument, not an executed
test or checked theorem.

## Exact missing original equation and why structural work cannot provide it

`OriginalSourceInterpretation.Sorts` (`:23`) provides `Descriptor`, `Value`,
`Root`, `Scope`, `JointWitness`, and the other event components as independent
types. It supplies no constructor `Value : PaperTypes.Ty → s.Descriptor` and
no embedding of `PaperTypes.Value` into `s.Value`. `Event` (`:62`) retains the
full fiber, original/current assignments, history, configuration, witness,
scope, authority, incidence and dictionary. These are not graph node IDs.

`SourceAssignment` (`:830`) independently supplies `descriptor`, `value` and
`root` maps from `OriginalSource.Endpoint`, plus one `event`. Its `row` (`:837`)
reads **`.finalRoot`**, while the adopted base introduction must remain at the
literal's synthesis coordinate and annotation preserves the distinct
`synthesis → writtenTarget` boundary (`OriginalSourceGeneration:34`). The
literal atom carries `site` and raw payload, but no equation relates its row
lookup to those distinct endpoints.

The exact missing commuting equation is schematically:

```text
readOriginalSameAssignment(a, q.synthesis, original r, e₀, ξ, ω)
  = ⟨Value(τ(l)), v(l), original r, original e₀⟩

readOriginalReturn(a, q.synthesis, original r, e₀, ξ, ω)
  = ⟨Comp(empty, τ(l)), v(l), original r, original e₀⟩.
```

The names on the left and the carrier embeddings on the right are **missing
definitions**, not proposed assumptions or available symbols. Required owners
are the primary abstract source model's generator endpoint allocation,
`SourceAssignment` interpretation, and L1 Descriptor/Value/Return construction.
The structural lemma's `.bottom` also has no supplied equation identifying it
with the original intrinsic empty Effect. Identifying it does not erase
contextual permission, inflow, residual, Call or future obligations.

A precise separation argument explains this cut. `RegularPublication`'s
`References = Kind → Nat → Nat`, `decodeConstraint`, `ClauseSatisfied`, and
`StoreSatisfied` never inspect an `OriginalSource.Endpoint`, `SourceAssignment`,
root, or event. Keep a correctly solved graph/reference pair fixed. Any two
external `SourceAssignment`s differing only in the root at the same endpoint
are indistinguishable to every one of those structural predicates. With an
original root `r = false` and another row root `true` in a two-element carrier,
the claimed original-root equality can hold for only one projection. The same
independence applies to descriptor/value/event fields. This is a countermodel
to an implication using **unconnected carriers**, not a counterexample to the
adopted L1 rule or to an eventual concrete model with a proved connection.

The fixed source consumer is `sourceRules`' `.lit` constructor
(`OriginalSourceGeneration:85`), which requires the actual
`literalDeclaration` atom at the same source site/context. `LiteralAtom`
(`OriginalSourceInterpretation:845`) demands the declaration relation, ground
descriptor and ground row; `generated_literal_membership` only consumes these
already supplied through `literalKernel`. It cannot create the missing
embedding. `return_observation_iff` (`:680`) also retains event coherence,
world membership, observation guards, same-event value membership and positive
observation fields. Intrinsic bottom alone supplies none of those enclosing
premises.

## Reuse, limits and next actions

Reused R199/R213's separation of source rules from structural solving and L1's
all-eight-payload source introduction. Reused R219's `NO_SAFE_CODE_SLICE`; no
Rust owner audit or production edit repeated. Reused R214/R215 only as described
by the pinned R219 result: one-sided Value lower bound allows top; two-sided
bounds repair that local failure. The exact-node argument above strengthens the
proposed R215 equivalence route within this graph grammar. Historical notes
were not silently imported as additional theorem authority.

Rejected: replacing `Build`/`Satisfies` with independent generation/solving;
assuming `LiteralDeclaration`, `Kernel.atom` or the target source law; inventing
an endpoint map; treating paper typing as original Descriptor/Root/Event;
reading every annotated literal at `writtenTarget` or conflating it with
`finalRoot`; using intrinsic empty Effect to erase contextual obligations.

TODO `R220-STRUCTURAL-LEAF`: Luna may route the precise structural theorem to
the registered `lean_prover` under the existing exact module/cache lease after
freezing this candidate. Falsifier: a graph/reference assignment satisfying all
three clauses whose designated Value node is not the exact coded atom, or whose
Effect node is not bottom. Required output: checked theorem type and complete
axiom audit. This has no parent reduction by itself.

TODO `R220-ORIGINAL-EMBEDDING`: Luna's abstract model owner must supply the
concrete independently meaningful carrier/endpoint/Return equations above,
using the existing L1 source meaning. Falsifier: a satisfying same assignment
whose interpreted source row changes payload, original root/event/scope/witness,
or merges synthesis and written target. This is a model construction boundary,
not a request for a new literal semantic decision. After admission, compose the
structural lemma through these actual definitions and apply the unchanged `.lit`
source rule with the same scoped witness. All other source cases remain open.

## Pins, checks, resources and stop receipt

All contract dependency SHA-256 values were recomputed and match:

| Dependency | SHA-256 |
|---|---|
| R199 model | `33d0cd52fbbf07d7916804f8b8961c102b53cc1cf5e9260ac15d83de9f295aa0` |
| R213 model | `17319f77031c5f2135fb7ea14cffbea6d8e1b0b5466aa26d1b8bc5b14082223e` |
| R219 result | `a88fd7ec4c0e85850a384220776d6c32d1a480e3923ba8b278ac716aea1fbb18` |
| L1 adoption | `f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8` |
| Contracts | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| OriginalSourceSyntax | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| OriginalSourceGeneration | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| OriginalSourceInterpretation | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| SimpleSubConstraintSyntax | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| SimpleSubRegularSolutions | `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29` |
| SimpleSubRegularPublication | `18fc6f138204e1529dcd0bb9c01a20de7444a26e4dadc87677460ccd8ac9fc99` |

Supplemental primary-source read for the L1 payload/type table:
`PaperExecutionSyntax.lean`, SHA-256
`d0dc9871c382ca945059167b8b9e05f8f672170208a994f081e29760a207b87d`.
Its `PaperValueTyped.literal` is not used to identify the original source
interpretation. No added external dependency.

Read pinned environment: Lean `leanprover/lean4:v4.35.0`, project arguments
`-j1 -M1024`, no external packages. **No checker execution, build, theorem type
print, or axiom audit**: none is claimed, and the contract reserves actual Lean
construction/checking for the registered prover after this frozen seam.
Luna explicitly confirmed no cache/build spending in this stage. No tests,
Cargo, external contact, Git, or child launch. An initial source lookup for
`PaperTypes.lean` failed because that filename does not exist; resolved by
reading the actual `PaperExecutionSyntax.lean` declarations. No proof/checker
failure is concealed by that locator repair.

Three stages: authority/source alignment; structural construction and exact-node
proof route; application to original source interface and precise stop.
First clock receipt: 2026-11-01 21:05:25 UTC. Finite assignment limit: 900 s;
elapsed at freeze reported with the final hash receipt. No background work or
heavy process remains.

Only new/written path:
`tasks/agent-loop/inbox/abstract-generator-denotation-r220-proof.md`.
Scratch/cache/generated/Lean/production paths: **none**.
Writer state: **STOPPED after this revision is frozen**. No descendant leases.
The frozen byte hash is sent separately to Luna to avoid a self-hash equation.
Review and model admission remain with Luna; this producer does not certify
either its mathematical candidate or the original parent.
