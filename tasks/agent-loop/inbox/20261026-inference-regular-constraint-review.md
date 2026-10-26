# Independent review: regular constraint application

Date: 2026-10-26. Reviewer: `/root/execution_frontier`, non-author of this module and its regular-solution dependency. Bounded compiler-referee / Lean proof review. Sole write: this receipt. Previous source-reconstruction artifacts remain frozen.

## Verdict

**ACCEPT the Lean module for its explicitly represented regular structural fragment. No BLOCKING or MAJOR finding. One MINOR handoff wording correction is requested below.** The proof constructs backward reflection of a concrete graph-indexed constraint history from accepted finite final evidence. It does not prove native-history production, source reconstruction, arbitrary quotient correctness, completeness/principality, or original whole-language inference soundness.

### MINOR-1: describe equality insertion in the proved direction

Location: producer handoff `20261026-inference-regular-constraint-soundness.md`, lines 139–140, calls the equality-insertion consequence “forward preservation.” The actual theorem is `ConstraintStep.sound`, lines 342–357 of the module, with direction `after.Satisfied graph -> before.Satisfied graph`; the intrusion case simply projects the retained old obligations from the conjunction. It does not preserve every old solution after new equalities are imposed.

Concrete separating case within the represented semantics: the graph containing value nodes bottom and top has `RegularSub graph (bottom,top)`. A retained positive parent/copy pair for those two nodes can be qualified at a singleton source vertex. Adding both equality directions additionally requires `(top,bottom)`, which fails expansion. The old demand is satisfied while the equality-augmented demand is not. This is not a counterexample to the submitted backward theorem or a claim about an actual native source trace; it distinguishes the two logical directions.

Minimum repair: replace the phrase with “backward solution reflection of equality insertion” or explicitly state “satisfaction after insertion implies satisfaction of the retained old obligations.” No Lean source or checker rerun is needed for that wording repair. The remainder of the handoff already states the correct direction.

## Frozen inputs and evidence

| Input | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/SimpleSubRegularConstraintSoundness.lean` | `1d2266867115fc27afe39dbb80a3ca0e8f75247a2e16b739145137e83999de33` |
| Producer handoff `20261026-inference-regular-constraint-soundness.md` | `7b9c333d6f097271c83434cf4eb6c92589f717af8354caddd7ad1fb52ff62225` |
| `SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `SimpleSubConstraintSoundness.lean` | `33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293` |
| `SimpleSubRegularSolutions.lean` | `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |

The source module and all four dependency files are byte-identical between the shared checkout and the isolated checked project `/workspace/scratch/f98087c7ac1a/inference-regular-constraints/`. No source change was observed during review.

| Existing verification artifact | SHA-256 |
| --- | --- |
| `check-07.log` | `356004804ba91637c9468a7c88416496ebbb78668d62379baa408e16563f4cbb` |
| `audit-08.log` | `0e40ac4b14e9a6dcab3a19a3435a876b49a6039ba287a7487af635e8ed2d7559` |
| `RegularConstraintAudit.lean` | `4e7c096bd759314b553af34ac69150c6e21e6845fe698d442ad089d498d889d3` |

The build log records successful construction of the frozen module. I inspected the actual audit program: it enumerates originating-module theorem constants, requires all named roots, prints exact types and axioms, rejects project axioms, and permits only `propext` / `Quot.sound`. Parsing the existing audit independently gives **169 unique matched begin/end records**, **169 axiom records**, and all **50 authored theorem names** present; the remaining 119 are generated helpers. Axiom sets are exactly **43 empty**, **83 `{propext}`**, and **43 `{propext, Quot.sound}`**. No `sorryAx`, `Classical.choice`, error, or kernel-bypass entry appears. The source/dependency scan found no proof hole or unchecked native proof. These are existing producer verification results independently inspected; I did not rerun Lean.

## Semantic review

### All-depth relation, transitivity, and reflexivity

The target remains the frozen independent `RegularSub graph pair := forall depth, Approx graph depth pair`, with `Approx` unfolding the actual deterministic `expand`. It is not defined by certificate acceptance, finite-Term `Sub`, or a supplied semantic-model law.

`NodeRel` is proved equivalent to `expandNodes` through `nodeRel_iff`. Its Function case retains both negative ports and both positive ports. Record comparison retains the complete ordered list, exact label and optional bit; tuple and variant cases retain arity/order and all nested payload comparisons. Leaf rules are precisely the frozen bottom/top/equal-atom rules.

`Layer.trans` identifies the middle node using equality of the same deterministic lookup. `regular_trans` then inducts on unfolding depth; the Function argument and argument-effect premises are composed in the reversed order, while result-effect and result compose covariantly. No arbitrary recursive assumption or globally assumed transitivity is introduced. Global graph validity is unnecessary for transitivity because already-related endpoints force the required lookups at every relevant layer.

`regular_refl` correctly requires both `graph.Valid` and actual endpoint existence. Its coinductive diagonal relation propagates child existence through the original valid node. It does not assign a reflexive type to a missing or dangling reference. The main application obtains the global validity premise from the same final acceptance check.

The frozen `regular_unfold` uses successful expansion at depth one to fix one child list and deterministic equality to reuse it at all depths. Thus all-depth proofs do not choose incompatible child witnesses by depth. Cycles cross represented constructors; there is no new alias node or bare circular assumption.

### Extrusion and actual retained occurrences

`copyLink_asConstraint` and `copyEqualities_asConstraints` establish exact equality with the prior accepted `Copy.link` and `Copy.equalities`: positive parent-to-child, negative child-to-parent, and both directions for equality. They preserve kind, parent, child, and polarity. The embedding is explicitly variable/reference-only; it does not claim every finite Term has been decoded as this graph.

`Extrusion` has concrete copy, unchanged-existing-reference, and structural constructors. The structural constructor requires the actual `expand graph pair` child list; emitted copies are precisely the ordered concatenation of those child derivations. `Extrusion.sound` derives the desired comparison by structural induction and `regular_unfold`, from the emitted links. No arbitrary approximation or preservation law is smuggled into the constructor. A copy leaf is a finite cut around a potentially cyclic graph; it does not claim to simulate native allocation, levels, memoization, or freshness.

Both extrusion step directions compose correctly with the rewritten demand: upper extrusion yields `lower <= fresh <= upper`; lower extrusion yields the same chain with the structural traversal on its lower half. The original root demand is removed, all unrelated obligations remain, and the exact occurrence record is appended. Occurrence retention is proved through steps and histories.

The intrusion constructor requires membership of the actual occurrence in the retained list, the frozen `Occurrence.Qualifies`, and membership of every selected copy in that occurrence's original copy list. `Occurrence.Qualifies` delegates to the original `Contracts.Qualifies`, whose paths remain entirely within one immutable birth-level induced graph. Nothing substitutes mutable type levels, unrestricted global SCC membership, or mere endpoint birth equality.

Qualification is not used to prove backward reflection: retaining the old obligations suffices for that direction. Therefore the result neither establishes that qualification is necessary for safety nor proves that added equalities preserve all prior models/principal coverage. The provenance hypotheses constrain the represented intrusion rule independently.

`accepted_retained_equalities` is the general reflection lemma for a starting store already containing the equality list. Actual occurrence provenance comes from its application after a legitimate `ConstraintStep.intrude`; this lemma alone does not manufacture such an occurrence or qualification proof. The concrete cyclic example supplies both through its history.

### Accepted final evidence reconstructs original demands

`ConstraintStep.sound` proves each actual rule rather than consuming a general step law. Decomposition reconstructs its removed parent by `regular_unfold`; replay uses both bounds actually retained in the rest of the store and the proved transitivity. `ConstraintHistory.sound` composes the steps backward on one fixed graph.

The exact main theorem is:

```text
accepted_original_demands:
  ConstraintHistory graph ref birth first last ->
  accepts graph certificate last.obligations = true ->
  graph.Valid and first.Satisfied graph.
```

Its only semantic bridge is the already proved finite certificate checker correctness. No final model/valuation, initial solution, per-step preservation law, or original root membership in the terminal certificate is required. This materially removes the supplied-final-model premise for the represented graph history.

`accepted_original_joint` uses one concrete relation, `RegularSub graph`, for every original and final demand and proves it postfixed by the actual unfolding theorem. It is one shared structural interpretation; it is not uniqueness of models or the original source-scoped joint Call/effect strategy.

### Non-injective renaming

`GraphRenaming` is exactly the explicit lookup equation for every kind and identifier, including missing lookups. `renameNode` preserves constructors and all metadata and renames only child references. `layer_rename` proves one-step equivalence from that syntax equation; `regular_rename` derives all-depth equivalence. It does not assume the desired semantic quotient property.

The premise is strong: references may be identified only when the resulting lookup equation holds. In particular, existing and missing source identifiers cannot be merged at a target lookup under this premise, nor can different renamed node structures simply be identified. The concrete duplicate-atom example satisfies this stronger equation with a genuinely non-injective map. No claim is made for arbitrary native union-find merges.

`accepted_renamed_original` additionally and explicitly checks the source graph's validity, pulls accepted target demands back with `regular_rename`, and then applies the source history. It keeps a single graph interpretation throughout that history. A faithful decoder from a changing native allocation/merge trace into this shared graph is still required.

## Examples and scope

I inspected all example definitions and proofs. The cyclic example is substantive: Function results pass through required/optional records, tuple elements, and variant payloads back to Function roots, with a separate recursive record field. It emits all four copies with both input polarities reversed, retains an actual event, qualifies that event through valid singleton paths, and checks all equality directions. Removing the required effect direction causes finite acceptance to be false.

The mixed cyclic decomposition example removes the original root from the final *demand list*, while its cyclic certificate still contains the root because the unfolding cycle reaches it. The separate acyclic example proves the stronger point needed against circularity: the original Function pair is absent from the **entire terminal certificate**, which contains only child value/effect pairs, yet the history reconstructs it. These are distinct, accurately described examples.

The proof represents atoms, bottom/top, four-port Functions, finite exact-shape records with optional metadata, tuples, and finite exact-shape variants with payloads, including guarded structural cycles. It excludes union/intersection and their cycles, unguarded aliases, open native row tails, width/presence weakening, general native coalescing, and source/Call/effect interpretation. Generalization/independent-use regular interpretations are not proved here. Nothing promotes the original inference-soundness, completeness/principality, progress, or termination roots.

## Inspection limits, remaining seam, and stop

Read the full 657-line target and all its 50 authored theorem statements/proofs; inspected the entire regular-solution dependency and the exact Copy/Occurrence/qualification definitions, plus relevant all-depth/guarded-recursion and intrusion source authority. The earlier Syntax/Soundness dependency reviews remain applicable to the unchanged hashes. Inspected the exact printed types of the main semantic, extrusion, history, joint-relation, renaming, and equality roots and verified complete audit enumeration/counts. I did not individually re-prove every generated helper or rerun the build. Native field shape was cross-checked; native traversal/correspondence was not certified by this review.

The actual next native obligation remains: accepted no-error/admitted inference supplies a faithful represented graph, initial/final demands, this concrete history, and an accepted finite certificate. The original source seam remains separate: scalar/regular demand satisfaction must be connected to the unchanged original source-scoped judgments, Call/effect clauses, and shared witness. Neither seam is an implicit conclusion here.

No source repair, Git action, compiler run, Lean/cache write, scheduling edit, or child launch. Python reads used `PYTHONDONTWRITEBYTECODE=1`. This receipt is frozen after hashing; writes stopped.
