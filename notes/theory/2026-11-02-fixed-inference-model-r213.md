# Fixed inference model — R213

Status: **MODEL-INCOMPLETE**. This freezes the mathematical interfaces and
their authorities; it does not claim a concrete `SourceProblem` instance or
start a theorem that assumes the missing equations.

## 1. Parent statement and proof boundary

The first target is the unchanged
`YulangClosure.SourceProblem.InferenceSoundness`
(`notes/theory/lean/YulangClosure/Contracts.lean:128–130`):

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

The proof keeps the same source `s`, scope `x`, generated constraint `d`,
satisfying assignment `a`, and one witness `e`. It must not replace `a` by a
freshly selected source witness. The soundness theorem is solution-indexed:
it does not assume the abstract solver accepted a run. Endogenous solver
soundness supplies the independent `solves d a` premise only in a later
composition. This separates source/type soundness from solver termination and
solution construction.

The other original roots remain separate:

- `SourceScopedCoverage` reverses source derivability to a solution of the
  generated problem.
- `PrincipalCoverage` additionally needs the original principal predicate and
  instance order and a factorization for every source derivation.
- `InferenceTermination` needs the actual initial state and complete transition
  relation. It does not follow from a finite accepted-run soundness proof.

No root or dependency package is closed: **0/4 roots; 0/5 packages**.

## 2. Fixed syntax and source-rule model

The full original finite syntax is
`YulangClosure.OriginalSource.Source` in
`notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean`. It retains 13
expression forms, 11 pattern forms, 3 statement forms, ordered containers,
annotations, binding identities, operation arms, and the original OR-pattern
merge map. No supported form is dropped from this model.

`OriginalSourceGeneration.sourceRules` is a total, source-directed rule-tree
constructor. It constructs literal/primitive/name/App/RefSet/Lambda/tuple/
record/variant/selection/case/catch/block rules; all pattern, statement,
container, arm, binding, and client continuation rules; annotation boundaries;
and original initializer, Return/rebind, publication, Shared, execution, and
invocation scopes. It retains actual child sites, endpoint ports, branch order,
formal role, Call telescope, and source binders. `compile`/`Build` lower this
tree to symbolic `Formula`; `Satisfies` interprets formula leaves through a
supplied original `Kernel`. `reconstruction` proves equivalence between that
symbolic compiler and its own `Judgment` grammar.

The source-rule clauses were checked constructor by constructor in R213. In
particular, `App` creates a `viewLogic` existential, five named Call atoms,
two endpoint checks, and two same-context operand children. Those children do
**not** expand the complete callee-first `Bind`, returned-provider/current-
world, or distinct pending-suffix semantics. The complete Call atom
interpretation must supply those. Contextual effects are not a separate
`Source` constructor or generic row equation: permissions, inflow, residuals,
lineages, and future obligations remain in the meanings of the relevant
source atoms/checks and in the shared solution/readout. `RuleTree.choice`
existing in the syntax does not mean `sourceRules` emits every independently
licensed alternative.

**Boundary:** this is original source-rule construction, not Simple-sub
generation. `Kernel.atom`, `admitted`, `primitiveCheck`, `structuralShape`,
`functionShape`, `boundaryTag`, `conversion`, and `checkingAdmitted` remain
semantic inputs. `Build`/`Satisfies` do not define independent constraints or
prove those meanings from them. Reusing `reconstruction` is valid only after
the independent constraint model derives the actual same-coordinate local
premises.

## 3. Fixed abstract type/effect algebra

The reusable independent syntax is
`YulangClosure.SimpleSub.Term` and `Constraint` in
`SimpleSubConstraintSyntax.lean`. It retains separate Value and Effect kinds;
bottom, top, union, intersection, opaque atom identity; Function argument,
argument-effect, result-effect, and result ports; record labels and optional
bits; tuple order; and variant tags/payload order. Function variance is
`(-,-,+,+)`. The paper's structural Union remains in the core: both branches
of `if true { 1 } else { "str" }` contribute to `int | str`.

`SimpleSub.Sub` is the retained finite structural derivability relation.
`Constraint.Satisfied` and `Store.Satisfied` quantify over a finite-Term
valuation. They are not the complete regular recursive solution model. The
independent regular comparison model is `SimpleSubRegularSolutions.RegularSub`
over graph nodes and all finite approximants; `SimpleSubLatticeInference`
defines graph-decoded `ClauseSatisfied` and `StoreSatisfied`. These are useful
structural components, but neither defines a source-indexed `p.solves` or its
coordinate/readout relation. No assumption equates finite-Term substitution,
regular graph assignment, and the mutable solver state.

**Authority:** the top-level inference principles select generation,
accumulation, propagation, level-based extrusion, value-reference-SCC
intrusion and generalization as the mathematical algorithm. Their selected
construction is not a post-hoc search over candidate typings. Existing local
step-preservation theorems remain conditional on their explicit graph,
history, occurrence, level, copy, and qualification data.

## 4. Required source-indexed model equations

The concrete `SourceProblem` instance must supply these *independent*
definitions, all over the same original source and scope:

1. **`generates s x d`:** actual finite Value/Effect constraints produced
   structurally from the full source and its binder/occurrence scopes. This
   cannot inspect `sourceJudgment`, solver success, a chosen solution, or Rust
   receipt/owner IDs.
2. **`solves d a`:** one regular structural assignment for all constraints in
   `d`, preserving all four Function ports and source coordinate identities.
   It cannot call `Kernel.atom` or take source typing as a premise.
3. **`sameScoped s x e a`:** a constructive decoding of that same assignment
   into every source witness component, retaining imports, one shared hidden
   witness, all uses and futures, scopes, roots, events, effects, and original
   bounds. Endpoint equality or a newly chosen witness is insufficient.
4. **Constructor compatibility:** from each generated constraint's
   satisfaction, derive the corresponding independently fixed source local
   premise, then use the actual `Judgment` constructor. The literal, Name,
   Lambda, App/Call, patterns, statements, operations, handlers, annotations,
   checks, conversions, and contextual effects all remain in the induction
   domain.

For App, the original rule emits one `viewLogic` existential; five base
coupled atoms (`descriptorFormation`, `wholeArgumentCompatibility`,
`completeCallCertificate`, `sourceCallIncidence`, `callableImage`), the
value check from callee `returnedValue` to App `descriptor`, and the
computation check from App `callableImage` to App `synthesis`, plus both
operand derivations under the same scope. An independent constraint
interpretation must yield those exact clauses for the same candidate and
telescope. `NativeInterface` or structural Function shape is not that law.
There is also a conditional sixth atom, `roleAndInitialCallOrigin`, appended
exactly when `singletonFormalCall context callee argument` is true. That
predicate requires two unannotated Name operands; the callee resolves to a
single-use, unannotated Value formal, and the argument resolves to a Value
formal. The atom stays under the same `viewLogic` witness and has the same App
site/context/operand sites. The independent model must derive this atom on
that exact branch; omitting it loses an original premise. A concrete
nonvacuous formal-context fixture is recorded in
`SourceAppAdmissionR159.lean:279–294`.
   The complete Call authority separately requires callee Bind into the actual
   returned provider/current world, distinct callee-/receiver-pending suffixes,
   and all independent arms; the generated App children alone do not encode
   that phase law. Pure `ReadInvoke` and computed `EvalInvoke`/`InvokeTail`
   remain distinct and must use the actual result slot, not an arbitrary
   endpoint equality.

For annotated literals, the original derivation retains the synthesized
`synthesis` endpoint and a separate `writtenTarget` boundary. The L1 base
introduction fixes `Value(τ(l))`, the raw literal value, pure `Return`, and the
original `(occurrence, root, event, scope, witness)`. The base rule is not
exhaustive literal checking: annotation, structural, method, adapter,
conversion, and enclosing contextual-effect premises remain. Therefore a
readout that maps every annotated literal directly to the written target or
final root would be wrong.

## 5. Equation ledger

| Component | Classification | Exact reason / next owner |
|---|---|---|
| Original raw syntax and source-directed rule-tree equations | **FIXED** | `OriginalSourceSyntax` and `OriginalSourceGeneration`; use their exact constructors and endpoints. |
| Symbolic rule-tree compilation/reconstruction | **FIXED, conditional on local Kernel** | Existing `compile`, `Build`, `Satisfies`, `reconstruction`; does not establish independent Kernel meanings. |
| Source Call and contextual-effect authority | **FIXED as source obligations; not interpreted by the Simple-sub model** | Complete Call, pure-read/computed-call result, effect-hygiene, and residual-lineage authorities listed below. Preserve ordered suffixes and the permission/inflow distinction. |
| Structural Value/Effect terms, ports, and finite subtyping rules | **FIXED** | `SimpleSubConstraintSyntax`; incomplete for regular recursion and contextual source admission. |
| Regular graph comparison / finite certificate soundness | **FIXED, structural only** | `SimpleSubRegularSolutions`; does not construct a source-indexed assignment or readout. |
| Source `Literal` L1 base type/value/Return | **FIXED** | Authoritative L1 adoption. All-payload constraint generation, solution readout, and annotated synthesis/target connection are **OPEN**; owner: primary abstract source-model construction. |
| Independent meaning of each source `Kernel` leaf/check/admission | **OPEN** | Existing modules retain supplied `Kernel` fields. The model must derive every leaf used by the original judgment from independently generated constraints and authorized local source meaning; owner: primary/source semantics. |
| Full source-to-constraint generator `generates` | **OPEN** | No existing concrete all-source generator emits the independent type/effect store. Owner: primary abstract model construction. |
| Regular solution interpretation `solves` and one shared source readout | **OPEN** | Existing graph/regular relations are structural inputs; no concrete map to source scopes, witnesses, worlds, roots, and effects. Owner: primary abstract model construction. |
| Full App/Call and contextual-effect equations | **OPEN** | Original coupled App premises and selected call telescope need independent same-witness meaning. The dependent typed-Union selected-branch result transport remains an open bridge; owner: primary/source semantics, with pending user question unchanged. |
| Conditional singleton-formal App origin | **OPEN** | `roleAndInitialCallOrigin` is present exactly on the `singletonFormalCall` branch under the same `viewLogic` witness; its independent constraint interpretation is not defined. The nonvacuous source fixture is `SourceAppAdmissionR159.lean:279–294`. Owner: primary/source model. |
| Endogenous accumulation/propagation/extrusion/intrusion/generalization algorithm | **OPEN** | R212 initializes rows and proves finite diagnostics but has no full transition/run/accepted/readout chain. Owner: primary abstract algorithm. This is separate from the solution-indexed soundness root. |
| Principal order and instance factorization | **OPEN** | `PrincipalCoverage` is parameterized; no concrete original order/factorization. Owner: primary metatheory. |
| Complete inference accessibility | **OPEN** | No complete `inferStep` for the selected algorithm, hence no whole-transition well-founded proof. Owner: primary metatheory. |

The first concrete source-to-constraint equation to construct after model
review is the adopted literal case, not a new L1 semantic decision. For the
same source literal `l`, site `q`, root `r`, event `e₀`, scope `ξ`, and shared
witness `ω`, the independent generated Value/Effect constraints must yield
the adopted descriptor/value/pure-Return facts and their original coordinate
readout. In an annotated case, the `q.synthesis → q.writtenTarget` boundary
must retain the distinct target and enclosing effect/checking premises. The
current `OriginalSourceInterpretation.LiteralDeclaration` is an unconstrained
relation on `(literal, ValueRow)` and `SourceAssignment.row` reads `.finalRoot`;
neither equation connects the adopted L1 row to the independent constraint
solution. The source-local owner is the primary abstract generator/readout
model, consuming the already adopted L1 rule.

The constructor map also reveals two exact scope hazards for later equations:
App's source tree does not itself encode callee-first Bind/current-world and
pending-suffix execution; and contextual permission is distinct from actual
effect inflow and residual effect. Any constraint/readout equation that merges
these coordinates would fail source correspondence. The selected
typed-Union question concerns the dependent branch/result telescope inside
Call incidence only; it does not block ordinary structural Union.

## 6. Composition and residual gate

Once the first four open items above are fixed independently, soundness is a
constructor induction over the unchanged source derivation shape:

```text
generates(s,x,d) ∧ solves(d,a)
  -> each source-rule constraint holds under the same a and original scope
  -> each original local premise is derived
  -> reconstruct Judgment and witness e
  -> sameScoped(s,x,e,a)
```

This is the exact solution-indexed proof direction. A whole-run solver theorem
may later prove `solves d a` for a produced accepted solution; it is not a
premise needed to prove the implication for arbitrary `a`. Principality and
termination remain separate roots, and Rust/native correspondence remains
downstream.

**Gate result:** `MODEL-INCOMPLETE`. The full generator, independent source
leaf meanings, regular solution-to-source readout, and complete Call/effect
compatibility equations have not been defined from existing authority. No
theorem packet is admitted until an authorized model fixes the equations needed
for its whole original domain. No parent premise moved in R213 at this point.

The exhaustive constructor/source-premise mapping used for this classification
is encoded by the pinned `OriginalSourceGeneration.sourceRules`,
`statementRulesK`, `statementsRulesK`, `expressionRulesK`, `bindingsRulesK`,
and `clientRules` equations. R213's read-only source map confirms coverage of
all 13 expression forms, 11 pattern forms, 3 statement forms, containers, and
all client constructors; it supplies no semantic meanings for those premises.

## 7. Direct input pins

Rechecked for R213:

- `Contracts.lean`: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `OriginalSourceSyntax.lean`:
  `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`
- `OriginalSourceGeneration.lean`:
  `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`
- `OriginalSourceInterpretation.lean`:
  `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`
- `SimpleSubConstraintSyntax.lean`:
  `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6`
- R212 `AbstractSimpleSubCore.lean`:
  `023635d283f9a00e906ec965a6eaa5595eab21f2b93f353a1d5ea0ede0bffb6c`
- root-first plan:
  `890fa8a5a1c88c6400e293870598750b285fe12075ad13cbd3e884cc71921c16`
- Literal L1 adoption:
  `f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8`
- top-level algorithm authority:
  `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`
- selected Source-Generalize source schema:
  `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`
- Source-Generalize proof construction:
  `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`
- complete Call contribution:
  `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e`
- pure ReadInvoke result:
  `8d1eb7ecea3e63d7ba0ae091dc673f3321e52fc0e31c5d824bdf4f1656b99488`
- computed EvalInvoke/InvokeTail result:
  `2f3a5461b6dacaa29e881ba8b3003120b912e441dd5e4c47fc4ccaa27d3b31a6`
- annotation effect hygiene:
  `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`
- contextual residual lineage:
  `d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98`
- regular solution semantics:
  `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29`
- regular graph store satisfaction:
  `c534c060dfde84f2817fbaa53222f430b59d9b6377cfacedabeca7b9b4b8ffa3`
- nonvacuous conditional singleton-formal App source fixture:
  `5e948a1f8a3aab66028f885ebf16b6ffeed81999039e8a5a4e9c3caf84464408`
- R213 read-only source-rule map was produced against the pinned syntax and
  generation files; it is an evidence report, not an authority or theorem.
