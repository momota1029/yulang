# Production HIR: empty-Record structural-shadow theorem

Date: 2026-10-04
Status: source-generation result; no implementation or semantic authority
Scope: the structural value shadow of complete current `yu-hir` bindings
Depends on: [source-generated structural theorem](../design/2026-10-04-source-generated-callback-structural-theorems.md), §5–7

## Statement

For every finite error-free `HirModule` produced by the current local
`lower_module` path, its monomorphic structural value shadow has a finite
descriptor graph over `Int` and `Function` only. In particular, its nonempty
Record alphabet is empty (`Λ = ∅`). The result remains true with recursive
references between local definitions. After finite rational equality
normalization, the package has no directed structural inequalities and no
rigid-name permission obligations; therefore it satisfies Theorem S's
closed-anchor/one-open-anchor predicate. If the generated equations are
satisfiable in the arbitrary-tree structural domain, they have a regular
witness. This is an application of Theorem S, not a new general regularity
argument.

The source property is independently checkable before solving: enumerate the
finite HIR nodes and verify that every node is one of the admitted cases below.
The proof does not inspect a solution, regularity, or a solver outcome.

## Source generator and proof

The current `ResolvedExpr` has exactly `Lambda`, `Integer`, `Name`, and
`Error`. For this theorem, exclude `Error` and require resolved names. The
current lowerer admits a binding body as one atomic integer/name; a
parameterized binding wraps that atom in one `Lambda`. Direct expressions
are also integer/name atoms. There are no source annotations or external
semantic roots in this lowering path (`SemanticImports` is empty and ignored
by `lower_module`).

Allocate one structural endpoint for each local definition, parameter, and
expression occurrence. Generate clauses as follows:

| HIR source | Structural shadow clause |
|---|---|
| integer | endpoint equals `Int` |
| parameter name | endpoint equals its parameter endpoint |
| resolved local name | endpoint equals the referenced definition endpoint |
| unparameterized binding | definition endpoint equals its body endpoint |
| parameterized binding | definition endpoint equals `Function(parameter, body)` |

The traversal is finite because it visits the finite HIR graph once and
allocates definition endpoints before resolving references. A recursive name
uses its already allocated endpoint; it does not unfold the target definition.
Thus every generated descriptor is either `Int` or a finite-arity
`Function` node. No case emits a Record, an inequality, or a rigid name.
The equality quotient may merge aliases and recursive endpoints, but cannot
introduce a new constructor label. Its free/free inequality graph is empty,
so each free component has no anchors and is a grounded G component in §6 of
Theorem S. With no rigid identifiers the rigid-scope premise is vacuous.

Theorem S therefore supplies the stated regular witness whenever the shadow
equations are satisfiable. The existence claim is conditional; this record
does not claim every HIR module is well typed. It also does not change the
original equations or infer that a particular chosen witness is principal.

## Boundary with production inference

This theorem concerns a deliberately named **structural value shadow**. It
does not erase or interpret the four Function ports in the current polarized
`yu-solver::TermView`, whose Function nodes include effect components. Pure
role and empty-effect handling remain governed by the source introduction
rules; this proof makes no effect-row, `never`/`Any`, or port-subtyping claim.
The shadow is not proved equivalent to the current F5 solver's generated
constraints, and is not the full successor inference generator. Applications,
Records, callback expected interfaces, annotations, imports, and open-world
clients remain outside current HIR or this theorem.

The gap is visible on the smallest lambda. `ConstraintBatch::collect` records
a `LambdaRecipe`; `InferenceSession::admit_lambda_fact` later creates a
positive four-port Function term
`Function(negative-parameter, EmptyEffect, body-effect, result)` and admits
the directed fact from that term to the definition root. The collector also
emits polarized effect bounds for the lambda/body. These are actual F5
constraints, not the structural-shadow equations above. The source semantics
selects a Pure introduction, but the current polarized representation alone
does not identify this fact with the two-child structural equality package.
Thus the record-free constructor inventory is established for both the
source shadow and the current term algebra, while **application of Theorem S
to actual production constraint generation remains unproved** because its
input relation and coupled effect ports have not been bridged.

For the exact source `id x = x`, the two sides currently visible are:

| Layer | Generated interface |
|---|---|
| Typed source core §§6/21 | `Value(Fun(Value(A), Comp(empty,A)))`; Pure introduction, Value entry |
| HIR collector / F5 admission | `Function(negative parameter, EmptyEffect, positive body-effect, positive result) <: definition root`; body and lambda effect components each receive polarized bottom/empty bounds |

The **value-port projection** does line up in this case. The lambda recipe
uses the same fresh parameter ordinal for its negative argument and positive
result endpoints. F5d generalizes that shared component once; the existing
identity-scheme assertion checks one quantifier and that both Function value
ports name it. The typed-core derivation likewise uses the same `A` for the
Value-entry parameter and returned name. This closes the value endpoint
correspondence for the identity example only. It says nothing about denotation
of the effect ports, conservative bound slack, callback views, or
`D_checked`/`P_actual` inclusion.

The effect evidence has a precise phase boundary in current code. Before
generalization, `emit_lambda` gives the identity body-effect component both
polarized bounds, and `admit_lambda_fact` places that component in the
Function's positive result-effect port. `finish` reports the lambda and body
effect projections as `SolvedEffect::Empty` when those two bounds are present.
But F5c's generalization summary nodes retain only Function argument/result;
scheme materialization later inserts the canonical negative `Empty` and
positive `Bottom` effect endpoints. This is an observed representation
transformation, not a successor meaning for either endpoint. The source-owned
effect evidence is not discarded from the solved artifact: `SolvedModule`
retains the `ConstraintStore`, whose facts, provenance, and term view still
expose the original Function node, its result-effect child, and the
body/lambda effect constraints after `finish`. For this identity path, existing
store evidence retains occurrence linkage; a parallel carrier is not
justified. What remains open is the semantic theorem that interprets this
linked evidence as the source Function view and proves full-bound transport.
The closed scheme alone does not carry that occurrence identity.

### Local source-to-projection lemma for the current lambda fragment

**Lemma.** For every complete parameterized binding admitted by the current
lowerer, the source body result has a `Value` interface and its generated F4
effect projection is `Empty`. This is not a theorem about the Function
scheme's complete effect-port denotation.

The source premise is checkable directly on HIR: a complete lambda body is an
integer, a resolved module name, or that lambda's resolved parameter name.
The typed-core rules give `Result(Value(A)) = Comp(empty,A)` in each case. For
integer/module-name bodies, `emit_integer` or `emit_resolved_binding_name`
emits the body's effect lower/upper facts. For parameter-name bodies,
`emit_lambda` emits those same two facts for its `body_effect_component`.
The lambda effect row receives the pair as well. Therefore both body and
lambda rows have

```text
EffectBottomPositive <: row <: EmptyEffectNegative
```

and `finish` reports `SolvedEffect::Empty` for each row with those recorded
bounds. In the parameter-name case,
`admit_lambda_fact` places that exact body row in the Function's positive
result-effect child. The facts and occurrence provenance remain available
through `SolvedModule::store` after finalization.

This closes a source-generation correspondence from `Result(Value(A))` to
the current local effect **projection** over this HIR fragment. It does not
identify `EffectBottomPositive` with an empty row, nor infer that the closed
scheme's positive `Bottom` port means empty. Scheme generalization still
records only canonical polarity endpoints; the denotational relation from
the retained effect facts to a role-indexed source Function bound, and the
callback full-bound clauses, remain open.

For `id x = x`, the evidence identity itself is also pinned without an added
carrier. `emit_lambda` allocates the body's effect component once and records
its lower/upper facts at the body occurrence. `LambdaRecipe` stores that
component position. `admit_lambda_fact` retrieves the same live component
ordinal and uses it as the positive Function result-effect child. The body
facts and Function fact retain distinct source occurrence/slot identities in
`ConstraintStore::provenance`; their common term endpoint is the link. The
existing `f5d_identity_lambda_admits_exact_effect_and_function_facts` test
checks those source slots, shared value parameter/result ordinal, Function
shape, and post-finish store retention. This closes only the identity
occurrence-link construction, not the semantic interpretation of that link.

This is the smallest concrete bridge obligation: derive, from the user-selected
Pure introduction and the intended meaning of the polarized row constraints,
that the F5 endpoint is an adequate presentation of the source interface,
including its effect evidence and full bound. The Oracle materialization of
polarized bounds cannot be used as that derivation, and the structural
shadow's erasure of effect ports does not discharge it. The source endpoint
and F5 endpoint remain different complete objects until this correspondence
is proved.

Relevant source locations: `crates/yu-hir/src/module.rs` (`ResolvedExpr`,
`lower_module`, `lower_body`, `lower_simple_chain`) and
`crates/yu-solver/src/lib.rs` (`emit_lambda`, `admit_lambda_fact`,
`emit_resolved_binding_name`, `finish`, `SolvedModule::store`, and
`finalize_generalization_draft_raw`),
`crates/yu-solver/src/f5c_generalization.rs` (`F5cSummaryNodeKind` and
materialization), and `crates/yu-solver/src/term.rs` (`TermView` / `TermNode`).
No compiler code or tests changed.
