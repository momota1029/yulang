# R199 — abstract Yulang inference model reconstruction

Date: 2026-11-02
Status: **MODEL-INCOMPLETE; BLOCKED_AT_ORIGINAL_LITERAL_RULE; R206 candidate unadopted; no semantic adoption**.
Parent baseline: `77bb8be466bbaa6cc9d7bd4587cf5975524f3ead`.
No semantic adoption, theorem closure, Rust correspondence, or production authority.

## 1. Intended model and unchanged parent

The objective is the mathematical soundness of Yulang's source-directed
Simple-sub inference, followed by separate principality and termination
proofs. Rust implementation correspondence is a later theorem. The original
source domain, accepted entry modes, Call/effect behavior, scopes and witness
quantifiers remain fixed.

The first root remains `YulangClosure.SourceProblem.InferenceSoundness`
(`Contracts.lean:128–130`):

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

`solves` must interpret independently generated constraints. It cannot assume
`sourceJudgment`, the desired original source-admission conclusion,
reconstruction, or the theorem being proved. It may interpret independently
defined local declaration, domain, and admission constraints that are part of
the selected source semantics; those equations must not encode the desired
source judgment. The result must preserve the same source, scope, assignment
and one witness.
`PrincipalCoverage` and `InferenceTermination` are distinct roots;
`PrincipalCoverage → SourceScopedCoverage` is a direct corollary only after the
principal root and its unchanged model are proved and the corollary is applied.

## 2. Existing model ingredients and their authority limits

### 2.1 Raw source data and candidate source-rule skeleton

`OriginalSourceSyntax.Source` is the raw resolved syntax. It includes all 13
expression, 11 pattern and 3 statement constructors, plus ordered containers.
It carries source sites, resolved names/declarations, the written annotation
ID, outer Value/Computation entry bit, literal payloads, pattern merge triples
and original arm order. Those fields are source data, not proofs.

`OriginalSourceGeneration.sourceRules` recursively constructs a candidate
finite local-rule tree from that raw syntax. Authority selects the SG
construction and its separation between source rules and inference, while
retaining genuine L1–L5 local premises. The Lean module and the source
construction document call this a candidate formalization; they do not certify
every atom/operand equation as the concrete original source semantics. The
table below records that candidate skeleton only. Its concrete semantic
validation remains open (the exact tree constructors and operands are in
`2026-10-26-original-source-generation-construction.md` §§3–4):

| Source form | Original local rule shape retained |
| --- | --- |
| Literal | `literalDeclaration(originalPayload)` |
| Primitive | `primitiveDeclarationInstance(originalDeclaration)` |
| Name | `resolvedSameBinding ∧ computedFetchOnce`; Published/Family adds one `exactWholeInstance` |
| App | One ViewLogic frame; descriptor formation, whole inert argument compatibility, complete Call certificate, Call incidence, callable image, returned-value check and invocation-computation check; both child derivations; guarded singleton-role premise only for the original one-use unannotated formal case |
| RefSet | Invariant reference protocol, result relation, value-to-reference-content boundary; ordered reference/value derivations under the reference return/pending suffix |
| Lambda | Capture/closure formation; original ViewLogic and formal Description; universally admitted invocation; receipt and source-selected entry; pattern/body; Shared evidence before body; Value entry's actual Force/Return/rebind suffix; retained Computation entry; body consumer and computation check |
| Tuple | Ordered child occurrences and tuple formation |
| Record | Ordered field/spread occurrences and visible-field updates |
| PolyVariant | Original tag, payload occurrences and exact arity |
| Select | Retained selection choice, qualified child and whole-instance obligations in one ViewLogic frame |
| Case | Ordered attempts, pattern/guard/body derivations, branch join and direct result boundaries |
| Catch | Original arm order, same operation instance, shallow packet/residual/latent obligations, rigid payload/continuation telescope, branch join |
| Block | Source-ordered statements, binding owners, final root and predecessor/rebind scopes |

The eleven pattern equations are: Wild introduces no binder; Literal preserves
payload and input comparison; Var binds the actual lexical occurrence; Tuple
preserves arity/order; List preserves prefix/rest/suffix; Record preserves
field visibility, spread and default-before-binding; PolyVariant preserves tag
and arity; Con preserves nominal declaration and invariant type arguments; Ref
compares an existing definition; As aliases the same input; Or preserves both
ordered attempts and the original merge map. The three statement equations are
Let (including simultaneous recursive members and one-shot initializer
anchors), Expr (ordered evaluation/discard), and Module (original linking
relation plus ordered body).

These are source-rule equations, not yet Simple-sub generation equations.
`Build` compiles that rule tree to the scoped `Formula`, and `Satisfies`
interprets it under a supplied `Kernel`. The checked equivalence
`source_reconstruction` proves `Satisfies ↔ SourceJudgment` for that same
supplied kernel. It does not determine the original kernel or connect it to
Simple-sub solutions.

### 2.2 Structural Simple-sub layer

`SimpleSubConstraintSyntax.Term` contains distinct Value and Effect kinds;
variables, atoms, bottom/top, union/intersection, four-port Function,
record/tuple/variant constructors and their order/labels/optional bits. Its
structural relation `Sub` is independent of source typing. Function comparison
uses variance `(-,-,+,+)`, including argument and result effect ports.
`Constraint.Satisfied ρ c` is exactly
`Sub (c.lower.subst ρ) (c.upper.subst ρ)`; a Store solution satisfies every
stored comparison.

This structural `Sub` and existing lattice/store theorems do not define
complete Function admission, contextual effects, literal/primitive meanings,
Call, or finite checking. An Effect-kind atom identity is not itself a
permission, operation witness, owner, scope, or effect relation.

### 2.3 Selected annotation/effect meaning

The existing user-approved annotation policy is part of the model, not a new
choice:

- Compose polarity through every nested Function. Function arguments and
  argument effects flip polarity; results and result effects retain it.
- A concrete effect `E` at a contravariant annotated position grants local
  permission to subtract `E` from effect flowing through that position. It is
  not a closed input upper bound: `[signal, write]` remains admissible at a
  `[signal]` permission position, and handling `signal` leaves `write` outward.
- A concrete `E` at a covariant annotated position is allowed there; allowance
  alone does not assert that `E` flows there.
- Type variables are ignored when collecting concrete annotation effects, but
  their symbolic connections and later concrete lower-bound checks remain.
- The annotation's resolved identity, concrete effect identities/type
  arguments, paths, symbolic dependencies, original owner and scope remain
  attached. Permission, actual inflow and subtraction residual are distinct.
- Formal Value versus retained Computation entry comes from the outer source
  annotation before body typing; annotation and entry consistency remains a
  local source rule, not metadata assumed correct.

Existing transport/lifetime and owner results retain their exact hypotheses.
They can be used after this model constructs the authentic annotation profile;
they do not themselves construct the profile or prove whole-language effect
hygiene.

## 3. The intended independent model interface

The candidate model has one fixed resolved semantic signature `Σ`, with
independently meaningful entries for source annotations, literals, primitive
and constructor declarations, source checking, complete Call and contextual
effects. It must not be a map from numeric IDs to arbitrary predicates. Each
entry has an explicit domain, telescope, interpretation and relation to the
original source declaration. The same `Σ` is consumed by:

1. the actual mathematical constraint generator;
2. the independent interpretation of a generated constraint and its solution;
3. the original syntax-directed source judgment.

The intended abstract problem has separate components:

```text
SourceJudgmentΣ(s, x, e)       -- original declarative source derivation
GenerateΣ(s, x) = d            -- actual Simple-sub formula/store and scopes
SolvesΣ(d, a)                  -- structural comparisons plus independent local
                                 -- declaration/effect/checking interpretation
sameScopedΣ(s, x, e, a)        -- same complete scope and single shared witness
```

The component equations have not been fully constructed. In particular,
`Build`/`Satisfies` above cannot be renamed to `GenerateΣ`/`SolvesΣ`: that would
skip the Simple-sub correspondence and would leave the concrete meaning inside
the supplied `Kernel`.

## 4. Soundness composition and exact open equations

The intended proof of the unchanged root is constructor induction:

```text
supported s
  GenerateΣ(s,x)=d
  SolvesΣ(d,a)
  ─────────────────────────────────────────────────────────────
  derive each original constructor premise from d under that same a
  reconstruct SourceJudgmentΣ(s,x,e) and sameScopedΣ(s,x,e,a)
```

For a constructor `c`, the required local theorem is not a wrapper around
source reconstruction. It must have the form

```text
GeneratedClauseΣ(c, inputs, outputs, scopes) = d_c
SolvesΣ(d_c, a)
  → OriginalLocalPremisesΣ(c, inputs, outputs, scopes, a)
```

and the source induction must consume those premises while preserving the same
assignment and scope. The following decisive model equations remain unfilled:

| Equation | Exact status and effect on parent |
| --- | --- |
| `interpretAnnotationΣ(annotationID, original lexical/type scope)` | Must recover the written typed tree, positions, composed Function polarities, concrete effects/type arguments, paths, symbolic dependencies and outer entry consistency. The Lean `Formal.annotation` is only `Option Nat`; no direct interpretation is established by R197/R198. Lambda's `sourceFormalRole` remains unproved. |
| `interpretLiteralΣ(payload, row)` and literal generator clause | Must fix the same payload, ground descriptor, value, root and event; generated constraints plus independent readout must imply the original literal declaration relation. R196 generation rewrite alone does not apply this equation to the parent. |
| `interpretPrimitiveΣ(declaration, type/effect telescope)` | Must provide the actual fixed primitive signature and its independent local law, including effects; not derivable from the constructor ID alone. |
| `interpretCheckΣ(goal, a)` | Must interpret Value/Computation/Domain/Observation/Equality goals as the original finite declarative checking judgments and conversions, with their original scopes. The `Kernel` field currently receives this meaning. |
| `interpretCallΣ(full call tuple, a)` | Must retain the same provider, argument carrier, current world, receipt, consumer, event, contextual effects and complete observation. The App formula states where these clauses occur but does not supply their independent domain/admission/readout equations. |
| `interpretEffectΣ(position, inflow, residual, permission, a)` | Must realize the selected polarity-sensitive permission policy above while retaining symbolic variables, exact owner/position and same-operation witness. Structural effect `Sub` does not provide this relation. |
| `interpretPatternΣ` and source extension | Must connect each pattern constructor's actual input and introduced environment to generation under the original resolved binder identities, including default order, Ref, and Or merge triples. |
| `interpretStatementΣ` and publication | Must connect ordered Let/Module roots, simultaneous recursive component introduction, one-shot anchors, Shared references and final publication to generated constraints without making publication a typing premise. |
| `GenerateΣ` for all forms and phase transitions | Must give actual equations for generation, accumulation, propagation, extrusion, intrusion, and generalization. Existing `sourceRules` is a separate local rule program; no full translation to the actual abstract solver is established. |
| `sameScopedΣ` and model instance | Must instantiate the original parent data and return one witness for the *same* `s/x/a`; a generated local proof object or a later Rust trace cannot replace it. |

The rows are construction obligations, not proposed axioms or claims that the
language is underdetermined. Current evidence does not demonstrate competing
accepted meanings, so it does not justify a new user semantic vote. If a
candidate equation contradicts an approved meaning, narrows accepted source,
changes an admission challenge, or duplicates a witness, stop that equation
and return the exact conflict for adjudication.

### 4.1 Literal equation construction attempt (R200)

The source payloads have a lossless bridge to `PaperTypes.Literal`: the eight
constructors carry the same payload types (`Bool`, `Int`, `Nat`, `String`, and
`List Nat`) in `OriginalSourceSyntax.Literal` and `PaperExecutionSyntax.Literal`.
The paper typing definition `PaperTypes.literalType` assigns each constructor
its corresponding base type, and the `PaperValueTyped.literal` rule types that
value without declaration, graph, or environment premises. This gives a
concrete candidate for the *type/value* projection of a literal rule while
preserving every original payload. It is stronger evidence than the `CoreSyntax`
bridge, whose `UInt64`, `List UInt8`, and byte-list path carriers cannot encode
all original payloads.

It still does not supply the required `LiteralAtom` equation. The source
interpretation's `LiteralDeclaration` relates a raw literal to a full row of
descriptor, value, root, and event; `LiteralAtom` also requires the descriptor
to be ground and the row to satisfy the independent ground predicate. Neither
`PaperTypes.literalType` nor `PaperValueTyped.literal` chooses those original
row carriers, defines the source `Root`/`Event`, gives the literal's contextual
effect row, or proves that a Simple-sub solution reads back that same row.
The paper execution typing relation is explicitly not identified with the
original effectful source interpretation in `OriginalSourceInterpretation`.

Therefore the following equation is supported only as a candidate local type
rule:

```text
sourceLiteralType(l) := PaperTypes.literalType (toPaperLiteral(l))
sourceLiteralValue(l) := PaperTypes.Value.literal (toPaperLiteral(l))
PaperValueTyped.literal : sourceLiteralValue(l) : sourceLiteralType(l)
```

The immediate `LiteralAtom` bridge remains open:

```text
IndependentSolutions(GenerateLiteral(site, l), a)
  → LiteralDeclaration l (descriptor(a, site), value(a, site),
                           root(a, site), event(a))
    ∧ valueForm(descriptor(a, site)) = ground
    ∧ ground(row(a, site))
```

That is only the literal declaration/readout atom. The full local source rule
also needs its actual Return construction and contextual effect equation, with
the same event, scope, and literal occurrence. Those obligations remain in
`interpretEffectΣ` and the source constructor/phase equations above; the paper
typing rule does not discharge them.

Filling the gap requires a source-faithful construction of the complete
descriptor/value/root/event and effect meaning, together with an actual
Simple-sub generator/readout equation. Supplying `LiteralDeclaration` as an
arbitrary parameter, interpreting `Solves` through `Kernel.atom`, or deriving
the row from the paper typing proof would leave that same premise assumed.
This construction attempt changes no source rule and closes no parent premise.

### 4.2 R204 sufficient direction into the selected SG literal rule

The soundness induction needs one direction only: the canonical value/type
introduction must be usable in the selected original literal source rule. It
does not need to characterize every legal literal checking alternative or
prove equivalence between paper typing and the whole source relation.

For the same raw occurrence `q`, original scope `xi`, event/world and row
`r = ⟨descriptor, value, root, event⟩`, the sufficient source-rule derivation
has these independently established parts:

1. **Static value/type premise.** The R203 `PaperValueTyped.literal` derivation
for the payload-preserving literal value at `sourceLiteralType(l)`. This gives
only the local base-type projection.
2. **L1 declaration and whole local typing premise.** The actual selected
literal declaration for `(l,r)`, its ground descriptor/value interpretation,
and every original primitive guard and permitted checking alternative needed
for this occurrence. No field is obtained from the paper derivation alone.
3. **L2 Return and contextual-effect premise.** The actual original Return
construction for that same value, event and world. The literal contributes no
immediate performed operation, while the enclosing judgment retains the
original permission, actual inflow, residual and Call/effect obligations.
4. **One-scope premise.** These facts use the source's original `xi`, occurrence
and correlated witness; the SG rule and eventual parent conclusion may not
choose a second row, event or witness.

When these premises are proved, the selected SG Literal constructor supplies
one source derivation at the original scope. Other source checking/declaration
alternatives remain available. The sufficient direction is not permission to
replace their relation, and no intrinsic-empty effect fact resets contextual
effects.

The parent-applicable theorem target is therefore **not**
`PaperValueTyped.literal → SG Literal`. It is the original solver-to-source
implication for this generated case: from the actual literal constraints and
an independently satisfying assignment, construct the same-occurrence L1
declaration/ground row and L2 Return/contextual-effect evidence above, then
consume those facts in the unchanged `InferenceSoundness` literal case to
produce its original source judgment and `sameScoped` witness.

The first concrete missing premise is the following construction/readout
equation, at the same generated `d`, solution `a`, source scope and occurrence:

```text
generates_literal s x d l ∧ solves d a
  → the actual row(descriptor(a,q), value(a,q), root(a,q), event(a))
    satisfies the independently defined L1 literal relation and ground law,
    and the original L2 Return plus contextual-effect law,
    with the same xi and one witness used by sameScoped(s,x,e,a)
```

The generator syntax must not encode `sourceJudgment`, the SG conclusion, or
the target witness as a premise. The independent `Solves` interpretation may
use separately specified `LiteralDeclaration` and `Ground` laws: sharing an
independent primitive meaning between generation and source typing is not
circular by itself. Circularity would arise if solution satisfaction assumed
the desired source judgment or reflection theorem instead of interpreting the
literal constraints independently. No selected source equation presently
derives this implication from an actual generator and independent Simple-sub
solution satisfaction. R194 supplies the symbolic literal atom and R196 proves
its exact `Build` formula; neither defines independent `generates`/`solves`
readout for descriptor, value, root, event, Return and contextual effects.

**R204 stop:** the sufficient direction and exact theorem application are now
fixed as the target; its decisive L1/L2 solver-to-source equation remains
unproved. No parent premise is removed. A proposed original-clause definition
must be reviewed for any change to accepted typings, payload validity,
effects, alternatives or scope before adoption. Do not turn this target into a
conditional theorem by assuming those missing fields.

### 4.3 R205 exact missing primitive interpretation

The existing syntax exposes the original literal clause but does not yet give an independent Simple-sub denotation. `OriginalSourceGeneration.sourceRules` retains the raw literal payload at its original site/context; `Build` compiles this to a local `.literalDeclaration` atom. `CanonicalSourceInferenceModelR196.literal_generated_formula` proves only that symbolic `Build` equation. In `OriginalSourceInterpretation`, `LiteralDeclaration` is an arbitrary supplied relation on `(literal, ValueRow)`, while `LiteralAtom` additionally assumes supplied `valueForm = ground` and `ground`. Those are useful source-boundary fields, not a concrete literal primitive interpretation or structural `Constraint.Satisfied` law.

A genuinely independent Simple-sub clause would require a fixed signature `Σ` containing a concrete literal-domain interpretation, then equations of this shape:

```text
GenerateLiteralΣ(ξ, q, l) =
  .local (.literalDecl(q, ξ, l, descriptorAt(q), valueAt(q), rootAt(q), event))

InterpretLiteralConstraintΣ(.literalDecl(q, ξ, l, d, v, r, e), a) =
  LiteralMeaningΣ(l, d, v, r, e)

ReadLiteralΣ(q, l, a) =
  (descriptorAt(a,q), valueAt(a,q), rootAt(a,q), eventAt(a))
```

These are a shape only, not the required equations: `LiteralMeaningΣ` is precisely the missing definition, and the current structural constraint grammar has no `.literalDecl` atom or independently selected interpretation for it. Defining `LiteralMeaningΣ` as `LiteralDeclaration`, `Ground`, or the existing source `Kernel.atom` would merely carry an unspecified relation into the solver interface. Defining it as `sourceJudgment` or the desired SG result would be circular. The actual source-typing rule and solution denotation need one independently fixed primitive meaning.

The selected materials currently leave two materially different candidate completions:

1. **Intrinsic table candidate (R203 projection).** Use the eight payload-preserving `PaperTypes.literalType` equations and `PaperValueTyped.literal` as the canonical source introduction, then define their descriptor/value/root embedding and ground/Return laws. This fixes one intrinsic base interface per payload constructor. It would reject any original declaration alternative assigning an incompatible interface unless that alternative is shown to be a checking rule over the same fixed interface. R203 explicitly leaves this as a candidate, not the selected SG literal relation.
2. **Declaration-driven primitive candidate (selected SG shape).** Fix an explicit original literal declaration table over each payload and its complete descriptor/value/root/event row, including all permitted local checking alternatives, guards, ground law, and Return/effect/world obligations; generate a corresponding local constraint whose independent denotation is exactly that table. This can preserve multiple original alternatives, but the table itself and its constraints remain to be specified and must be shown to be the original language meaning. No selected source presently gives its all-payload equations.

The native literal `0`/`1` Call instances do not fill either whole-language table. No subset-only rule is a candidate, since it would narrow the original source domain. This is an input gap in the authenticated source authorities, not evidence that the language lacks literal semantics. No candidate is adopted here.

**R205 stop:** the independent local literal meaning and corresponding Simple-sub atom must be fixed before actual generation/readout equations or a literal reflection theorem can be written. A user decision is required only if choosing between the intrinsic table and the declaration-driven table changes accepted interfaces or alternatives; the proposal must first receive independent review. Parent delta remains zero.

### 4.4 R206 candidate introduction, corrected by R207

R203 supplies a canonical **static value/type introduction candidate** for each raw literal payload. With `p(l)` its payload-preserving map, `τ(l) := PaperTypes.literalType(p(l))`, and `v(l) := PaperTypes.Value.literal(p(l))`, the eight base projections remain `unit ↦ Unit`, `bool ↦ Bool`, `int ↦ Int`, `floatBits ↦ Float`, `string ↦ String`, `bytes ↦ Bytes`, `path ↦ Path`, `character ↦ Char`. This is the kernel-checked `PaperValueTyped.literal` rule, not yet an instance of the original SG source rule.

For the source boundary, retain the original root coordinate `r`, occurrence `q`, scope `xi`, ambient event `e0`, and correlated witness strategy `omega` as supplied by the original source derivation:

```text
LitRow(q,l,r,e0) =
  ⟨ descriptor = Value(τ(l)), value = v(l), root = r, event = e0 ⟩

Return(LitRow(q,l,r,e0)) =
  ⟨ Comp(empty, τ(l)), v(l), r, e0 ⟩
```

The base literal performs no intrinsic operation. Its local performed-effect row is `empty`; surrounding permission, actual inflow, residual, Call effects, guards and future obligations remain in the enclosing source judgment. No fresh root, event, scope, or witness is introduced. Any proof-only checking uses the same value and its original endpoints. An actual selected conversion retains its own `Executed` boundary, distinct source/target rows and event/effect transport, all linked to the same literal occurrence and outer witness.

This is intentionally only a **sufficient-direction candidate**. It proposes one base literal introduction followed by any independently admitted source checking/annotation path at its original occurrence. It does not define the complete literal relation or remove its other alternatives. Structural and annotation checks follow the selected Source-Generalize §3.2 rules; a registered method/adapter remains an alternative with its complete original inputs, effects, guard and evidence. An unregistered overload is not ruled out by this candidate, and the hypothetical `int → Number` case establishes no current Yulang behavior.

The required admissibility implication is:

```text
R203 canonical introduction of (l, τ(l), v(l))
  at original (q, r, e0, xi, omega)
→ one authentic selected SG Literal derivation
  at those same original coordinates
```

**R207 exact stop:** the selected SG construction §3.1 requires the actual literal declaration and whole local typed relation, with all conservative alternatives and guards; L1 requires the authentic primitive's independently fixed typed relation, and L2 retains original Return/world/effect obligations. Those authorities do not state that the R203 base introduction satisfies that declaration at root `r`, nor give its ground/value-form and Return law for all eight payloads. The typed-core document is a draft schema `Value(type of literal)`; its full raw-source elaboration is open. The selected native `0` and `1` Call rules are bounded instances. Thus the candidate cannot yet be derived into the original source rule.

Do not replace `r` by a new `LiteralRoot(q)`, and do not assume `sourceJudgment`, `LiteralDeclaration`, `Ground`, or a `Build` leaf proves the missing L1 law. No exhaustive overload policy is needed for soundness; preserve all other original alternatives while seeking one admissible path. The exact blocker is **BLOCKED_AT_ORIGINAL_LITERAL_RULE**: supply or authenticate the original L1 introduction law, or present a concrete changed-rule proposal for review and approval if creating it changes source meaning. Parent delta remains zero.

## 5. Principality and termination remain distinct

For the same fixed model, `PrincipalCoverage` must separately construct a
solving principal assignment and prove every original source derivation
factors through it using the original `instanceOf` ordering. It cannot be
inferred from forward soundness. When proved, the direct corollary to
`SourceScopedCoverage` must be applied and recorded.

Termination requires the actual initial states and all transitions of this
model. A global accessibility proof must account for repeated accumulation and
propagation, type/effect variable allocation, level-aware extrusion,
birth-qualified intrusion/equality, replay/callback behavior and
generalization. Existing local descent results do not yet cover this relation.

## 6. Outcome and falsifier

**Outcome: MODEL-INCOMPLETE.** This document freezes the faithful equations
already supported by the selected source rules, structural Simple-sub core,
and annotation/effect policy, while naming the missing constructor-to-solver
relations. It is not a success for the model gate and activates no Lean proof
packet. The original parent delta remains **0/4 roots; 0/5 packages**.

The falsifier for a future completed model is a supported source form and
original scope for which an independently satisfying generated assignment
fails the original local rule, loses a concrete effect or symbolic dependency,
changes a provider/event/owner, or cannot supply the same shared witness. The
model review must also find all 13/11/3 forms, all selected transitions, and
the full Call/effect telescope.

## 7. Frozen source locators

The following direct inputs were checked at `77bb8be46` before this draft:

```text
Contracts.lean                                 2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e
OriginalSourceSyntax.lean                      3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1
OriginalSourceGeneration.lean                  126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef
OriginalSourceInterpretation.lean              feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef
PaperExecutionSyntax.lean                       d0dc9871c382ca945059167b8b9e05f8f672170208a994f081e29760a207b87d
SimpleSubConstraintSyntax.lean                 a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6
OriginalSourceChecking.lean                     a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6
2026-10-26-original-source-generation-construction.md e9027e317deb5cd5c34cc3892f332a06910a6ff93f1890a82e59faf31d643283
docs/yulang-source-type-safety-ja.tex            2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166
2026-10-11-yulang-inference-top-level-principles.md 7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81
2026-10-10-annotation-effect-hygiene-integration.md a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18
2026-11-01-parent-obligation-reconstruction-r199.md 7c525a98e53a62a370096d85a3b371af5952dae19d8593b4e02cf3a812c3f36e
```

No Rust source, runtime implementation or quarantined path was read for this
mathematical model construction. No build, test, Lean check, new environment,
cache, target or scratch directory was created.
