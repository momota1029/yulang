# R199 — abstract Yulang inference model reconstruction

Date: 2026-11-02
Status: **MODEL-INCOMPLETE; primary construction frozen for independent review**.
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
