# R216 — source-resolved annotation equations

Status: **STOP AT THE SOURCE-DATA EQUATION; model incomplete.** The original
soundness claim and supported source domain are unchanged. This note records
the concrete equation interface and identifies the first missing owner. It
does not claim an annotation theorem or any parent-premise reduction.

## Original parent and exact use site

`Contracts.SourceProblem.InferenceSoundness` is still

```lean
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

For Lambda, `OriginalSourceGeneration.sourceRules` extends the original
context with the original formal name, owner site, `formal.annotation`, and
Value/Computation entry. It emits the original atom
`sourceFormalRole formal.site formalContext`, carrying the same annotation ID
and entry (`OriginalSourceGeneration.lean:130–141`). Any bridge must show that
the same generated problem and satisfying assignment establish this atom,
then retain its full scope in the original witness.

R215's candidate note SHA-256 is
`c3044d07f4290b019e2a181b032e314501ddc1bc9e37e9d8725cec3898973866`.
R215's independent review accepted it only as incomplete. The root/package
counts remain 0/4 and 0/5.

## Concrete source-data equation required

The intended separation has three explicit inputs:

```text
source signature Σ : fixed declarations, independent of a solver assignment
original use u       : (annotation id α, formal owner q, lexical/type scope Γ,
                        entry mode m, original occurrence)
solution ρ           : assignments to generated Simple-sub value/effect vars
```

The declaration lookup must be source-owned and identity preserving:

```text
resolve(Σ, α) = some (α, owner, Γdecl, complete annotation A)
```

At the original formal use, generation and source typing must read that same
`A`:

```text
generate(Σ, u) = (C_A, role_A)
sourceFormalRole(Σ, u) = role_A
```

`C_A` must contain constructor-directed value links and effect-variable links
for each original nested path. A candidate resolved node records its exact
source constructor and ordered children; each child keeps declaration-derived
variance. Full path polarity is the composition of the original constructor
variances. For an effect row at `(α,q,Γ,path,position)`, concrete members at a
negative position classify as **permission**, positive members as **allowance**,
and symbolic row variables remain linked to their same generated effect
variables. The source-selected handler filters only actual matching inflow to
form residual. These are four separate objects: permission, allowance,
inflow and residual.

The required independent readout is:

```text
denote(ρ, C_A, path) = (the value/effect terms assigned at the generated path)
```

It may inspect `ρ` for solver variables only. It may not read `Σ`, choose an
annotation declaration, recover an owner/scope from a graph node, or supply a
source atom as a premise. The same `denote` must be used by generation's
soundness argument and by source typing. For fixed `Σ` and `u`, changing `ρ`
cannot change `α`, owner, scope, entry or the annotation tree.

Those equations define a concrete target and a falsifiable boundary. They are
not yet definitions of the original language: the current source model does not
contain `Σ`, `resolve`, `A`, `C_A`, or `denote`. In particular, choosing an
inequality direction or equating an annotated effect row to actual inflow would
add semantics absent from the cited authority. The selected hygiene policy
does not make either choice: permission allows local subtraction, allowance
allows a concrete effect, and neither creates an arrival.

## Pinned source facts

All hashes below were read during R216.

```text
3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1  notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean
126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef  notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean
feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef  notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean
a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6  notes/theory/lean/YulangClosure/SimpleSubConstraintSyntax.lean
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240  notes/theory/2026-10-08-source-generalize-definition-and-proof.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38  notes/design/2026-10-08-source-generalize-definition.md
a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8  notes/design/2026-11-02-literal-l1-adoption.md
409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f  crates/yu-hir/src/module/source_annotation.rs
2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166  docs/yulang-source-type-safety-ja.tex
e9027e317deb5cd5c34cc3892f332a06910a6ff93f1890a82e59faf31d643283  notes/theory/2026-10-26-original-source-generation-construction.md
```

The source-to-Lean obstruction is exact:

1. `OriginalSourceSyntax.Annotation` is only `Nat` (`:23`). The `Source`
   constructor stores that ID; it has no resolved declaration or annotation
   tree. The original generator preserves it but does not look it up.
2. `OriginalSourceGeneration.Kernel` (`:670+`) parameterizes `atom`,
   `admitted`, primitive checks and structural checks. `Satisfies` consumes
   those meanings; reconstruction does not define them. The original
   interpretation's `SourceAssignment` has event/endpoint/binding fields but
   no annotation declaration environment. `literalKernel` deliberately
   changes only the literal atom and preserves the other kernel fields
   (`OriginalSourceInterpretation.lean:830–855`).
3. `SimpleSub.Term` has value/effect variables, opaque `atom Nat`, structural
   Function/record/tuple/variant constructors, and `Constraint` stores only
   kind/lower/upper. It has no source annotation ID, declaration owner, scope,
   path, row position, handler or source occurrence. `Store.Satisfied` proves
   only structural comparisons.
4. The Rust `SourceAnnotationType` provides useful implementation grammar
   (effects plus Unit/Int/Bool/Str/Variable/Hole/Tuple/Function), keyed by an
   owner and source position. Its effect rows contain resolved source effect
   family IDs and symbolic names. The original source-generation construction
   note states that its raw Lean grammar is not a Lean copy of Rust
   `LocalSource`, and that the relation to Rust carriers, declaration tables,
   scopes and component registration is unproved. Neither the Rust record nor
   that raw grammar proves coverage of every original `supported` source form.
   Rust data cannot silently become the missing mathematical definition.
5. R208's `StaticAnnotationConstraintInterpretation` does not fill this gap:
   it retains a caller-supplied arbitrary tree and coordinates in `Solves`;
   its reflection theorem derives the newly defined `SourceFormalRole`, not
   the original `Kernel.atom` from store satisfaction.

The first missing equation owner is therefore **the original source/signature
elaboration and its annotation-formation law**, before Simple-sub solving:

```text
(raw source annotation occurrence, original signature/scope)
    ↦ (resolved declaration identity, full annotation tree, entry mode)
```

That owner must state full constructor coverage, declaration/type-variable
scope, nominal/effect identity (including any type arguments), and original
annotation formation/compatibility direction. The effect policy fixes hygiene
behavior after that data exists but does not supply this schema or relation.
Source-Generalize authorizes legitimate missing definitions and keeps these
as explicit local laws; it explicitly does not define an unprovided annotation
law, narrow unsupported extensions, or treat Rust recognition as legality.
No current pinned owner supplies this equation. This is an unresolved model
dependency, not proof of semantic underdetermination.

## Parent application and remaining gate

Because the required original source equation has no pinned definition, R216
constructs no `ResolvedAnnotation` instance, `Kernel.atom` interpretation,
Lean theorem or `LocalLaws` instance. The Lambda `sourceFormalRole` premise of
the original `InferenceSoundness` induction remains. No roots or packages
close; parent-premise delta is zero. App admission, Catch, principality,
termination and Rust correspondence remain independent/open.

The discriminating next step is to locate or define, under the existing source
authority, the original signature elaboration relation above; then freeze its
full constructor equations and prove `generate`/`denote` soundness for the same
`Σ,u,ρ` before applying it to the original atom. A future theorem must retain
all original Lambda binders and Entry modes and must not turn permission into
inflow or residual.

No new cache was needed in R216. The user explicitly authorized cache creation
for this continuing goal; the existing pinned project cache remains permitted.
No Lean, Rust, Cargo or test command ran. No theorem or axiom audit exists.
