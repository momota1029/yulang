# R188 — direct App case stopped at the original ViewLogic domain

Outcome: **BLOCKED_AT_EXACT_LAW**. Revision 1, author
`/root/r188_app_soundness` (`prover`). This is an unreviewed mathematical
boundary report, not a conditional soundness theorem. Original parent
premises discharged: **0**. Source under-specification, semantic impossibility
and a counterexample are all **unestablished**.

## Original parent and attempted application

The unchanged parent is
`YulangClosure.SourceProblem.InferenceSoundness`,
`notes/theory/lean/YulangClosure/Contracts.lean:128–130`:

```text
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a.
```

The assigned induction case is the original unannotated
`s = App_q(f,arg)` under its original scope `x`, generated object `d`,
satisfying assignment `a`, telescope `Δ` and legitimate child IHs at the same
environment `η`. Neither child may choose another assignment, provider,
world or shared witness. R187 supplies a representation prefix, not a
completed concrete instance of `generates` and `solves`.

Unfolding the actual source target gives
`OriginalSourceGeneration.sourceRules:111–123`:

```text
existsE b_q (
  rule App q Γ
    [descriptorFormation; wholeArgumentCompatibility;
     completeCallCertificate; sourceCallIncidence; callableImage;
     roleAndInitialCallOrigin only if singletonFormalCall Γ f arg;
     CheckValue(returnedValue(f), descriptor(q));
     CheckComputation(callableImage(q), synthesis(q))]
    [sourceRules Γ f; sourceRules Γ arg]),
b_q = ⟨q, .viewLogic, 0⟩.
```

This display records the source target; it does not define inference solving
as satisfaction of that target. The R187 attempted generation equation has
the same outer ViewLogic binder and a conjunction with both child objects
at that scope (`R187:95–109`). Its `Exists` interpretation ranges over an
independently defined binder domain (`R187:70–84`). That interpretation
cannot yet provide the first source constructor premise below.

## First unavailable definition and its required law

Let `V` denote the intended independent semantic data, `E : Environment V`
the original environment for the unchanged assignment/telescope, and
`k : Kernel V` the original local source interpretation. These are names
for the correspondence that must be constructed, not newly assumed inputs
to an asserted theorem.

The first missing construction is the independent domain and original
readout of this actual binder:

```text
D_q(E,Δ) := ⟦ViewLogic(C,q,σ,Δ)⟧_E = ?
decode_q : (E : Environment V) → D_q(E,Δ) → ScopedValue V = ?
```

Its required original-source identification has the following exact type
(the minimal forward direction needed for this induction case):

```text
∀ (E : Environment V) (z : D_q(E,Δ)),
  k.admitted E ⟨q, .viewLogic, 0⟩ (decode_q E z).
```

Here `z` must be the witness of this very binder in the one satisfying
assignment `a`; `decode_q E z` must retain that witness's original dependency
telescope and source occurrence. Choosing another admitted witness is not
this correspondence. Writing `D_q` as the set defined by the desired
admission, or assuming the displayed law, would not construct its independent
meaning. Neither is done here.

The consuming source constructor is exactly
`OriginalSourceGeneration.lean:751–754`, `Judgment.existsE`:

```text
(value : ScopedValue V)
(admitted : k.admitted E b_q value)
(proof : Judgment k (E.extend b_q value) body)
→ Judgment k E (.existsE b_q body).
```

The declaration of the required relation is `Kernel.admitted` at line 672.
The source formula's existential clause at lines 847–848 also explicitly
requires this admission; it does not derive it. Reusing `Build` satisfaction
would import the missing source premise and is excluded by R188.

The already pinned source-Generalize construction §3.3, lines 234 and
242–253, fixes ViewLogic classification, introduction, frame sharing and
placement below description dependencies and above challenges. It supplies
no concrete independent `D_q`/`decode_q` equation establishing the displayed
law. Its §5.2, lines 556–563, requires independently fixed binder domains.
R187 lines 76–81 preserve that requirement instead of supplying this domain.

Thus even when exposing R187's existential connective and retaining the
legitimate child IHs, reconstruction cannot introduce the outer original
`Judgment.existsE`. No App local atom or checking goal is counted as derived.
This is the first unavailable law in direct source-constructor order. It is
a formalization boundary in the inspected inputs, not a refutation of the
original source rule. Luna confirmed this exact stopping point in the current
assignment message; no additional source owner was admitted or read afterward.

## Preserved obligations and prior work

The original `singletonFormalCall` test at source-generation lines 63–73
remains restricted to the actual unannotated Name/Name, one-use Value formal
case. Written annotation still adds its final formation and direct boundary
through `annotated:35–43`; it does not replace the synthesis endpoint. Neither
path is discharged or removed.

R187's graph/connective prefix and source-scope retention are reused only
for the attempted representation. Its incomplete model is not promoted to
an actual emitted generator or solved constraint relation. The original
complete-Call definition §2 retains actual callee Bind, returned receiver,
current configuration and all independent complete alternatives; §3 retains
independent C0. The source-interface definition §§2–4 constructs incidence
while retaining primitive typing, contextual hole/world binding and phase/
dispatch contracts. None supplies the earlier ViewLogic domain/readout law.
No C0 assumption or IF-to-admission inference is used.

No later complete Call, effect-permission, provider, observation, foreign-arm
or checking obligation is simplified to bypass this stop. Accumulation,
propagation, levels, extrusion, qualifying intrusion and generalization keep
their accepted meanings. No production or native correspondence evidence is
claimed.

At the parent's App branch, the exact intended application would be the
assigned `AppCase(App_q(f,arg),x,q,f,arg,d,a,η)` to the parent hypotheses and
both legitimate IHs. That application remains unavailable at `existsE`'s
admission premise. No witness `e` and no `sameScoped` proof have been produced.
The parent, other constructors, source coverage, principality and termination
remain open.

## Checks, resources and next boundary

Checks consisted of SHA-256 authentication and bounded reads of admitted
mathematical authorities. No Lean/checker/build/test/Rust/Cargo/environment/
cache/scratch/Git operation, executable probe or descendant launch occurred.
There is no checked theorem type or axiom audit; the displayed types identify
missing evidence only. Fresh independent review belongs to Luna.

The grant was 1800 seconds, one CPU, with no extension. Exact elapsed time,
CPU and peak memory were not instrumented and are UNKNOWN. Requested and
observed effective model/effort are UNKNOWN; no model-switch claim is made.

Mutual TODO `R188-VIEWLOGIC-DOMAIN-1`: Luna owns any next admission. Required
evidence is the independently defined original ViewLogic domain and readout,
with the same-assignment identification consumed by `Kernel.admitted` /
`Judgment.existsE`. Falsifier for a proposed completion: it selects a different
witness/telescope, defines the domain by source success, assumes complete
admission, or leaves the original readout equation unproved. This TODO grants
no new dependency, lease or implementation authority. There is no further
in-envelope step after this exact-law stop.

The complete write set is this note and the single assigned inbox. Dependency
and artifact hashes are frozen in that inbox. No scratch paths or descendants
exist. After the inbox is frozen, writes stop.
