# R192 — canonical source interpretation boundary

**Outcome: `BOUNDARY_STILL_OPEN`.** This is a bounded source-intake result, not
a semantic impossibility result and not a proof attempt. The original
`InferenceSoundness` proposition remains open, with zero of its four tracked
root obligations closed.

## Parent obligation

The target remains `YulangClosure.SourceProblem.InferenceSoundness`
(`Contracts.lean:128–130`):

```text
∀ s x d a,
  supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

The output derivation must use the *same* solving assignment `a`; source
support, generated problem, quantifiers, scope, and conclusion have not changed.
This intake closes no premise of that theorem.

## Bounded source findings

1. **The source rule fixes the App shape, not its atom meaning.** The source
   type-safety paper's App rule receives a Function derivation, an argument
   derivation, and the complete Call derivation; it evaluates the callee once,
   delays the whole argument, and passes that argument to complete Call. This
   is the induction target's source-rule structure. It does not define the
   independent denotation of generated `descriptorFormation` or `ViewLogic`
   admission.

2. **Generation emits syntax whose interpretation is abstract.**
   `OriginalSourceGeneration.lean:111–123` emits App atoms for
   `descriptorFormation`, `wholeArgumentCompatibility`,
   `completeCallCertificate`, `sourceCallIncidence`, and `callableImage`, plus
   the conditional role/origin atom, the selected `.viewLogic` witness, two
   Checking goals, and both child derivations. `Kernel.atom` and `Kernel.admitted`
   (`:670–679`) are fields of the abstract interpretation interface. The
   reconstruction result is conditional on a supplied Kernel. The syntax file
   enumerates atom kinds and payloads but supplies no source-typing meaning.

3. **Logical admission is still an independent input.**
   `OriginalSourceEnvironment.lean:596–600` retains
   `LocalAdmissions.logical`; `DataAdmitted (.logical kind data)` delegates to
   it. `Judgment.existsE` (`OriginalSourceGeneration.lean:751–754`) requires
   one admitted payload for the selected witness, then the body derivation in
   its extension. It does not require admission of every domain element. The
   missing equation therefore concerns this exact selected witness and its
   original telescope.

4. **The generalization materials state obligations, not the missing
   denotation.** Source-Generalize L1–L5 and §§3.1–3.3 require independently
   fixed primitive relations, ordinary constructor laws including Call,
   local checking/conversion laws, original world/primitive/annotation laws,
   and lifetime laws. They constrain a future construction; they do not give
   the needed descriptor interpretation or admission equation. The source
   contracts design also explicitly leaves `DescMem` independently
   interpreted and says its contract does not select a descriptor meaning or
   admission policy.

The concrete missing boundary is:

```text
⟦descriptorFormation(q,f,arg,vq)⟧(E, Δ, a) = ?
⟦logical ViewLogic admission⟧(E, Δ, a, vq) = ?
```

It must read the selected witness from the *same* solution assignment and
original scope, provide the original formation predicate in the witness's
extended environment, and derive admission of that selected ViewLogic payload.
The relation cannot be defined by `Kernel.atom`, successful typing, successful
constraint solving, or an assumed admission law: each would make the source
induction circular or conditional on the missing fact.

## Parent-dependency effect

The missing meaning blocks the first source-soundness induction step that
requires the generated App constraints to establish original source premises.
After that boundary is supplied, the complete App obligations still include
whole-argument compatibility, complete Call, incidence, callable image,
conditional origin, both Checking goals, the child inductions, and preservation
of `sameScoped` under the same assignment. No one of those obligations is
claimed discharged here. The separate `SourceScopedCoverage`,
`PrincipalCoverage`, and `InferenceTermination` roots remain open too;
implementation correspondence remains a later bridge.

The typed-Union question remains pending and was only checked as a status
locator. This result does not answer it. No material semantic choice was
established by this bounded input set, so no choice was made.

## Scope, evidence, and next admissible action

This result is limited to the ten pinned direct inputs in the R192 contract
(their hashes matched before source reading). It does not claim that no
definition exists elsewhere in the repository or in the wider authority
record. No Rust owner, Lean build, test, cache, environment, scratch output, or
compiler semantics was inspected or changed.

The next useful step is source-authority intake for the independent
`descriptorFormation` definition and its equation to the original formation
judgment, together with the selected-witness logical admission law. Search
must stay on named authoritative owners and preserve the existing source
domain and telescope. If the owner requires a choice among source meanings,
stop at the exact alternatives and route that decision to the question board.
Only after independent review accepts those definitions and readout equations
does a proof lane become useful. It must then apply them to the unchanged
`InferenceSoundness` parent; definition recovery alone closes zero parent
roots.

## Authentication

Contract: `tasks/agent-loop/sprints/canonical-source-interpretation-r192.md`
SHA-256 `f791a73dd535fe1be3237c8a15ec220f9ce232bc38c86db6b492160c2526ceeb`.

Pinned source hashes are recorded in that contract. Outcome SHA-256 is
recorded in `tasks/agent-loop/current.json` after independent review.
