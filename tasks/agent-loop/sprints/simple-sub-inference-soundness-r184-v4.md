# Sprint R184 v4 — concrete Simple-sub inference soundness

Status: versioned dependency revision after the v3 proof lane found two exact
imports required to state and apply the existing certificate soundness theorem.
The original parent and objective stay fixed; no semantic or algorithm change
is selected. Baseline: `yulang3` at
`513af1ce8664581bd76480674e8275fb0bad1a7a`.

## Original parent and measurable outcome

The target is Yulang's mathematical type/effect inference guarantee, not Rust
implementation correctness. Preserve all original source forms, scopes,
effects, quantifiers, and one shared witness. The forward target follows the
user's statement:

```text
Γ ⊢ e ⇒ (C, τ)  ∧  σ ⊨ C
  →  σΓ ⊢ e : στ
```

Formalize `C`, its independent type/effect denotation, the source-directed
generator, substitution of the same satisfying assignment, and the original
typing judgment from the pinned authorities. State and prove the concrete
theorem for the full original supported domain, then instantiate or explicitly
map it to `Contracts.lean`'s `SourceProblem.InferenceSoundness` without changing
its same-solution `sameScoped` conclusion.

Success requires the generated-solution implication to yield complete original
source typing, including App/Call and contextual effects wherever the accepted
rules use them, and no unproved `LocalLaws`, source-admission, witness, or
readback premise. A lemma that merely assumes `Build`/`Satisfies`, source
typing, or the desired admission does not close a parent premise. If one
original local law remains genuinely unproved, report the exact premise and
owner; label the parent OPEN. Do not narrow the source domain to obtain a green
fragment result.

## Exact output lease and method

One registered `lean_prover`, read-only except for these exact outputs, 2400
seconds:

- `notes/theory/lean/YulangClosure/SimpleSubInference.lean`
- `tasks/agent-loop/inbox/simple-sub-inference-soundness-r184-proof.md`

Inspect the direct import headers of the five pinned mathematical modules
(`SimpleSubConstraintSyntax`, `SimpleSubLatticeInference`,
`SimpleSubGeneralizationSoundness`, `OriginalSourceInterpretation`, and
`SourceFunctionMembership`/`NativeDictionaryDenotation`). This is a dependency
map, not a census; pin further definitions only if the proof actually needs
them. Reuse the three pinned SimpleSub modules for their actual constraint
grammar, solver relation and soundness theorem. Preserve exact hypotheses and
apply anything relevant to the original parent. Do not
define a second algorithm. Only fill a gap if the pinned modules leave one.
Construct the mathematical constraint language, its satisfying-assignment
relation, the syntax-directed generator, and the original source judgment as
separate definitions. Prove soundness by induction over actual generation and
its scoped declarations, preserving the complete telescope and same
assignment/shared witness. Effects and Call must follow the source rules and
the approved algorithm; no arbitrary predicates or unconstrained
`LocalLaws` may hide the obligations. Reuse proved hygiene results only with
their exact hypotheses and apply each to this parent theorem.

Run the pinned project only after a concrete theorem exists. Use the existing
Lean 4.35.0 environment/cache, one verification owner, and the bounded project
checker; report the exact command, exit, theorem type, and complete `#print
axioms` audit. Do not install tools, create another environment/cache, edit the
root import, or run Rust/build/tests/Cargo/runtime work. If required imports or
semantic owners fall outside these pins, stop and return exact paths for
sequential primary admission.

## Parent map and non-goals

- `InferenceSoundness` (`Contracts.lean:128–130`) is this sprint's parent.
- `SourceScopedCoverage` (`:133–135`) is the distinct reverse direction; no
  proof of it is inferred from forward soundness.
- `PrincipalCoverage` (`:138–144`) requires the original principal ordering
  and universal factorization; it is deferred as its own proof obligation.
- `InferenceTermination` (`:152–154`) requires well-foundedness of the actual
  inference transition relation; it is deferred separately.
- `NativeCorrespondence` (`:147–149`) and Rust simulation are later bridges,
  not assumptions or evidence for the mathematical theorem.

No principality, termination, implementation, source/native simulation, or
production-cutover claim is authorized here. A companion coverage lane starts
only after the canonical generator and constraint denotation freeze; it must
use this exact generated `C`, not a separately chosen schema. Do not introduce
a second definition of the algorithm.

## Falsifier, review and stop conditions

Falsifier: a satisfying assignment for an actual generated `C` for which no
original source derivation exists under the same substituted context/type and
shared witness, or an induction case whose original rule premise is absent
from `C`'s denotation. Fresh independent mathematical/source-correspondence
review follows a frozen output, 600 seconds. It must reject source restrictions,
assumed admission, a substituted witness, redefined solving, and any theorem
that does not apply to the original parent.

The accepted top-level inference decision fixes constraint construction,
propagation, levels, extrusion, intrusion, generalization and the required
soundness direction. If faithfully stating the theorem requires a choice that
those sources do not determine, stop before selecting it and bring the exact
alternatives to the user. Otherwise continue without another approval request.

## Frozen direct inputs

Recompute every digest before content reads. Any mismatch stops the lane for
sequential primary review. Budget accounting: R184 v1 proof grant 2400 seconds,
parent-map review 600 seconds, and v3 proof grant 1800 seconds are fully charged.
V4 grants at most 1800 additional proof seconds and one fresh 600-second
proof-artifact review, for a 7200-second total sprint envelope. No renewal.

- `notes/design/2026-10-11-yulang-inference-top-level-principles.md` —
  `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`
- `rules/compiler-engineering.md` —
  `4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9`
- `notes/design/2026-10-08-source-generalize-definition.md` —
  `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`
- `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` —
  `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`
- `docs/yulang-source-type-safety-ja.tex` —
  `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`
- `notes/theory/lean/YulangClosure/Contracts.lean` —
  `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean` —
  `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`
- `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` —
  `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`
- `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` —
  `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132`
- `notes/theory/lean/YulangClosure/OriginalSourceChecking.lean` —
  `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6`
- `tasks/agent-loop/history/original-inference-model-r183-stop-replan.md` —
  `3178e92e4d6565fca58a9ea20c4bff7aac613cc2fa409600ce35a8f982304f50`
- `tasks/agent-loop/history/parent-theorem-dependency-reconstruction-20261102.md` —
  `bdb83b830072e78c244cd2da6215e7ba5f2468df93afa5a3208c2a2419c08fe0`

- `notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean` —
  `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`
- `notes/design/2026-10-08-contextual-function-membership-definition.md` —
  `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0`
- `notes/theory/2026-10-08-call-semantic-input-realization.md` —
  `fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a`
- `notes/theory/2026-10-08-simultaneous-immutable-root-introduction.md` —
  `a5efa7056b12f931892548ecf3366d66156627ec44577c99d20ca48596438ae6`
- `notes/theory/lean/YulangClosure/SourceFunctionMembership.lean` —
  `8d370ee57e486ae48607d1bab493ae5135f28bf8a5a7ff1b0ef240fc0247e424`
- `notes/theory/lean/YulangClosure/NativeDictionaryDenotation.lean` —
  `d44a78f08970a09ca4c3e99a1d8dea846286a299d1a2bc91ec3b5e0eabea9070`
- `tasks/agent-loop/history/simple-sub-inference-soundness-r184-stop-dependency-boundary.md` —
  `1a5ca3a97ac701658ca8587e3d59c8c78051c0ed0fa2db7f8ed89de7bf2a9e6b`

- `notes/theory/lean/YulangClosure/SimpleSubConstraintSyntax.lean` —
  `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6`
- `notes/theory/lean/YulangClosure/SimpleSubLatticeInference.lean` —
  `c534c060dfde84f2817fbaa53222f430b59d9b6377cfacedabeca7b9b4b8ffa3`
- `notes/theory/lean/YulangClosure/SimpleSubGeneralizationSoundness.lean` —
  `3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246`

- `notes/theory/lean/YulangClosure/SimpleSubLatticeCertificates.lean` —
  `55533eee35ed7058abd125ac0e01d8f29b8c0534800018d254c1bd9f9c0bb79b`
- `notes/theory/lean/YulangClosure/SimpleSubRegularPublication.lean` —
  `18fc6f138204e1529dcd0bb9c01a20de7444a26e4dadc87677460ccd8ac9fc99`
