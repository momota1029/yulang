# Sprint R183 — recover the original inference model and App readback

Status: admitted bounded continuation of the unchanged Yulang type/effect
inference-soundness goal. Baseline: `yulang3` at
`89d0dd2bfc3619e6034360e8aa0837bf834499a`.

## Parent theorem and outcome

The parent remains original `SourceProblem.InferenceSoundness`: for every
supported original source form, generated constraints, and satisfying
assignment `a`, derive its original source typing judgment and one shared
`sameScoped` witness under that same `a`. Preserve all forms, quantifiers,
effects, complete prior telescope, original admission and shared witness. Rust
implementation correctness is not the target theorem.

R182 identified two bounded gaps: the syntax catalogue stopped at three header
authority citations; and the pinned Lean declarations did not identify a
concrete `SourceProblem` instance or inference-solution-to-App-payload/admission
readback. Determine whether the original sources define the missing model and
equations, faithfully encode a concrete mathematical model not yet present in
Lean, or leave an equation semantically open. Produce an authenticated
definition map and the first constructible original-scope soundness lemma, or
one exact missing equation suitable for a material decision.

## Lanes and exact outputs

1. Source authority lane, read-only, 900 seconds:
   - inspect only §2 of the pinned source-generalization definition;
   - inspect only §§3–5 of the pinned definition-and-proof document;
   - inspect the pinned `sec:source` and `sec:all-source` sections of the
     source-safety paper;
   - complete the Endpoint/Port/Binder and descriptor/interface write
     representability catalogue from the pinned `OriginalSourceSyntax.lean`;
   - map original generation, solving, source typing and shared-witness
     readback equations, without choosing any missing equation.
   - sole output: `tasks/agent-loop/inbox/original-inference-model-r183-source.md`.
2. Lean model lane, read-only, 900 seconds:
   - inspect exact `SourceProblem`, `InferenceSoundness`, `generates`, `solves`
     and `sameScoped` declaration occurrences in the pinned modules;
   - inspect the `OriginalSourceChecking.lean` declaration context and only
     `generated_application_ports` and `generated_application_checking`;
   - map each `SourceProblem` field to an actual concrete Lean declaration, a
     source-defined mathematical object awaiting faithful formalization, or an
     equation still requiring semantic choice;
   - trace App formation, unchanged `LocalAdmissions.logical`, and the same
     assignment/full-telescope witness. Do not equate solving with desired
     source typing or assume admission.
   - sole output: `tasks/agent-loop/inbox/original-inference-model-r183-proof.md`.

Combined success is an authenticated source-to-Lean definition map and either
an actual first constructible theorem target for the original parent or one
exactly stated unresolved defining equation. A scoped search cannot establish
repository-wide absence of an instance. Stop on any essential unpinned owner,
ambiguous authority, or equation not determined by accepted sources; return
the exact locator without recursive traversal. No semantic selection, compiler
edit, Rust inspection, Lean command, build, test, Cargo, runtime, new cache, or
environment is authorized.

## Frozen direct inputs

Recompute every digest before content reads. Any mismatch stops the dependent
lane for sequential primary review.

- `notes/design/2026-10-08-source-generalize-definition.md` —
  `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`
- `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` —
  `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`
- `docs/yulang-source-type-safety-ja.tex` —
  `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`
- `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean` —
  `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`
- `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` —
  `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`
- `notes/theory/lean/YulangClosure/Contracts.lean` —
  `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `notes/theory/lean/YulangClosure/OriginalProofProgress.lean` —
  `21e361962538d5e2738041b58186682a4a9fb3ad10c75f4c39dc97e32a443f39`
- `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` —
  `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132`
- `notes/theory/lean/YulangClosure/OriginalSourceChecking.lean` —
  `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6`
- `tasks/agent-loop/sprints/source-syntax-owner-r182.md` —
  `c1ef27937a773c09cb0394dca29684f4def469322def8d864c1a3f38af4ca304`
- `tasks/agent-loop/history/source-syntax-owner-r182-activation.md` —
  `08a7de965830c06194b9236c5524860d231161ac01813eb172395b218be54987`
- `tasks/agent-loop/history/source-syntax-owner-r182-outcome.md` —
  `a434c61892d82dc4abe6f7c6651deb09978228f9f1e17d7de0d39f16a1e10662`
- `tasks/agent-loop/inbox/app-syntax-owner-r182-source.md` —
  `76a2a787b1e4caee11b6d347236761996abecdd45168f7731f79f3d389214c7f`
- `tasks/agent-loop/inbox/app-inference-instance-r182-proof.md` —
  `9571d4c4c95604efcd5f097298d163684df06cc13fa12bac6edd805d5e026357`

## Review and stop conditions

Fresh independent exact-conformance review: 300 seconds after both outputs
freeze. Reviewer must reject any field justified only by an abstract structure,
generic parameter, conditional reconstruction, supplied admission, or newly
selected witness. No Lean proof review is implied. No user decision is needed
for faithful source authentication and formalization intake. A material user
decision becomes necessary only if the accepted original sources leave the
inference, solving, or admission equation genuinely unspecified. Parent remains
OPEN absent an independently reviewed full-scope proof or counterexample.
