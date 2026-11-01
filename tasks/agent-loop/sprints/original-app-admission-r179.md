# Sprint R179 — construct original App logical admission

Status: ADMITTED continuation of the unchanged Yulang type/effect inference soundness goal. Baseline: `yulang3` at `9ee28f082c157fda11d7c5c948decd3798472bbb`. Parent `SourceProblem.InferenceSoundness` retains all original quantifiers, source forms, and one shared same-solution `sameScoped` witness. Runtime/Rust-program correctness is excluded; Rust is inspected only for source correspondence.

## Fixed outcome

Construct the App occurrence's original `.logical .viewLogic` payload and prove its existing `LocalAdmissions.logical state binder .viewLogic data` premise from the same inferred solution and complete prior source telescope, then apply it to R178's existential App binder. Do not assume the admission predicate, accept the five `Logical` fields as free parameters, define admission as equality with a newly assembled record, change the source rules, or reuse Lambda/formal admission for App.

The exact source rule is `OriginalSourceGeneration.sourceRules` App (`:111–123`): it introduces `b = ⟨site,.viewLogic,0⟩` and requires original admission plus finite value and computation Checking, alongside the App-local clauses and both source children. R178 independently reviewed that native Apply does not construct the local admission; this packet attempts the constructive owner bridge, not another inventory.

## Required construction plan

For the actual source App and the *same* solution `a`, construct `Logical s View` field by field from the original source meanings and genuine callee/whole-inert-argument induction hypotheses:

1. `descriptors`: retain the child descriptors and construct only the exact App/Call descriptor entries justified by original descriptor formation and whole-argument compatibility at this occurrence.
2. `interfaces`: derive the callee returned-value and complete inert whole-argument interfaces from those same child derivations; preserve permission, inflow, residual, and complete Call receiver/result distinctions.
3. `viewMeaning`: use the existing original interpretation of the source-owned view presentation at this App occurrence under `a`; do not choose an unrelated or per-call view.
4. `eta`: use `a`'s source assignment at the App's extended telescope.
5. `witness`: transport the same `a`-owned joint witness through the prior telescope and App extension; do not introduce a fresh witness.

Every field must have an actual source-owned constructor or equation. The proof must then discharge the existing local admission relation. `SourceAppAdmissionR159` and `OriginalAppConstructionR160` expose the prior boundary: they do not authenticate a concrete App `LocalAdmissions.logical` law. Do not repeat their consumer-only theorems. If one required field or the admission relation has no independent constructor, stop with the first exact owner/equation and classify R179 **BLOCKED**.

A proposed packet that merely takes these five outputs as parameters does not meet the outcome. Do not promote a candidate policy, synthetic permissive kernel, implementation guard, source counterexample, or parent theorem.

## Parent application and limits

An actual App admission is one local premise only. Finite App value/computation Checking, complete Call certificate, whole Build satisfaction, concrete `SourceProblem`, and the parent's shared same-solution `sameScoped` witness remain open. No result here proves whole-language soundness or production readiness.

## Frozen direct inputs

Every row must strictly parse as one path and one full 64-hex SHA-256 and match before content reads. Count path rows separately; malformed rows are fatal.

- `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` —
  `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132`
- `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` —
  `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`
- `notes/theory/lean/YulangClosure/OriginalSourceChecking.lean` —
  `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6`
- `notes/theory/lean/YulangClosure/OriginalFormalAdmission.lean` —
  `77230ab7984ee544db16fe4d9663b73f98b9afa9c5d2610fad59c26753d5ac7c`
- `notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean` —
  `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`
- `notes/theory/lean/YulangClosure/OriginalParameterSemantics.lean` —
  `733c5b05e0db226f95d14ff2161c46e9a389b43d86b365b000a9656ec4fd0bd2`
- `notes/theory/lean/YulangClosure/OriginalParameterWorld.lean` —
  `7b5f849f744dbe56f374d8be6b11a5a218176abf6eeda2fb9da8180c7b1ff802`
- `notes/theory/lean/YulangClosure/OriginalAppConstructionR160.lean` —
  `a7a766ef1d733719bfc4145bdcc9051e2e9e64521feb3fa400877a60bf9cb793`
- `notes/theory/lean/YulangClosure/SourceAppAdmissionR159.lean` —
  `5e948a1f8a3aab66028f885ebf16b6ffeed81999039e8a5a4e9c3caf84464408`
- `notes/theory/lean/YulangClosure/SourceLogicalOccurrencesR104.lean` —
  `0e7a42d66578388585a5abd1da12c77a9d7d46823687ed511d26e359b3078f39`
- `notes/theory/lean/YulangClosure/OriginalSourceValueEntryAdmission.lean` —
  `3dc218f9d6623192d7d85c6f5be14f0fddbe833b19ede467c75647a5833205dd`
- `notes/theory/lean/YulangClosure/OriginalProofProgress.lean` —
  `21e361962538d5e2738041b58186682a4a9fb3ad10c75f4c39dc97e32a443f39`
- `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` —
  `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md` —
  `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`
- `tasks/agent-loop/history/app-demand-original-checking-r178-outcome.md` —
  `eb5dab4d2905db070d20e70c54a90b39a686285c8297d74e134bd68505cc5b47`
- `tasks/agent-loop/inbox/app-demand-original-checking-r178-proof.md` —
  `86b17a3e1a943f53699eb19583d1ed89e2d32fc3974075064c758cfc6b63c2f3`
- `tasks/agent-loop/inbox/app-demand-original-checking-r178-source.md` —
  `f79255103002e94c782259e60594b6280963feeebc2319fc939d6216601474fa`

## Lanes, exact outputs and verification

- Proof: one registered `lean_prover`, 1200 seconds. Sole outputs: `notes/theory/lean/YulangClosure/OriginalAppAdmissionR179.lean` and `tasks/agent-loop/inbox/original-app-admission-r179-proof.md`; sole owner of existing `.lake`. Start from the exact App induction hypotheses and same solution. A theorem must construct the fields and discharge actual existing admission. If no theorem is constructed, run no Lean command.
- Source correspondence: one registered `researcher`, 600 seconds, read-only. Sole output `tasks/agent-loop/inbox/original-app-admission-r179-source.md`. Map each planned field to the exact original App/source-Generalize clause and any existing child derivation/solution owner. Do not repeat Rust structural inventories. Keep candidate implementation facts as correspondence evidence only; no compiler edits.
- Fresh independent review: 300 seconds after both outputs and their inputs freeze; review the exact field constructors, same-solution/telescope preservation, theorem type and complete axiom audit.
- At most one focused theorem check plus its required import build, pinned Lean 4.35.0, existing `.lake` only, one CPU, 1 GiB and 180 seconds total. No Cargo, tests, runtime, default build, new environment/cache/scratch, or compiler edits.
- Stop if no source-owned recipe exists, any field requires a free parameter/independent witness, a semantic decision changes, dependencies expand, or resources are exhausted. Keep the parent OPEN.

Luna owns exact hash acknowledgements, leases, independent review, adjudication, central state, exact staging, commit and push. Preserve all UNKNOWN rows and quarantined paths.
