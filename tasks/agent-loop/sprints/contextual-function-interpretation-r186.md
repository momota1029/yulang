# R186 — contextual Function interpretation for inference soundness

Status: **ACTIVE bounded mathematical construction**, revision 1. Baseline
`yulang3` at `513af1ce8664581bd76480674e8275fb0bad1a7a`. Parent remains
`SourceProblem.InferenceSoundness`, `Contracts.lean:128–130`, unchanged.

## Outcome and parent connection

R185 was independently accepted only as an incomplete inspection handoff. It
isolated the App case: Simple-sub has a four-port `Term.function`, while the
original source interpretation has separately admitted descriptors, complete
contextual challenges, checked inlets and observations. The missing bridge was
not proved impossible or semantically underdetermined. R186 changes the method:
construct that interpretation from the accepted same-provider Function
semantics, then apply the structural Function rule to the original App case.

The unchanged parent is:

```lean
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

The target result must preserve every assignment `a`, source scope `x`, and
one shared witness `e`. App's original `.viewLogic` candidate, descriptor and
admission, whole-argument compatibility, complete Call evidence, source
incidence, callable image, conditional `roleAndInitialCallOrigin`, both
checking goals, and both child derivations remain explicit. Do not weaken the
source domain or move any Call/effect premise out of the parent.

## Construction and success gate

One registered `lean_prover` owns these exact outputs for at most 1800 seconds:

- `notes/theory/lean/YulangClosure/ContextualFunctionInterpretationR186.lean`
- `tasks/agent-loop/inbox/contextual-function-interpretation-r186-proof.md`

Define an independently typed contextual Function descriptor from the accepted
same-provider membership semantics. Its challenge side must retain the whole
carrier, argument/effect input, event, actual provider, original context and
incidences jointly. Its observation side must retain result/effect values,
pending observations and the admitted futures required by the pinned source
meaning. Keep one world, telescope and witness across all ports. Define the
four-port interpretation of `Term.function` independently of source typing or
admission.

Prove substitution/readout commutation for the same valuation. Then prove the
actual structural Function rule sound by deriving challenge-domain inclusion
from argument and input-effect contravariance, and complete observation
inclusion from result and output-effect covariance. Use the same actual
provider throughout. These inclusions must follow from the concrete
definitions; they cannot be assumed as `LocalLaws`.

Apply the result directly to original App generation. The assignment is not a
success if it stops at a standalone variance lemma: the frozen Lean artifact
must construct the `.viewLogic` candidate and discharge at least one named
original App premise from actual generated constraints and legitimate child
induction hypotheses under the same assignment and scope. State every App
premise that remains. A theorem that assumes admission, source typing, `Build`
satisfaction, the desired witness, or the parent conclusion is circular and
fails the gate.

Success requires a concrete kernel-checked theorem and its exact type plus a
complete `#print axioms` audit, and fresh independent review. A precise
source-qualified counterexample can falsify the parent case but cannot close
the soundness gate. An unproved interpretation or stand-alone structural lemma
is `INCOMPLETE` and removes no parent premise.

## Frozen scope, inputs and boundaries

Authenticate every pin before content reads. Reuse the exact original source
and Simple-sub syntax from R185; do not repeat broad inventories. Do not read
Rust, inspect `SimpleSubRegularConstraintSoundness.lean` or `Regular.expandNodes`,
or add solver internals. No change to approved source meanings, contexts,
quantifiers, source forms or production authority. If the contextual
interpretation requires a specific observable choice that conflicts with a
pinned authority, stop with that exact equation and alternatives; absence of a
Lean definition alone is not such evidence.

Use only the existing Lean 4.35.0 project/cache after a concrete theorem exists,
at most two pinned checks and one verification owner. Report exact commands,
exits, theorem types and complete axiom audit. No new environment/cache, Rust,
Cargo, build, tests, runtime work, root import edit or generated artifacts.

Fresh independent `compiler_referee` review follows frozen output, at most 600
seconds. It checks concrete definitions, same-provider and cross-port
correlations, soundness of structural variance, noncircular admission,
substitution/scope, exact parent application, and full axioms. The producer
cannot review their result.

## Authenticated inputs

- R185 incomplete outcome — `tasks/agent-loop/history/yulang-generation-soundness-model-r185-outcome.md` — `f181a23577bf4d09988218eb9133268b5d82bbad4f68d1023d5046bc0633b60e`
- R185 proof handoff — `tasks/agent-loop/inbox/yulang-generation-soundness-model-r185-proof.md` — `0f869c9973939788fd73ac4a251ebb6eec18800e4972d67cb6b5dd1a44016eda`
- R185 contract — `tasks/agent-loop/sprints/yulang-generation-soundness-model-r185.md` — `a8ef22037c3a717e979042bd53e2d3a00722c1053b0b6864f8956b5b4a21c6f0`
- `notes/theory/lean/YulangClosure/Contracts.lean` — `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `notes/theory/lean/YulangClosure/SimpleSubConstraintSyntax.lean` — `a9ec574d31223e0484fd827838b45cd019fc858ee9f326c95ebc2e1e77a1f6`
- `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean` — `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`
- `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` — `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`
- `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` — `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132`
- `notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean` — `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`
- `notes/theory/lean/YulangClosure/OriginalSourceChecking.lean` — `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6`
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md` — `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`
- `notes/design/2026-10-08-contextual-function-membership-definition.md` — `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0`
- `notes/theory/2026-10-08-call-semantic-input-realization.md` — `fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a`
- `notes/design/2026-10-05-inferred-function-call-views.md` — `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1`
- `notes/design/2026-10-05-source-contracts-and-common-allowance.md` — `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186`
- `questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md` — `9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3`
- `questions/2026-10-05-source-annotation-boundaries/approved-answer.md` — `e1e2ff77b181fe42edd404ee0d69cfc6d3bb0fbc99ba7e7f092710025d11fb12`

All source/algorithm authorities stay as pinned inputs; this packet constructs
their concrete mathematical relation and makes no semantic adoption.
