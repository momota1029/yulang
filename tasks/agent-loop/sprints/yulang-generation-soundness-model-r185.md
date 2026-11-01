# R185 — mathematical generation-to-source soundness model

Status: **ACTIVE bounded proof packet**. Revision 1. Baseline branch `yulang3`,
commit `513af1ce8664581bd76480674e8275fb0bad1a7a`. Luna owns authority,
leases, review, integration and Git.

## Original outcome and success evidence

Target the existing mathematical parent `SourceProblem.InferenceSoundness`,
`notes/theory/lean/YulangClosure/Contracts.lean:128–130`, without changing its
quantifiers:

```lean
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

This is Yulang's type/effect inference guarantee. The same generated problem,
assignment, source scope and shared witness must survive. Call and contextual
effects remain in scope wherever the accepted source rules require them.

The decisive work is to define actual Simple-sub generation and an independent
type/effect denotation, then attempt the App induction case directly. The case
must derive the original App candidate/admission, descriptor formation,
compatibility, complete Call evidence, incidence, callable image, conditional
`roleAndInitialCallOrigin`, and both checking goals from generated constraints
under the same assignment. Existing reconstruction may be applied only after
its complete source-side premises have been derived.

Success is either (a) a kernel-checked theorem that applies to the unchanged
parent, with exact type and complete axiom audit, or (b) an exact, reviewed
obstruction naming the first missing semantic equation/owner. A schema that
assumes admission, source typing, `Build` satisfaction, the parent conclusion,
or a separately chosen witness is incomplete and cannot be reported as
progress at the parent.

## Exact assignment and method

One registered `lean_prover` owns these exact outputs for at most 1800 seconds:

- `notes/theory/lean/YulangClosure/SimpleSubInferenceSoundnessR185.lean`
- `tasks/agent-loop/inbox/yulang-generation-soundness-model-r185-proof.md`

Construct the concrete constraint grammar/generation and its satisfaction
relation from the accepted Simple-sub mathematics, with a single scoped
variable namespace and independently defined type/effect meaning. Work by
induction on actual generation, preserve the original telescope and assignment,
and attempt App first. Do not define `solves` as source typing or bake the
desired source premises into constraint satisfaction. Apply every established
case to the original parent; keep unresolved constructors explicit.

Inputs are the reviewed parent map and corrected R184 v4 stop record below,
plus the authenticated original source syntax, generation, environment,
checking and interpretation modules and `SimpleSubConstraintSyntax`. Recompute
every digest before reading. Reuse the exact authorities already pinned in the
R184 v4 contract; do not conduct another source census. Do not inspect Rust,
`SimpleSubRegularConstraintSoundness.lean`, `Regular.expandNodes`, or add
solver internals as prerequisites. If an unpinned declaration is necessary,
stop before reading it and return its exact path and dependency edge to Luna.

Only run the existing Lean 4.35.0 checker after a concrete theorem exists, with
at most two pinned checks and one verification owner. Report commands, exits,
theorem types and full `#print axioms`. No new environment/cache, root import
edit, Rust, Cargo, build, test, runtime, or production activity.

## Independent review and stop boundary

After the frozen outputs, Luna assigns one fresh independent reviewer for at
most 600 seconds. Review checks semantic authority, independent satisfaction,
complete App premises, substitution/scope, exact parent application and the
full axiom audit. The author cannot review their own result. Parent remains
OPEN until the full theorem and review pass.

Stop at the first equation that the accepted algorithm/source authorities do
not determine, conflicting authority, required unpinned dependency, exact
counterexample, or budget boundary. Report the equation and owner; do not
select a semantic alternative. No user semantic choice has been established
yet. Principality, source coverage, termination, Rust correspondence and
production gates remain separate.

## Frozen inputs

- Parent map `tasks/agent-loop/history/parent-theorem-dependency-reconstruction-20261102.md` — `bdb83b830072e78c244cd2da6215e7ba5f2468df93afa5a3208c2a2419c08fe0`
- Corrected R184 stop `tasks/agent-loop/history/simple-sub-inference-soundness-r184-v4-stop-original-app-bridge.md` — `d857e35e5ce760bba88a41ab69b94cf45f5656a4ba79627b0a5394fe08a15bff`
- `notes/theory/lean/YulangClosure/Contracts.lean` — `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean` — `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`
- `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` — `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`
- `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` — `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132`
- `notes/theory/lean/YulangClosure/OriginalSourceChecking.lean` — `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6`
- `notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean` — `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`
- `notes/theory/lean/YulangClosure/SimpleSubConstraintSyntax.lean` — `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6`
- Semantic authorities and Simple-sub model pins are inherited exactly from R184 v4; no pin change is authorized here.
