# Sprint R239 — concrete abstract Yulang inference model

Status: ADMITTED, Luna-owned whole-model candidate construction.
Baseline: `dea5d9d92c4429d0a259e0db8475c315a2ca39b3` on `yulang3`.
Unchanged goal: establish Yulang's source-directed Simple-sub inference
guarantees, with annotation effect hygiene as a required model component and
Rust correspondence as a later separate layer.

## Original roots and fixed quantifiers

Use `YulangClosure.SourceProblem` and its unchanged roots in
`notes/theory/lean/YulangClosure/Contracts.lean:128–154`:

- `InferenceSoundness`: every supported source/scope, actual generated
  constraint, and satisfying assignment yields an original source witness and
  the same scoped observations.
- `SourceScopedCoverage`: every original source judgment and actual generated
  constraint has a solving assignment with that same scoped witness.
- `PrincipalCoverage`: retain the original principal solution and universal
  instance-factorization quantifier.
- `InferenceTermination`: use the actual inference initial state and complete
  transition relation.

Do not narrow the source grammar, replace the arbitrary satisfying assignment
with native success, weaken shared-witness equality, or claim a root closed by
merely defining an instance. R238 is the preceding reviewed boundary: the
generic parent has no concrete Yulang instance and separate R217/R208
annotation components lack an authoritative common interpretation.

## Required candidate

Create one coherent mathematical model candidate, not another isolated
permission/residual lemma. It must define, in the same source signature and
scope:

1. immutable source declarations, lexical owners, annotation occurrences and
  scopes; resolved effect identities with type arguments; composed polarity;
  Function arrow rows separately from value `Effectful` wrapper rows;
2. the original source judgment over every existing expression, pattern,
   statement, container, arm and client constructor, preserving exact
   Lambda entry/receipt/body scopes and complete App/Call checking obligations;
3. independent Simple-sub generation and solution interpretation, including
   actual generation, accumulation, propagation, levels, extrusion, intrusion
   and generalization interfaces. `solves` must not call source typing,
   `Kernel.atom`, successful native inference, or the soundness conclusion;
4. one complete shared assignment/readout defining `sameScoped`, retaining
   endpoint ports, occurrence identities, provider/owner, event paths, all
   uses, futures and the original shared witness;
5. a concrete `SourceProblem` value whose four roots unfold to those definitions
   without changing their quantifiers. The native fields must name the actual
   abstract inference state/transition, not an arbitrary placeholder.

Use the adopted source, Simple-sub and effect-hygiene authorities and existing
Lean definitions only where their equations match. Reuse existing R169/R41/R38
results at their real interfaces. `OriginalSourceGeneration.Build/Satisfies`
cannot be renamed as independent Simple-sub generation/solving. Do not fill
missing semantic fields with arbitrary predicates or a theorem-shaped
assumption.

R237's all-eight direct literal generator proposal remains unadopted. The
typed-Union question remains pending. Preserve both full source domains and
record an unresolved equation if either decision is required; do not infer an
approval from this model task. These are independent blockers and must not be
silently consumed.

## Parent application and success evidence

The core evidence is a typechecked model with the four parent roots unfolded
and an actual Lambda case. Show how independently generated annotation clauses
under the same assignment feed the exact original `sourceFormalRole` atom and
Lambda `Judgment` consumer; expose App's full original clause set and checking
children in the same model. If a required source equation is unresolved, keep
the module an explicitly incomplete candidate and name that exact equation.
Do not report parent-premise reduction or root closure until the theorem is
applied to this concrete model and the source constructor premise actually
disappears.

## Authority and frozen inputs

| Path | SHA-256 |
|---|---|
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean` | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| `notes/theory/lean/YulangClosure/SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `notes/theory/lean/YulangClosure/SimpleSubGrowingInference.lean` | `865b9eb4a64962182a22a9e507b98b1e7ab92ac143e4cbfea0b8570e39bb58ce` |
| `notes/theory/lean/YulangClosure/SimpleSubLatticeGrowingInference.lean` | `1270e3407ddeef881020610b094709ebba07b62a97e54712bcc4b139ef8e78d0` |
| `notes/theory/lean/YulangClosure/SimpleSubGeneralizationSoundness.lean` | `3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246` |
| `notes/theory/lean/YulangClosure/OriginalPrincipality.lean` | `c9d214cd086aa1fbdf8f471e7b52c8cccddaa971fc68a8bb0956c9539d098dc7` |
| `notes/theory/lean/YulangClosure/OriginalInferenceTermination.lean` | `26aca31b41897e297e516bf98b6e11d63dab50482a69f5b8a1f98a739696f946` |
| `notes/theory/lean/YulangClosure/SourceAnnotationElaborationR217.lean` | `e10a84fc095af0cd492f1dd8285eb0136f185b64a29a66deaddc35973c6c08d3` |
| `notes/theory/lean/YulangClosure/StaticAnnotationConstraintInterpretation.lean` | `1829ee637ab5cf3254e220e4c0fc1306f248499f087baa779287b947c67018c9` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/design/2026-11-02-literal-l1-adoption.md` | `f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8` |
| `tasks/agent-loop/inbox/abstract-source-inference-model-r209.md` | `c6edf5e4490511b86837391dec73e16ca35737c2d90f5b95eb4a1d390ba0711a` |
| `tasks/agent-loop/history/20261102-fixed-inference-model-r213-outcome.md` | `5c4ada6c740926181d42251178326596bc10f95e6b05a340ab28417b48f6d725` |
| `tasks/agent-loop/inbox/source-annotation-constraint-model-r238.md` | `e47f82011b870dcc6614cdc139036e32e2b6dc53412c0e17b2b84198b9eb0fcb` |

Do not overwrite R209 or R213 records. User-authorized R237/R238 outcomes remain
separate inputs; typed Union stays in its questioner's bundle.

## Ownership, resources and gate

Luna alone owns:

- `notes/theory/lean/YulangClosure/AbstractSourceInferenceModel.lean`
- `tasks/agent-loop/inbox/abstract-source-inference-model-r239.md`
- this sprint contract and `tasks/agent-loop/current.json`.

The previously absent Lean model path and handoff path were checked for an
existing lease before admission; neither has one. No other writer may acquire
these paths. Rust remains `NO_SAFE_CODE_SLICE` for the inspected hygiene seam;
do not touch `candidate_source.rs`, `candidate_effect.rs`, receiver code, the
pending question bundle, or UNKNOWN/quarantined runtime files.

Primary budget: at most 3,600 seconds. Fresh independent source/model review:
at most 600 seconds. Zero Astra. Use Lean 4.35.0/Lake 5.0.0 and only the
existing `notes/theory/lean/.lake`; no new cache path, worktree, environment,
target or scratch directory. Existing cache growth cap: 64 MiB. At most two
targeted pinned checks, assigned to the primary. No tests unless the user asks.

The reviewer must reject arbitrary `Kernel` meanings, assumed reflection,
missing constructors, weakened original roots/`sameScoped`, hidden semantic
choices or claims of proof closure. Stop at the exact unresolved source
equation and present a concrete authority decision if one is required.
