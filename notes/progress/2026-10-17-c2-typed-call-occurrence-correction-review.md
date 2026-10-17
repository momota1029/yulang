# c2 typed call occurrence correction — sprint closeout

Sprint: `c2-typed-call-occurrence-correction-20261017`, contract revision 3  
Baseline: `8f012935e`  
Outcome: **REVIEWED-CLEAN-BOUNDED**; typed source/native occurrence correction proved and independently reviewed.  
Parent: original FORWARD-FIRST-CALL A/B, semantic F2 admission, VIEW and CHECK remain OPEN.

## Adjudicated result

The previous `C-AppArg` candidate `Unit+ <= arg(N2)` was ill-typed and had no
constructor edge. Its revision-1 source claim is explicitly withdrawn. For a
successfully registered c2 Apply construction, the native initial pair is
`callee2+ <= N2-` at checking occurrence `(c2,0)` with its occurrence-derived
cause. `arg(N2)` is the same retained positive endpoint as source argument `a2`;
that identity is not a separate subtype pair.

Only under an actual positive Function comparison `P+ <= N2-` processed by
ordinary Function decomposition does the conditional child
`arg(N2)+ <= arg(P)-` follow. This is ordinary call-check evidence. It does not
construct semantic `IF(g)`, any original F2 guard/admission, the complete
`B_in` action, VIEW or CHECK. The proof also requires successful registered
constructor premises and does not prove reachability of the exact example
through every candidate route.

The previous source-graph retention and identity-substitution facts remain
usable only within their recorded premises. Original providers, carriers,
worlds, contexts, observations, responses, resumptions, futures and A/B
quantifiers were preserved without projection.

## Implementation boundary and next owners

Implementation research progressed by locating and pinning the source seam:
`candidate_source` retains the Apply source children; `shadow_apply` builds the
negative Demand and whole-call pair; `candidate_call::observe` authenticates
source/native identities and polarity; ordinary Function decomposition owns
the conditional child. This is sufficient to correct the implementation
correspondence documents, but not to justify a compiler edit.

`NO_SAFE_CODE_SLICE` remains. The original source-admission owner must derive
and type the actual F2/IF(g) formation and comparison-independent admission
judgment from the source signature/use rule. The inlet/consumer owners must
supply complete carrier VIEW and correlated original-clause CHECK. Until those
source rules and gates are independently reviewed and adopted under the
repository's design-authority process, no compiler semantics change follows.

## Independent reviews

- Compiler referee: CLEAN within the conditional source/native scope; no
  reachability or semantic admission overclaim. Receipt SHA
  `dc944d612e45b687161292133c2838a42fc7f47fe923ebb8561e0bee3786900a`.
- Spec auditor: CLEAN within the bounded correction; original quantifiers and
  open gates preserved. Receipt SHA
  `d92d8ce778da9c61570fe67be0da685fc14d0e6a8c5f758465ad5b5c37500de2`.
- Luna adjudication: both receipts agree with the frozen source correction and
  proof. This closes only the packet's typed occurrence result.

## Frozen artifacts

- Contract rev3: `tasks/agent-loop/sprints/c2-typed-call-occurrence-correction-20261017.md`, SHA `aaaff21bda20de6288fd660356e6fcb63460e76bae2d239b662746664cf11adf`.
- Corrected source artifact: `notes/design/2026-10-17-c2-admission-occurrence-and-phase-rule.md`, SHA `a78c3b32db064e3e6add46daeb7395703fe453fb6aba74ba9d98ce82ed409d25`.
- Source handoff: `tasks/agent-loop/inbox/20261017-c2-admission-occurrence-and-phase-rule.md`, SHA `3bc79093b819f2de7029b81136bbfed0a3b9ef727acf68cb5c87696b184e9be4`.
- Proof: `notes/theory/2026-10-17-c2-native-call-operand-correspondence.md`, SHA `725c14759f92b85203b5d22894b0de1da95732448b50f0718a8879ed56243aed`.
- Proof handoff: `tasks/agent-loop/inbox/20261017-c2-native-call-operand-correspondence.md`, SHA `923f792a915d8e3a95adf4d563f43c59f5cc99ff5ddf60d9ec07e6f1a7110b64`.
- Compiler receipt: `tasks/agent-loop/inbox/20261017-c2-native-call-operand-correspondence-compiler-review.md`, SHA `dc944d612e45b687161292133c2838a42fc7f47fe923ebb8561e0bee3786900a`.
- Spec receipt: `tasks/agent-loop/inbox/20261017-c2-native-call-operand-correspondence-spec-review.md`, SHA `d92d8ce778da9c61570fe67be0da685fc14d0e6a8c5f758465ad5b5c37500de2`.

All authors and reviewers STOPPED. Total charged: 445/600 seconds (source 160,
proof 145, compiler review 80, spec review 60). The remaining 155 seconds are
retired, with no carryover. `python3 tools/agent_sprint.py check` passed; this
is workflow/static evidence only. No tests, build, probe, compiler/runtime
execution, compiler edit, semantic adoption, expected-output change or
production promotion occurred. Luna remains sole Git integrator.
