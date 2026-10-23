# Operational semantics: primary-only manuscript checkpoint

Status: **OPEN — research manuscript preserved; requested full theorem not completed.**
Claim class: candidate paper derivation for an explicitly stated execution-type
projection, plus candidate operational construction for fully decorated plans.
Author: current `/root` only. No subagents launched, no independent review,
no proof assistant verification, and no mathematical or production gate promotion.

## Exact result

The user asked to extract a genuinely closed operational semantics from the
newest TeX and complete type soundness independently of inference. The later
instruction selected primary-only work. This checkpoint does not weaken that
parent request or call its effect obligations optional.

`docs/yulang-operational-type-safety-ja.tex` contains:

- A syntax-directed execution typing judgment, immutable recursive value-graph
  typing, all machine administrative forms, typed operation payload/response
  instances, raw continuations and multi-shot resumption.
- Explicit receipt-before-force complete calls and inert adapters; shallow
  selection versus forwarding; failed pattern/guard attempts; monomorphic
  shared reference protocols; ordered record views and all eleven pattern forms.
- A finite provenance-graph eligibility construction for plans already carrying
  their View ports, profile/map automata and source phase tables. It reuses the
  existing Flow/Receive/Observe definition rather than discarding the reviewed
  transport algebra. It is a candidate construction, not approved runtime code.
- Substitution, canonical forms, immutable graph extension, evaluation-frame,
  complete-call, request decomposition and handler/resume lemmas, followed by
  one-step preservation, progress and a finite-prefix safety derivation.
- An explicit limitation: this result uses the **execution-type projection**
  and cannot by itself prove the original fine effect/profile annotations safe.

The important discrimination is pre-dispatch observation. In a decorated
configuration with inherited live protection and a receiver-local grant on an
outer complete CallView, emission-time observation gives `Protected=1, Grant=1`.
Observing only outward-bubbled requests can give `Protected=1, Grant=0` at the
inner handler. Both machines can preserve value/response types. Therefore the
projection theorem cannot silently stand in for effect/hygiene soundness.
This is a constructed decorated-graph comparison, not a reproduced compiler bug.

## Original parent application and exact remaining work

The manuscript supplies a candidate value/request/continuation proof component
for the original goal. It **does not complete** that goal. Remaining:

1. Supply every source/certificate constructor with the correct View positions,
   source profile, type-path transducer, receiver role/phase and reentry mapping.
   A supplied decorated-plan theorem is not proof of this construction.
2. Define and prove the concrete-machine/complete-cell simulation for every
   administrative frame, including pre-dispatch outer observations, failed
   attempts, operation mappers, shared reads and returned latent computations.
   Do not assume this simulation as a renamed primitive-adequacy premise.
3. Complete the certificate-to-explicit-code bridge, including recursion guards,
   computed-root initialization, native char/range/list-view constructors and
   resolved Ref-pattern equality. Fixed numeric/text helper parameters preserve
   the projection theorem but do not choose unspecified byte-level behavior.

These remain owned by the primary. The next action is a constructor-by-constructor
decoration and simulation proof on the explicit machine, not another inference
finite-witness task. Original inference/source/native A/B, Q1–Q8, principality
and production stay OPEN. No expected outputs or compiler behavior changed.

## Inputs and frozen artifact

- Original user TeX SHA-256:
  `28dc9b7fcb818e99a9513054d5847274ccce0d816a8c4a9644b802f0aa3fbd65`.
  The file was neither edited nor staged.
- Existing typed-boundary draft SHA-256:
  `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb`.
  Relevant sections: receiving/observation, transport/lifetime, observer-frame
  construction and concrete-realization boundary. Those premises remain intact.
- Manuscript SHA-256:
  `863d7d4033733bd8fdd99a744a26b0f0c93b204761431bdf2d694af4f7b71559`.
- Source inventory reads used `git show` at frozen Oracle
  `a58eefc31e22141574b6f20c6a5748151c6d79f1`, including the 62 PrimitiveOp
  constructors and runtime primitive dispatch. No Oracle executable was run.

## Verification, runtime and preservation

XeLaTeX completed, producing a 17-page PDF at
`/tmp/yulang-op-20261023/yulang-operational-type-safety-ja.pdf`.
The final build has no undefined references or overfull boxes. Table
justification still produces underfull-box notices. The first page was visually
inspected. This checks document rendering, not the mathematical argument.
`python3 tools/agent_sprint.py check` passed; it is static protocol evidence only.
No compiler changes, Cargo builds, semantic tests or executable proof probes ran.

Initial `collaboration.list_agents` returned only `/root`. It did not establish
old-session worker cessation. The prior compact state is byte-preserved in
`op-semantics-20261023-prior-current.json`; four UNKNOWN old identities and
their reserved paths remain quarantined. During this pass R349's proof and
handoff files appeared at their old reserved paths. They were not consumed,
edited, staged or treated as a writer-stop receipt.

Only this manuscript and its exact primary-owned state/contract/outcome paths
are candidates for a research-only checkpoint. Existing untracked user
documents and R349 outputs remain separate. No background work or future
automatic continuation is claimed.
