# Sprint R45 — derive an Application output owner and its consumers

Status: CANDIDATE until Luna freezes this contract and grants exact leases
Branch / baseline: `research/simple-sub-intrusion` / `6bf4236c8`
Authority: unchanged original inference/evaluator theorem and Simple-sub A/B;
  `rules/goal-driven-sprints.md`; delegated JOF recommendation; R44 is closed
  as an unsuccessful non-authoritative candidate.
Contract revision: 1; hash recorded in `tasks/agent-loop/current.json`.

## Original outcome and success evidence

Parent: the unchanged full inference/evaluator theorem and original Simple-sub
A/B claims, quantifiers, accepted source domain and semantics. Parent remains
**OPEN, 0 → 0**. No source restriction, premise weakening or production change.

Outcome: construct a source-owned output description for the ordinary
`q = Application(Name(loop), Name(y))` from independently formed operand and
Application premises, or identify the first precise judgment for which no such
owner can be formed under the pinned rules. Carry the result through the
complete Call interface and the exact Generalize actions for two independent
frames and a shared-frame alias. Apply every established result immediately to
the original parent obligation.

Success requires a typed, acyclic derivation that identifies (a) the authentic
Application output owner and its exact free-dependency telescope `D_q`,
separately from source context and type scope; (b) the actual effect
introduction and all ordered result/provider/world/future/receiver/return and
pending/W/Z Call arms; and (c) explicit retain/fix/copy maps for two independent
frames and an alias. No premise may be obtained from a completed `Q_q`, solved
endpoint, successful query, native solver state or `D_q := Gamma_q` assumption.
An unsuccessful construction is useful only if it names the earliest blocked
judgment, the missing premise and owner, and a source-qualified falsifier or
why available authority does not provide the owner.

The independent Sol lane attacks the candidate's dependency and provider
assumptions with a concrete counterexample or a source-supported derivation.
The implementation lane is read-only and records the exact current source to
constraint to propagation to consumer/evaluator path and its proof prerequisites.
R44 already found `NO_SAFE_CODE_SLICE`; this sprint grants **no Rust/test/build/
Cargo/runtime/expected-output or production authority**. It must not read or
modify quarantined `candidate_scheme.rs`, `shadow_apply.rs`,
`candidate_local_self_recursion.rs`, `tasks/current.md`, or unknown R35–R41
artifacts.

## Frozen dependencies

All hashes below refer to exact bytes at baseline `6bf4236c8`:

- R44 contract:
  `8a9cdf31c8ce33feb30673a7cb91c099173ecd1da44e37e76b27d951960a91d8`.
- R44 unsuccessful-candidate review/adjudication:
  `4e29ef28ad7cdec80a2c195e8bbac09b07fb4ff15c3ff4ca11834ffba010c0aa`.
- R44 scope audit:
  `172eb876bb50d8439a996cb411af537eb3f526e4dfc951c5fb996b666eb0e9cc`.
- R44 conditional evaluator corollary rev2:
  `bb7aff3ed064b7118861f8da67df2d69bd0392c783df7e4864d1a811b112d3ee`.
- Source Generalize definition/proof:
  `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`.
- Typed-computation core:
  `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e`.
- Code-Call input construction (verified corrected digest):
  `f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6`.
- Call source-interface construction:
  `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98`.
- R44 implementation boundary:
  `5478d92e69688b26b0b2e6e0564df1efa5d06ef98aeaed5dd222110be4603a21`.
- R42 implementation gate:
  `855c07f2a6de1e156209f91c7c9f9ea2169369feb0381edb63ddeceb013c1758`.
- Source-computation role elaboration:
  `9a230eb023698666f4c3e518a527009d6915e65f658b230e6da6a29914ca3abb`.

R44 draft and proof attempt are rejected design evidence only. They may be
read as counterexample inputs, never as established formation premises.

## Two productive lanes

### Constructive core proof — Astra, bounded

Use contextual metavariables and explicit substitutions to ask whether the
Application constructor can authenticate every member of `D_q` before Call
headers. Build several related stages: derive the owner/dependency rule; carry
it through effects and complete Call interfaces; instantiate both independent
frames and the shared alias; apply the outcome to the unchanged parent. Do not
assume `D_q` is empty or the full context. Stop at the first unsupported owner
with a minimal exact judgment/falsifier. Maximum three substantive stages.

Exact outputs:

- `notes/theory/2026-10-19-r45-contextual-output-core.md`
- `tasks/agent-loop/inbox/20261019-r45-core.md`

### Independent source attack — Sol

Independently reconstruct the actual q source/interface dependency order from
the pinned Generalize, Code-Call and source-interface sources. Attack
irrelevant-challenge dependence, provider replacement, all Call arms and
two-frame/alias scope. Try to refute the proposed owner; if it survives, give
the exact source judgment chain and identify all remaining premises. Do not
certify Astra's work or use solver success as evidence.

Exact outputs:

- `notes/theory/2026-10-19-r45-application-derivation.md`
- `tasks/agent-loop/inbox/20261019-r45-proof.md`

### Source/native/evaluator path — Luna/high, read-only

Use only the pinned R42/R44 implementation-boundary documents, source role
elaboration and typed-computation core. Trace the available source constructor,
generated constraint owner, propagation, typed Result/Preserve consumer,
Context/Dispatch path, CopyScope boundary and evaluator. Name at least two
actual safe source/native owners inspected and record `NO_SAFE_CODE_SLICE` if
the required owner/certificate or writer identity is absent. Do not inspect
quarantined paths or unknown-owner artifacts.

Exact outputs:

- `notes/progress/2026-10-19-r45-source-native-evaluator-path.md`
- `tasks/agent-loop/inbox/20261019-r45-implementation.md`

## Resources, exact leases and review

Aggregate ceiling 3000 seconds, no carryover: Astra 300 seconds; Sol 900;
Luna read-only implementation mapping 600; fresh independent review reserve
900 (compiler_referee and spec_auditor, 450 each); primary integration 300.
Charge reserved grants when issued. Actual elapsed CPU/RSS remain UNKNOWN unless
observed. Astra medium effort, at most one Astra assignment and three stages.
At most six active/reserved/unknown assignments including primary; retain
unknown dirty-file ownership quarantines. If capacity cannot satisfy the envelope,
serialize within the same cap without starting nested agents.

Each lane owns only the two exact output/handoff paths listed in its section.
Luna owns this contract, current state, and integration. Workers do not start
teams, widen leases, change semantics or use Git. The candidate and all direct
dependencies freeze before fresh independent review. Reviewers check authentic
dependency ownership, complete provider/pending/W/Z/future/receiver/return arms,
two independent frames, alias sharing, original A/B scope and evaluator-claim
limits. Primary adjudicates; review is not promotion.

Stop on the fixed outcome, a source-qualified counterexample, an unsupported
owner after bounded stages, authority/dependency/lease change, the resource
bound, user STOP or session end. Keep the original parent OPEN. No compiler
implementation follows automatically; a later code gate requires an
Authoritative source rule, source/native and copy proof, and authenticated
write-lease release.

## Dispatcher proposal and primary decision

The boundary dispatcher proposed this integrated outcome, contextual
metavariable/explicit-substitution method, Astra/Sol proof split, read-only
implementation path and 3000-second envelope. Luna accepts the core outcome
and method. Corrected before activation: baseline is the current pushed
`6bf4236c8`, not the dispatcher's earlier `7dadd71ea`; implementation remains
read-only because R44 found no safe code slice; Code-Call digest is verified as
listed above. This contract records no approval beyond these exact lanes.
