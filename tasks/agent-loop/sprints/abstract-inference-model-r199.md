# Sprint R199 — abstract inference model reconstruction

Status: PRIMARY MODEL CANDIDATE FROZEN FOR REVIEW; model gate not passed.
Branch / baseline: `yulang3` / `77bb8be466bbaa6cc9d7bd4587cf5975524f3ead`.
Authority: continuing user goal; unchanged Contracts; Simple-sub top-level
principles; selected native source-Generalize and annotation/effect policy.
Primary: `/root` (Luna).
This contract admits review of an incomplete candidate. It does not activate a
theorem worker, Rust writer, semantic adoption, or production change.

## Original goal and parent roots

The long goal remains a concrete mathematical model and Lean closure of
Yulang type inference soundness, principality and termination, with effect
hygiene treated as a core source-semantic obligation; then a separate Rust ↔
abstract-algorithm correspondence. No source forms, quantifiers, Call/effect
fields, scopes, Value/Computation entries or shared witnesses may be removed.

The immediate parent is `InferenceSoundness` at
`Contracts.lean:128–130`:

```lean
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

Baseline is **0/4 roots closed and 0/5 dependency packages closed**. This
candidate produces no parent-premise reduction.

## Fixed inputs and hashes

```text
Contracts.lean                                      2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e
OriginalSourceSyntax.lean                           3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1
OriginalSourceGeneration.lean                       126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef
OriginalSourceInterpretation.lean                   feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef
OriginalSourceChecking.lean                         a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6
SimpleSubConstraintSyntax.lean                     a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6
Simple-sub top-level principles                  7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81
Source-Generalize selecting authority              46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38
Selected Source-Generalize construction            e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240
2026-10-26 source-generation construction          e9027e317deb5cd5c34cc3892f332a06910a6ff93f1890a82e59faf31d643283
Annotation/effect hygiene policy                  a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18
Source type safety crosswalk                       2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166
Parent reconstruction plan                        7c525a98e53a62a370096d85a3b371af5952dae19d8593b4e02cf3a812c3f36e
PaperExecutionSyntax.lean                          d0dc9871c382ca945059167b8b9e05f8f672170208a994f081e29760a207b87d
```

## Exact output leases

- Primary model candidate: `notes/theory/2026-11-01-abstract-inference-model-r199.md` (frozen hash recorded after review intake).
- Primary sprint contract: `tasks/agent-loop/sprints/abstract-inference-model-r199.md`.
- Primary outcome/activation receipt: `tasks/agent-loop/history/abstract-inference-model-r199-outcome.md`.
- Independent reviewer messages only; Luna records the immutable review receipt after the reviewer returns.
- `tasks/agent-loop/current.json` remains primary-owned; no other path is leased.

## Lanes

**Model/proof lane — Luna primary, candidate frozen.** Build the constructor-
complete model from approved source rules, the Simple-sub structural core and
the selected effect policy. For each constructor, separate (a) original source
rule, (b) actual algorithm constraint generation/phase transition, (c)
independent satisfaction/readout, and (d) theorem application to the unchanged
parent. A theorem worker remains WAITING until a complete model passes review.

**Rust/effect-hygiene implementation lane — no safe edit slice at this gate.**
The next-action audit inspected the clean candidate scheme/receiver owners;
their relevant gates still require authentic annotation/role semantics and
native justification. Existing Rust/runtime UNKNOWN leases remain quarantined.
No production/source write or runtime read is authorized by this contract.
The selected effect policy is fully included in the abstract model, with
permission, inflow, and residual kept distinct. This is not a claim that Rust
implements that policy.

## Model review gate

Fresh independent `compiler_referee` review checks the model's equations,
non-circularity, construction completeness and exact parent cut. A fresh
`spec_auditor` checks source/effect policy conformance. Reviewers are read-only
and may return findings without creating files. Luna writes the frozen receipts.

Review must reject success if any of the following holds:

- an equation equates solving with source typing, admission, reconstruction
  or the desired theorem;
- any of the 13/11/3 original source constructors is omitted or silently
  narrowed;
- the raw `sourceRules/Build/Satisfies` construction is treated as the actual
  Simple-sub generator without a separate correspondence;
- Function effect ports, selected polarity-sensitive annotation behavior,
  symbolic dependencies, complete Call fields, original scopes, or the single
  shared witness are dropped;
- an arbitrary signature predicate replaces an independently specified local
  declaration meaning;
- a transition needed by the actual inference algorithm is absent from the
  model or termination relation;
- a new semantic/architecture choice is adopted without normal review and
  recorded user approval.

**Accepted result for this review:** confirm the exact `MODEL-INCOMPLETE`
boundary and first missing equations. It is not a model-gate pass. If reviewers
find a concrete approved source equation that closes a gap, Luna revises the
candidate, rehashes, and requests delta review before any proof activation.

### R200 bounded construction delta

The primary added §4.1 to the candidate, mapping all eight raw source literal
constructors losslessly to `PaperTypes.Literal`. `PaperTypes.literalType` and
`PaperValueTyped.literal` give a candidate type/value projection without
payload narrowing. The delta explicitly leaves the original descriptor/value/
root/event readout, literal Return, contextual effect, and actual Simple-sub
generator/solution equation open. No source rule or semantic choice was adopted.

Fresh exact-hash read-only `compiler_referee` and `spec_auditor` delta reviews
both passed the wording-repaired candidate at SHA-256
`f60b89d98ced17cabf860c6dd65aa3929796c85a407c8f82af25607adf0017cb`, with no
remaining findings. Both confirmed `MODEL-INCOMPLETE`, zero parent reduction,
and no activation. The earlier minor finding that the displayed implication
was only the immediate `LiteralAtom` bridge was repaired by leaving Return and
effect premises explicitly open; Bool was added to the payload-type list.

The R200 candidate delta was reviewed against baseline
`2ecc95edb7282a387b288d27968148c3be6a82dc`. `PaperExecutionSyntax.lean` is pinned at
`d0dc9871c382ca945059167b8b9e05f8f672170208a994f081e29760a207b87d`.
No Lean/build/test or runtime was run, and no new environment or storage was
created. Existing dirty/untracked/quarantined paths and UNKNOWN leases remain
untouched.

## Resource and stop envelope

- Total primary + review wall: at most 3,600 seconds.
- Maximum assignments: primary plus two fresh reviewers; zero Astra.
- No Lean, Lake, Cargo, build, test, new environment, target, cache or scratch.
- Preserve every pre-existing dirty/untracked path and every UNKNOWN lease.
- Existing user capacity-release receipt is already applied; do not count its
  slots again and do not treat it as writer cessation or path release.
- Stop model selection at an approved-meaning conflict, missing genuine local
  law, altered challenge/domain, witness duplication, changed scope, or any
  semantic decision outside the current authority. Record `MODEL-INCOMPLETE`
  and preserve parent delta zero.

## Success, falsifier, next boundary

This sprint's only review milestone is an accurately audited candidate and
exact first missing equations, or—if all equations are constructively fixed—a
fresh review pass of the complete model. A source-qualified satisfying
assignment that fails an original constructor/effect rule, changes owner or
event, loses symbolic dependencies, or cannot produce the same witness
falsifies the proposed model.

Only a fresh model-gate pass admits the first parent-applicable proof packet.
The initial proof target is the all-payload literal constructor implication,
then Lambda annotation/entry with the already fixed effect-hygiene policy.
The next dispatcher consultation is after complete-model review, an approved
authority conflict, or a resource boundary; routine drafting/review intake
does not trigger another round.
