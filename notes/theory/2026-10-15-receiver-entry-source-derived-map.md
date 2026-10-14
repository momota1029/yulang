# Receiving-entry source/native correspondence: the first missing interface

Date: 2026-10-15
Status: bounded constructor derivation; reviewed with one authority wording repair integrated; source/native bridge OPEN
Baseline: `28fd565e7144373ce5cd19d5e8fa6cff673087cf`
Branch: `research/simple-sub-intrusion`
Lease: this file only; constructive leaf; frozen on handoff
Parent: H1/H2/U OPEN; H3/P disabled; no production or theorem promotion

## 1. Frozen statement, scope and authority

The original parent ranges over every admitted shallow Catch, its original
scrutinee, formal and arm binders, providers, complete Call and future interfaces,
raw resumptions and residual lineages, under **one original scoped assignment
sigma**. Its consumed, protected, unmatched, outside-arm and raw-resumption
contributions retain their required meanings. This packet neither narrows that
domain nor changes its quantifiers.

This bounded question is whether current HIR/native constructors instantiate
the selected source Call semantics for each executing occurrence of an
original receiving call `C_in`, separately from its static Lambda/formal/
profile template. The required native correspondence includes the occurrence,
query-compatible boundary/receiver fields, received/captured/returned typed
views, matching Receive/Observe/current roots, and exact return/re-entry
lifetime. Boundary/query field names below describe the existing consumer's
input shape; they do not introduce a new source semantic object or token. All
original scopes and binders must remain fixed under sigma; no independently
chosen endpoint witnesses, solved rows or canonical equality supply incidence.

The derivation below assumes authentic successful LocalSource formation and
resolution for the displayed source shapes, enabled candidate graph effects,
successful fallible collection/admission, and an actual matching positive and
negative Function pair when its dispatched children are discussed. Those are
explicit local constructor hypotheses. They do **not** assume full source
typing, a satisfying sigma, complete Call admission, execution, a received
boundary, a typed profile instance, a receipt or an event. The conclusion is
the emitted static prefix and its first unsupported transition. This is not a
third transport theorem conditional on supplying that transition.

Authority and dependency roles:

- [Inferred call views](../design/2026-10-05-inferred-function-call-views.md)
  §§1–3: source formation and one joint assignment; static slot and executing
  boundary differ. Section 2 expressly leaves exact generation judgments open.
- [Directional addendum](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
  §§2–4: selected original upper `ResultEffect` only; preserve inherited
  protection and introduce no provider/lower-output backflow. The introduction
  does not itself establish protection of a concrete event.
- [Top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
  §§1–3: generate and accumulate ordinary constraints without waiting for
  execution or solving their final types.
- The authoritative [original Call formation](../design/2026-10-07-original-call-formation-definition.md)
  §§2–4 selects `OC-CallEff` for actual emitted Gen-Call-0 records and maps
  their invocation root to the complete `J_call`/`ExecuteCallable` interface,
  including actual entry, body, designated consumers and native-return
  delimiters. The authoritative [complete Call contribution](../design/2026-10-07-complete-call-contribution-definition.md)
  §2 selects `C-Inv`/`InvMem` and `C-Call`/`CallMem`, retaining actual
  receiver role/entry, whole carrier, current provider/world, ordered pending
  suffix, result and future interface. The authoritative [source Call
  interfaces](../design/2026-10-08-call-source-interface-definition.md)
  §§3–4 and [source-frame construction](2026-10-08-call-source-interface-construction.md)
  §4 construct `FrameCall` with its dependent receiver
  `IF(ExecuteCallable(actual_f,arg,current_C1))`, full result/future slots,
  and source/operator origins. These are selected source-semantic suppliers,
  not current HIR/native production correspondence or cutover authority.
- [Charter](../design/2026-09-29-scc-intrusion-redesign-charter.md)
  §§13–15 selects typed-value transport/lifetime and shallow raw-resumption
  behavior. [Typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
  §§2,4,6 and [source owner](../design/2026-10-02-typed-source-owner-realization.md)
  §§1–3,5 are **Draft realization candidates**. Their decorated-machine
  transitions are compared as targets, never premises about actual source.
- The reviewed [entry bridge](2026-10-15-receiver-entry-source-bridge.md) and
  [falsifier](../progress/2026-10-15-receiver-entry-source-falsifier.md) at this
  baseline are prior bounded results; their conditional examples remain
  conditional. Their artifact headers do not record the later review; the
  primary's packet supplies that review status for this assignment.

The source-level Call and receiver semantics are therefore not missing from
the selected mathematical direction. No runtime representation, activation
token, profile-position expansion, grammar, production mechanism,
ordinary-inference restriction or parent status is selected here.

## 2. Reachable constructor prefix for relay

Use the source shape

```yulang
my relay cb = catch cb() { v -> v }
my provider ignored = 1
my answer = relay provider
```

This is a bounded **source-constructor trace**, not an executed program trace
or a complete source-typing theorem. Fix `O` = relay's definition root, `L` =
its original Lambda, `f` = original formal cb, `H` = its Catch, `z` = the
original arm binder v, `C_cb` = cb(), and `C_in` = relay provider. Let `s_f`
and `s_z` be their retained original scopes. The following output derivation
uses their authentic identities, without replacing either binder by a row.

1. **Lowering and resolution.**
   `yu-hir/src/module/local_source.rs:115–181` distinguishes Lambda, Apply,
   Catch, Parameter and CatchBinder. At `:640–684` empty cb() creates separate
   Apply and Unit slots. Thus cb's use resolves to f and the arm use v resolves
   to z; neither is resolved by a successful Function comparison. Exact parsing
   of this composed spelling was not run. Existing value-Catch fixture bodies
   at `candidate_catch_value_source.rs:108–145` support the individual binder,
   callable and effect-preservation shapes, not this program's execution.
2. **Original template.**
   `candidate_source.rs:260–285,327–334,382–407` registers O/L/f and its
   original scope, joins cb's Name to that registration and retains omission
   before visiting the Lambda body. The Parameter endpoint for cb is that
   original formal endpoint. This is an actual static constructor output;
   it is not a completed semantic protection profile or a dynamic receiver.
3. **Callback demand.**
   `candidate_source.rs:604–621` emits the original C_cb Apply recipe and
   checking/cause. `shadow_apply.rs:1432–1544` validates that join and builds
   `U_cb = Function4(a_unit+, E_unit+, e_cb-, r_cb-)`, where a_unit is the
   original Unit expression's Value endpoint (with its own Unit bounds),
   `e_cb` its fresh inference invocation-effect row and `r_cb` its result
   endpoint. No inference endpoint is identified with the Unit leaf. The actual
   symbolic DirectionalIntroduction retains `(O,L,f,s_f,C_cb,U_cb,
   ResultEffect,e_cb)` before admission of `f+ <= U_cb`. Omitted-formal
   provenance is not recreated from a provider's type. At `:1566–1584`,
   callee evaluation effect and e_cb flow into C_cb's application effect.
   No claim identifies the inference row e_cb with an execution occurrence.
4. **Catch binder and result.**
   `candidate_source.rs:366–369,422–430` schedules scrutinee collection before
   the arms and maps z to the **original scrutinee endpoint** r_cb. At
   `:353–356` the arm Name's endpoint is replaced by that exact binder map;
   `:517–537` emits `r_cb <= r_H`, the scrutinee application-effect inclusion
   into E_H, and the arm's own effect inclusion into E_H. There is a value
   arm, so the additional no-value-arm fallback at slot 52 is absent.
   All arm constraints are still generated. No row subtraction or dynamic
   handler selection occurs in this construction.
5. **Lambda and receiving comparison.**
   `candidate_source.rs:659–675` retains L's body/root/parameter recipe.
   `lib.rs:11254–11420` emits
   `F_L = Function4(f-, entry_L-, returned_L+, r_H+)`, with
   `entry_L <= returned_L` and `E_H <= returned_L`, retaining inert
   InferredEntryOrigin/FormalConstruction where applicable. C_in constructs
   its separate upper demand
   `U_in = Function4(provider+, E_provider+, e_in-, r_answer-)`.
   For an actually propagated comparison `F_L <= U_in`, the children at
   `lib.rs:12551–12579` include `provider+ <= f-`,
   `E_provider+ <= entry_L-`, `returned_L+ <= e_in-` and
   `r_H+ <= r_answer-`. These are the exact structural receiving Argument
   edge and complete four-field obligations. `:12701–12724` admits each
   Function child before enqueue. Stored or dispatched constraints alone
   establish neither full Call meaning nor activation/complete future replay.

This prefix is source-directed and preserves original binder and field
incidence. The same sigma interprets every endpoint; it is never chosen
separately for the provider, formal, Catch arm or result. It establishes no
global source adequacy or satisfiability claim. The current Apply inputs even
retain `ReceiverDispatchAndCompleteResultFutureInterfaces` as a pending
supplier (`candidate_call.rs:135–145,269–300`).

The receiving invocation, if executed, is relay's occurrence, not the static
L, C_cb, or provider's own invocation. Using cb as callee does not make the
provider invocation receive cb's public callee view. The selected transport
principle preserves each actual argument and private captured view separately.
Returning z exposes the callback's **result** correspondence. It cannot copy
cb's outer call-effect profile onto an unrelated latent position in z. Even
when a callback returns a callable, no additional nested protection position
is introduced by this derivation.

## 3. First unsupported source/native transition and actual consumer

The selected source semantics already defines receiver entry and return
conditionally through `OC-CallEff`, `C-Inv`/`InvMem`, `C-Call`/`CallMem`, and
`FrameCall`. The first unsupported step in the **current implementation
correspondence** is to instantiate those judgments from an authentic HIR Apply
and native `CandidateSourceCall` input, then connect their actual receiver
observation to the typed profile/Flow/Observe/Receive/current-root evidence
consumed below. In particular, the actual emitted Gen-Call-0 record and its
complete interface remain required source inputs; a `LocalSource::Apply` or
structural Function4 comparison alone is not that record.

The still-required native evidence mapping is:

> Given the selected source `FrameCall`/`J_call` derivation for `C_in` and
> `f`'s source template, relate its particular receiver execution to the
> existing consumer's occurrence and boundary fields. Bind the received view
> along its original typed correspondence under sigma, establish the matching
> profile/Flow/Observe/Receive and current roots, and align normal completion
> with expiry. Symbols such as `a`, `b`, and `original_receiver` below name
> those required native fields; they are not new source constructors.

This is a missing **source-semantic-to-native constructor/consumer
correspondence**, not a missing source-level Call rule or equation between
effect rows. `candidate_call.rs:131–175,269–300` explicitly retains
`OriginalGenCall0` and `ReceiverDispatchAndCompleteResultFutureInterfaces` as
pending suppliers; the current candidate input is not an established instance
of the authoritative `e`, `Q_e`, `FrameCall`, or `J_call` above. At the native
side, the existing original-entry record is inert (`candidate_context.rs:157–171`);
FormalConstruction is not a callback contract or runtime receipt
(`:274–282`). Neither the Lambda's `returned` row nor solver recipe completion
represents normal source return. The selected source judgment can be mapped
without running the program during constraint generation, but that exact
mapping remains unproved.

The authoritative source definitions also fix behavior that the earlier
version of this note incorrectly treated only as a Draft target: complete
receiver entry/body/designated-consumer/return ordering, actual provider/current
world, raw pending suffix preservation, current-state resumption and no receipt
replay. Those source facts must now serve as premises for the native bridge.
The identity-qualified `Owner`/`Bind`/`View` realization and concrete typed
receipt records remain Draft candidates and cannot replace that bridge.

The tempting *concrete realization* in
`typed-computation-core-elaboration.md:928–959` starts with “enter actual
receiver; establish its source boundaries and receipt,” followed by entry
force, typed rebind, body and return. That document is Draft, and §2 (`:64–83`)
already takes Flow/receipt derivations and original annotation positions as
inputs. The authoritative `J_call`/`FrameCall` suppliers establish source-level
receiver execution and its ordered return interface, but they do not identify
the current compiler's typed boundary/receipt fields with that contract. The
Draft equation therefore remains a possible concrete target, not the source
premise for this mapping. The Draft owner machine likewise starts from a
decorated graph stronger than parsed source
(`typed-source-owner-realization.md:20–32`).

At the current native seam, the original Apply Value pair has no closed
Allowance: `candidate_context_source/seed:2683–2738` consequently supplies
IDENTITY. `candidate_context_execute_relation:2964–2977` returns false there.
There is no new receiver interpretation in this trace. This is a static
transition calculation, not observed incorrect protection.

The candidate target consumer is
`yu-core/src/shadow_typed_evidence.rs:92–148`. It requires exact supplied
profile→Flow→Observe/Receive port matching plus current handler, handler-owner
and immutable original-receiver roots. Its constructor validates wiring, not
source derivation (`:1–12,26–84`); the result is Assumed. The first input row
above is unsupplied, so this packet does not instantiate that query.
In particular, no supplied-token boolean calculation is substituted for any
source entry, typed path, receipt, observation or current-root proof.

## 4. Alpha-return/beta-enter discriminator: qualification boundary

The prior falsifier's spelling remains unqualified as a current source/native
instance:

```yulang
act signal:
    our ping: int -> int
my receiver f = { my step x = f x; my ignored = f 1; step }
my old = receiver signal::ping
my later = receiver old
```

Its intended alpha entry captures f in returned step; a later beta entry
receives old and invokes alpha's capture. Actual collection supports the
individual Lambda/Block/captured Name/Apply/operation shapes. This does not
prove the composition's parsing, successful admission, full typing or
evaluation. In particular, alpha first calls signal::ping. No supplied source
handler/response derivation establishes that this request returns and alpha
reaches step's return. The claimed alpha-normal-return/beta-entry sequence
therefore remains **unconstructed**. The two displayed receiving calls are
also distinct static C_in occurrences, despite sharing receiver's template.

The selected source `J_call`/`FrameCall` semantics includes actual receiver
execution and invocation return, so the abstract source relation can state
this sequence under its complete-input and typing premises. This note does not
construct those premises from the displayed HIR program or map its dynamic
occurrences, receipts and typed views to the native query. The exact
whole-program admission/typing and source-to-native operational sequence
remain unproved. Purity of the provider does not supply that correspondence.
This spelling neither proves an escaped old boundary nor replaces the
original capture candidate.

To state the requested **same receiving-call** discriminator precisely,
consider this separate candidate locator:

```yulang
my relay cb = catch cb() { v -> v }
my provider ignored = 1
my enter cb = relay cb
my first = enter provider
my second = enter provider
```

The one Apply `relay cb` in enter is C_in for both proposed executions.
The intended finite control prefix is alpha-enter(C_in), callback completion,
value-arm completion, alpha-return, beta-enter(C_in). At the latter point an
old alpha boundary, if retained anywhere, must still reference alpha rather
than beta. The static C_in/L/formal template is identical for both entries.
This is the required discriminator **specification**, not a proved
source/native trace: the authoritative source semantics provides its Call
entry/return clause, while authentic lowering to that source frame, exact
whole-program admission/typing, and the native typed-view/receipt/current-root
mapping remain unproved. Purity of provider does not supply that mapping.
This spelling neither proves an escaped old boundary nor replaces the
original capture candidate.

Thus the reachable evidence is the original source-generation prefix and its
receiving Argument edge, not an established alpha-return execution. No
identity-collapse counterexample to actual compiler behavior is claimed.

## 5. Required raw shallow-resumption native mappings remain open

The authoritative complete Call clauses and charter §§14–15 already constrain
source-level pending suffix behavior: resumption uses current state, does not
replay receipt, and does not reinstall the consumed shallow handler. The
following exact raw-owner/profile mappings into the current native consumer
remain unconstructed; they are not fresh assumptions fed to the conditional
query.

| Required case | Selected source contract | Missing native source correspondence |
| --- | --- | --- |
| Resume while the saved executable owner is still active | Charter §§14–15 and `C-Call` preserve the current continuation/state and do not reinstall the consumed shallow handler or replay receipt. The selected lifetime behavior preserves the still-live owner's identity and activity. Borrowed enter/leave is the Draft owner realization being checked, not an approved concrete mechanism. | Raw Function4 construction has no source-derived mapping to the active owner/current-root and historical receiver fields consumed by the native classifier. |
| Resume after the saved executable owner has expired | Expiry removes protection authority while preserving origins/events/latent effects; the saved continuation uses its current resumed state and original ordered suffix. Any fresh executing receiver must be distinct from the expired receiver. | No native source record maps the saved span, alpha expiry, beta current receiver and exact completion delimiter together. |
| Retain old boundary identity through either case | The selected typed-lifetime contract preserves historical receiver identity and forbids reactivating it through a new current receiver; raw resumption does not recreate the old entry. | No source-produced native profile/receipt packet binds the historical receiver to exact typed paths, events and current roots. |

The historical-identity requirement is orthogonal to the Draft's borrowed/fresh
owner realization alternatives.
Draft source-owner §§2–3 offer a concrete Owner/View realization, but this pass
does not derive its native constructors from admitted relay/Catch source.
The actual `candidate_effect.rs:806–863` constructor pairs response ports,
returns the original scrutinee value and conservatively retains full-S
effects; it explicitly reinstalls no handler. Inspected raw-continuation
fixtures (`candidate_operation_catch.rs:24–100`) assert those provisional
typing constraints and leave capture eligibility/residual removal open.
They do not furnish source execution, owner activity or typed observation.
Consumed shallow h0 must remain gone; saved reachability cannot make it or
an old receiver active. All raw-resumption, consumed, protected, unmatched
and outside-arm parent contributions remain required and OPEN.

## 6. Economy audit and one next action

The reviewed entry bridge and complementary supplied-evidence falsifier both
leave the same source/native correspondence premise untouched. This packet
adds the authoritative Call/receiver suppliers to the dependency map; it adds
no equivalent conditional transport lemma.

Correct receiving incidence, live observation and expiry are A/B requirements
for the selected behavior. Original formal/scope/field recovery would be D:
the actual constructors already retain those facts and §2 uses them directly.
The source Call/receiver semantics is already selected; the missing A/B bridge
is its authentic source record and complete frame into the current HIR/native
producer and context consumer, with typed incidence and lifecycle preserved.
This audit neither reclassifies a required gate nor establishes impossibility
or a new semantic decision.

**One next action:** derive the source-to-native bridge from the authoritative
`OC-CallEff`/`FrameCall`/`C-Inv`/`CallMem` constructors to the exact
`LocalSource`/`ApplySourceInput`/`CandidateSourceCall`/native Function4 owner.
It must establish the matching typed profile, event observation, received
view, current roots and expiry under one sigma. Recheck whether the same-call
alpha-return/beta-enter and raw-resumption obligations follow at that bridge;
do not add another Call semantic rule or resume protection implementation on
inert metadata alone.

## 7. Checks, resources and commit packet

Method: one static bounded constructor/consumer derivation, at most 25 minutes;
one leaf, zero descendants. Commands: `git rev-parse HEAD`, branch inspection,
focused `cat`/`sed`/`rg`, read-only Python SHA-256 comparison of dependencies
against `git show <baseline>:<path>`, and artifact whitespace/hash checks.
Initial aggregate captures were truncated; decisive sources were reread in
bounded ranges. Guessed `spec/` and `crates/yu-vm` paths were absent; no claim
depends on those searches. Inspected yu-core exports and the yu-backend-vm
boundary are not a whole-repository evaluator absence proof.

Zero Cargo, tests, builds, executable semantic probes, measurements or samples.
No source program was parsed/inferred/executed by this worker. CPU/RAM and
exact elapsed use were not measured. Primary retains verification ownership.
Requested normal route: prover, gpt-6.1-sol/high. Actual role session is this
constructive leaf; effective runtime model/effort metadata is unavailable
(unknown). Config registers the unpinned prover with Sol/high subagent
defaults; that is not runtime override evidence. No Astra or nested launch.

Unverified scope: exact whole-program source qualification for both composed
discriminators, full Call/future interfaces, all typed capture/store/return
maps, source profile formation for unknown shapes, raw re-entry, real event
and handler ownership, generic arms, all-path replay/lifecycle, abnormal
publication, hygiene, soundness, principality and production/F5 cutover.

Commit packet:

- Exact leased/changed path: `notes/theory/2026-10-15-receiver-entry-source-derived-map.md`.
- Baseline: `28fd565e7144373ce5cd19d5e8fa6cff673087cf`; confirmed before reads.
- At dependency check HEAD had advanced to
  `43d0ad5619d28503a9b06429717a78723690d858`; all 33 direct dependencies
  below still matched the baseline byte-for-byte. Changed dependency hashes:
  none. No moving dependency edit was consumed.
- Honest status: initial semantic and authority reviews missed omitted
  authoritative original-Call/receiver definitions; primary repaired the
  source/native framing. The focused delta review found one authority-boundary
  overstatement about Draft borrowing; that wording is corrected below. No
  parent promotion.
- Checks already run: baseline/branch confirmation, exact dependency equality
  and SHA-256 pins; static whitespace check recorded at handoff. No executable
  source or compiler check.
- Proposed checkpoint message: `research: bridge selected source Call semantics to native receiver evidence`.
- Shared-record delta for primary/curator: preserve the static cb Apply/Catch-
  binder/scrutinee/receiving-Argument prefix; source `OC-CallEff`/`FrameCall`/
  `C-Inv`/`CallMem` semantics is already selected; the actual HIR/Gen-Call-0
  to native typed evidence/current-root/expiry correspondence remains open.
  Alpha/beta and raw resumption are unqualified at that bridge. Keep H1/H2/U
  OPEN and H3/P disabled.

### Direct dependency SHA-256 at the pinned baseline

```text
8b418f8ed02606205ecdfedcf5da72dae074e1c799237b8cc034fdfbd71ab7a1  rules/agent-orchestration.md
3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69  rules/research-lab.md
e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1  rules/design-authority.md
4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9  rules/compiler-engineering.md
2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6  rules/git-concurrency.md
a0a114b589e8920af8e8fd871d15f63d68b735fc1a553f5a89952b1eab8489e5  rules/orchestration-budget.md
993d4c2a7743669b4c7a6c46f054c4caae492873f0a5f20a1ea566ebf9dea3c1  .codex/config.toml
485a26c7409e16c692ad10095031ab0e7084726ec5da5666082b3bbc4a5daf98  .codex/agents/prover.toml
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
4940e031b83d3d0315f17beb51ba2e952ec64ae7d57d9ae0d086024c7305ca9f  notes/design/2026-10-07-original-call-formation-definition.md
4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e  notes/design/2026-10-07-complete-call-contribution-definition.md
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c  notes/design/2026-10-08-call-source-interface-definition.md
278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98  notes/theory/2026-10-08-call-source-interface-construction.md
ead206bff341c82993acbaecda25ae1d3a760397796bbbbb53ba3ef917a53fb1  notes/theory/2026-10-07-owned-call-contribution-construction.md
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1  notes/design/2026-10-05-inferred-function-call-views.md
6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7  notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md
1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb  notes/design/2026-10-02-typed-boundary-realization-draft.md
5cbd8110736ee4d43e0c65460fa9ecf700228bfdbe9fbaa7642ea0302d86f1aa  notes/design/2026-10-02-typed-source-owner-realization.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e  notes/design/2026-10-02-typed-computation-core-elaboration.md
b6d6598c08ed920536ecf3ca9ef4a015a64e51ffa0f149f097aad7ba55089e68  notes/theory/2026-10-15-receiver-entry-source-bridge.md
a14e5b71f3bff5da6be5b7ce4028a87d2b1a0c8398bcad19d27de31a5516fb13  notes/progress/2026-10-15-receiver-entry-source-falsifier.md
afc91346af535529f973421bdbe2a43520c98946097cae545e4ae1a665146074  crates/yu-hir/src/module/local_source.rs
32a6d875b9e89af8192cf017fbeccc95e9648223490d72de64a6957c97aa6e1b  crates/yu-solver/src/candidate_source.rs
cc5778b936a5495182c08d4853ab9ef006d079df5e169dd94df629c2d82f3199  crates/yu-solver/src/candidate_call.rs
831dc28b977a5e01e6f0ef0faa795495d78ecb2cc01678db48e9cf7ea5132eac  crates/yu-solver/src/shadow_apply.rs
f414efa7efdb17644f4dfa6b0bba621c1bb7cccd0f83735c33a0acb875da6b91  crates/yu-solver/src/candidate_effect.rs
6301ca80eec137df3f2c2c44e2edaa7dbdf1ed7a78c69617228888e63654e461  crates/yu-solver/src/candidate_context.rs
e902da1c9a7f0fb4dcd806c87563d1ae46d35bbb999e69b7fee51c3c0f6e4bf5  crates/yu-solver/src/lib.rs
dabcbd07b2d1baace0227cb94164db871fdadc1089b1854b396dfb464d26ce95  crates/yu-core/src/shadow_typed_evidence.rs
3a2c2befd0dd38df3c06458a7fd918b8f32124a75d264ed51d859ec036c4ab5e  crates/yu-core/src/lib.rs
7a52b6e5f77b6f1c8ba9f590c4327a151381cfe254fc52c843a6421189666ad5  crates/yu-backend-vm/src/lib.rs
449e254d4ea61a14e2713c2434734cb317f4da34dff0515b65090e37d0d3f60f  crates/yu-solver/tests/candidate_catch_value_source.rs
8c580da56de25c76146073919840f6d15dec3b11a53c0787309a082dc59e5484  crates/yu-solver/tests/candidate_operation_catch.rs
```
