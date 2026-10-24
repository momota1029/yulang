# LEAN-COMPLETE-CALL-20261025/r8 — checked Call representation and proofs

Status: **FROZEN** by Luna. This is a fresh 6,600-second research sprint; no
r7 grant carries over. Branch `research/simple-sub-intrusion`; baseline commit
`dc6088c8e0b00248f0c14043f3cdb1e129ce6b92`, pushed to `origin` before this
contract. Contract SHA-256 is recorded in `tasks/agent-loop/current.json`.
This contract changes no Yulang semantics and authorizes no compiler or
production change.

## Original outcome and success evidence

The unchanged parent is complete Lean proofs of Yulang semantics and type
inference under `notes/theory/lean`, with primary-owned reviewed commits and
pushes. The original inference A/B, source/native correspondence, principality,
termination, and the full parent remain OPEN.

R7 preserved an unaccepted representation candidate, then failed the first
pinned Lean check: `CoreSyntax.lean`, exit 1, 3.55s, 33 elaboration/type
diagnostics. Its exact failure receipt and hashes are in
`tasks/agent-loop/sprints/lean-complete-call-20261025-r7-outcome.md` (SHA-256
`892aff9b3005cf6620802555924767968ea4db63914687493f197d3e1c0afa37`). R7
proved neither proposition. R8 first repairs those elaboration failures without
changing the representation's meaning, freezes and checks its full dependency
component, and then attempts the exact Call context and finite-prefix claims
below. An unelaborated or vacuous no-`Bad` result is not success.

### Governing source and fixed Call order

The semantic authority remains `docs/yulang-operational-type-safety-ja.tex`,
especially §§ “値と計算”, “型付け規則”, “call の入口と adapter”, and “View、
transport、受領を生成する全規則” at lines 145–245, 362–400, 535–602,
1029–1044, and 1231–1266, plus `rules/design-authority.md`. The
review-pending V1–V7 outline is not a premise.

For `Call(f,t)` with `f:C(A,B)` and `t:UA`, retain the source sequence and
data: choose one fresh receiver and enter its Scope; peel wraps outermost to
innermost using that owner; keep each argument adapter inside the inert
`Delay(let z <- Force t in a(z))`; attach the source lambda receipt to its
designated carrier paths before the first force; Value entry forces the
received carrier and Computation entry substitutes it without forcing; execute
the typed body and declared-result consumer; run pending result adapters
inner-to-outer under the complete Call View; on normal return leave Scope while
retaining returned value views and latent code. Req/Fail remain in every
admitted body/adapter grammar that contains them. Requests retain their
operation instance, value payload, response-typed continuation, observed
event-time Views, Call context, Scope/View context, world, and literal old
suffix. Fail retains its reason and only the existing source cleanup relation.
No new observation or cleanup policy is allowed.

The formal result is still only a bounded typed Call component with explicit
metadata inputs. Full decorated-plan authenticity, effect hygiene, all-source
View/eligibility/current-world coverage, frontend construction, native
correspondence, and arbitrary foreign-tail safety remain OPEN. A type equality
does not authenticate receipt slots, interface path correspondence, captured
Views, fresh-owner evidence, or a source plan.

## Exact propositions

The r7 proposition claims and their quantifiers are unchanged. Names below are
frozen for r8; helper signatures are written against the checked r8 interface
and may not weaken them.

### P — `call_context_plug_typed` (`CallPlugging.lean`)

For each actual `TypedCall.ContextTyping env frames holeType resultType`
derivation and every computation typed at `holeType`, plugging that computation
into the represented context yields a computation typed at `resultType`.
Provide inversion over that same judgment so the proof can recover the actual
hole and typing derivation, pending delayed argument adapters, body/result
consumer, pending result adapters, Scope/owner, receipt/View inputs, and the
independently typed literal Control suffix. Use actual syntax and typing
constructors. This is a supporting proposition, not the old parent A and not a
same-body safety assumption.

### Q / unchanged Proposition A — `call_step_typed_or_handoff` and
`call_context_plug_preservation` (`CallContext.lean`)

For every typed represented Call context, classify each actual active-computation
or administrative Call transition. An internal successor retains the typed
context and result type, the literal suffix, and the exact source-prescribed
world transition; a Ret/Req/Fail handoff retains the result type, resulting
world, and literal suffix. Prove this from the checked syntax, actual
substitution and P, with no `BodyLaws`, assumed Call preservation, or assumed
substitution theorem. Export the unchanged A theorem
`call_context_plug_preservation`, including the actual context plug/inversion
and one-step obligations. P and Q together are Proposition A; neither alone
closes it.

### B — unchanged `bounded_call_finite_prefix_safety` (`CompleteCall.lean`)

For every closed represented typed Call configuration, every independently
typed arbitrary old Control suffix, and every actual finite Call-internal
prefix through its first explicit handoff or represented Ret/Req/Fail terminal,
preserve the typed Call-context judgment, result type, literal suffix, and
source-prescribed world behavior; prove every state in that prefix is not
`Bad`, with exact prefix/exit arithmetic. Use Q's exact frozen A declaration
and dependency hash and classify every actual successor. Do not claim safety of
foreign suffix execution after handoff.

The no-`Bad` result must be connected to actual represented execution and
source constructors. It cannot be discharged solely because `CallHead` lacks
a `bad` constructor, because a typing index rules `Bad` out by definition, or
because no transition was provided. Establish the actual Call-step/start
coverage and typed state/transition relation used by the prefix theorem. If
this connection is absent from the frozen interface, B is blocked and Luna
records the exact source/formal obstruction; do not relabel a vacuous statement
as safety.

Keep Req/Fail cases whenever admitted syntax can reach them. A standalone
constructor or request/failure record does not prove reachability. If an exact
source-required transition cannot be represented or proved, stop with its
source locator and counterexample. Keep all r6 public theorem statements and
their transition meanings unchanged. No assumption, hidden premise, proof
hole, unsafe proof, `native_decide`, V1–V7 premise, semantic weakening, or
source-domain narrowing is allowed.

## Frozen dependency component

Luna revalidates every entry at dispatch, after the repair freeze, before
proof dispatch, and before review. These hashes are the baseline inputs; the
five r7 candidate modules below are permitted repair outputs and must receive
fresh interface hashes in the implementation handoff. A changed non-leased
dependency returns to Luna; authors do not expand leases.

| Input | SHA-256 |
|---|---|
| `AGENTS.md` | `69e24ca7bc987f0fa646145751e966f740f6774ef357082078a20030c50c89ae` |
| `AGENTS.pre-sprint.md` | `34b8b8169696dcc6a0899204226914d250ddecf6782d14be670b7b2d5352c562` |
| `rules/goal-driven-sprints.md` | `e50f5d4f79814c87af56e7dc34ddb6ab968abb523826c72ecdc40a8920397c0a` |
| `rules/design-authority.md` | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` |
| `notes/design/2026-10-16-goal-driven-sprints.md` | `2dfeb555c913d3142078de535ee4b7f68e9a27f2b91a5f0bb82d4d867db4fc4e` |
| `.agents/skills/yulang-sprint/SKILL.md` | `b6f4a50703928020607edebe1c8b138fb98a0378220f00b7c190dba9fc068515` |
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `notes/theory/2026-10-24-corrected-core-value-continuation.md` | `4d8ffd63cbb65cd6917145fa31a4cb3f04656a19f7b71fd0e3fdd6cecaabfbeb` |
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/YulangClosure/CoreSyntax.lean` (r7 candidate) | `0250b51b7b97a98e52b76e3785a7341f2b454a422016c6945d7d6c4190804b07ff` |
| `notes/theory/lean/YulangClosure/CoreSubstitution.lean` (r7 candidate) | `fc73d6d60d28f2abb54049a5715751d27df47ad93dbeb8f52966cf98a747bd2f` |
| `notes/theory/lean/YulangClosure/CoreExecution.lean` (r7 candidate) | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `notes/theory/lean/YulangClosure/CoreComposition.lean` | `1527cd3c5961b413ec2b97495744b218aba6247956881318485364d15065294c` |
| `notes/theory/lean/YulangClosure/ControlSyntax.lean` (r7 candidate) | `94d9b59e7cc69dac98de9797c7627a571554b859e3906c7c1ca94881d9482864` |
| `notes/theory/lean/YulangClosure/ControlTyping.lean` (r7 candidate) | `163c191584b6abb462c1e5e190bb2105d6ec3c4f0512568e87570b89ff00ffd8` |
| `notes/theory/lean/YulangClosure/ControlComposition.lean` | `9a48a5f2ef15eb947478757e0fa74457579183ccdbab90f2518886590e33fc40` |
| `notes/theory/lean/YulangClosure/CoreControlBridge.lean` | `30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a` |
| `notes/theory/lean/YulangClosure.lean` | `04a209f4aa4a9e8c2848aee11eb16befb6fe4e0b566d4683dd0705f96ccf3b2f` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| r6 accepted outcome | `b6def9a2c248ccbd7a8bda1cba9489b6dab84abd8a9131f0b24ce573e0eefd4a` |
| r7 failed outcome | `892aff9b3005cf6620802555924767968ea4db63914687493f197d3e1c0afa37` |

Pinned Lean is 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`). One Lean
process at a time; `-j1 -M1024`; each invocation has a 120-second ceiling.

## Assignments, exact leases, and staged grants

All authors are fresh r8 assignments. The previous r7 workers are STOPPED and
their grants remain charged. The first issued assignment is only implementation
repair, capped at 1,200s. Later grants are gated as specified below.

### Implementation repair — Luna/high, maximum 1,200s

Exact write paths:

- `notes/theory/lean/YulangClosure/CoreSyntax.lean`
- `notes/theory/lean/YulangClosure/CoreSubstitution.lean`
- `notes/theory/lean/YulangClosure/CoreExecution.lean`
- `notes/theory/lean/YulangClosure/ControlSyntax.lean`
- `notes/theory/lean/YulangClosure/ControlTyping.lean`
- `notes/theory/lean/YulangClosure/ControlComposition.lean`
- `notes/theory/lean/YulangClosure/CoreControlBridge.lean`
- handoff only: `tasks/agent-loop/inbox/20261025-lean-call-implementation-r8.md`

Repair the observed elaboration issues and resulting Lean errors: remove the
unused `CallType` decidable-equality derivation or provide an equally lawful
structural solution; put `PortPath` before `ViewOccurrence` and `Adapter` before
`InterfacePlan`; replace reserved `instance` identifiers consistently; split
syntax from Prop-valued typing declarations where Lean's Prop elimination
restriction requires it without changing typing claims; correct request
payloads from computation to value at `requestScope`, `requestExpose`, and
`finishRequest`; fix resulting compile errors. Preserve every source-order,
typing, substitution, metadata, world, Req/Fail, and suffix claim. Do not change
semantics or proof obligations. Stop and report exact source/formal evidence if
a semantic decision is required. The author does not run Lean or Git; Luna owns
serialized checks. Freeze one coherent handoff and stop before verification.

### P — Sol/high, maximum 1,200s; launch only after representation checks

Exact paths: `notes/theory/lean/YulangClosure/CallPlugging.lean` and handoff
only `tasks/agent-loop/inbox/20261025-lean-call-plugging-r8.md`.

Prove `call_context_plug_typed` by induction over the actual typed context
constructors and provide context inversion needed by Q. Retain the typed hole,
all pending adapters/consumer, Scope/owner, receipt/View data, and arbitrary
literal suffix. P may not assume a one-step preservation or body-safety law.

### Q — Sol/high, maximum 1,800s; launch with P after representation checks

Exact paths: `notes/theory/lean/YulangClosure/CallContext.lean` and handoff only
`tasks/agent-loop/inbox/20261025-lean-call-context-r8.md`.

Prove `call_step_typed_or_handoff` by inversion over every actual Call
transition and the actual substitution relation. Consume P's exact frozen
theorem. Export the unchanged Proposition A theorem
`call_context_plug_preservation`. Stop at any omitted source constructor,
unrepresented world operation, lost suffix/metadata, or need for an assumed
safety premise.

### B — Sol/high, maximum 1,200s; launch only after Q/A freezes

Exact paths: `notes/theory/lean/YulangClosure/CompleteCall.lean` and handoff
only `tasks/agent-loop/inbox/20261025-lean-complete-call-r8.md`.

Prove the unchanged `bounded_call_finite_prefix_safety` for every actual finite
Call-internal prefix through first typed handoff/terminal, with independently
typed arbitrary suffix, world, exact arithmetic, and all-state no-`Bad`
property. Consume the exact checked A declaration/hash. Do not start proof edits
or spend this grant while A or the representation is pending. B does not claim
foreign-tail safety after handoff.

### Conditional stage order and total cap

Fresh r8 cap: 6,600s total: implementation 1,200; P 1,200; Q 1,800; B 1,200;
Luna serialized checks/integration 600; fresh independent review 600. No Astra.
P and Q may run in parallel only after implementation stops, all representation
checks pass, Luna freezes the exact hashes, and the actual-execution/nonvacuous
`Bad` proof seam is confirmed. B begins only after A's exact checked declaration
and dependency hash freeze. If that seam is absent, P/Q/B are not launched; Luna
returns to the dispatcher with the exact obstruction. Unissued stage grants
are not running, charged, reclaimed, or transferable. Maximum two new authors
active concurrently (P/Q). The three legacy UNKNOWN reservations remain
quarantined and consume their slots/resources; no path is reclaimed.

## Verification, review, and Git

Only Luna runs checks, serialized and with the pinned toolchain. Check the
repaired representation modules in dependency order, then `CallPlugging.lean`,
`CallContext.lean`, `CompleteCall.lean`, every changed direct/transitive
dependency, and `YulangClosure.lean`. Stop on the first failure, preserve the
exact diagnostics, and spend no more than the 600-second primary cap. Run no
Cargo, native builds, or tests. `python3 tools/agent_sprint.py check` checks
workflow state only.

After every author is STOPPED and bytes/dependencies are frozen, a fresh
isolated `compiler_referee` reviews the combined candidate and all r6 public
declarations. Review checks exact source order, one owner, receipt before
force, delayed adapters, actual Value/Computation entry, inner-to-outer result
adapters, event-time Views, Req/Fail reachability and preservation, world and
suffix behavior, P/Q/B proof use, actual execution correspondence, nonvacuous
Bad exclusion, axiom receipts, and proof-hole/escape scans. Authors cannot
review their own work. Acceptance needs no blocking/major finding and all
blocking/major findings closed with checked bytes under the same scope.

Only Luna updates this contract/current state and performs explicit-path Git
staging, commit, and ordinary push after acceptance, or a clearly labeled
research-only checkpoint if the bounded attempt stops unaccepted. Never stage
unknown/pending work, overwrite a moved remote head, or force-push. A commit or
static check is not proof closure. Full parent and production/source/native
gates stay OPEN.

## Stop and consultation conditions

Stop a lane at its cap, a source-semantic contradiction, changed dependency,
unresolved proof hole, failed proof obligation, unrepresented transition, or a
need to enlarge its exact write lease. Unknown writers keep their leases. Do
not resume r7 grants. Next dispatcher consultation is at a material semantic
obstruction/counterexample, changed authority/dependency/lease/resource,
implementation-to-proof integration seam, r8 outcome, or goal replanning—not
after each lemma or routine check.
