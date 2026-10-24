# LEAN-COMPLETE-CALL-20261025/r7

Status: FROZEN by Luna as a bounded continuation of the user's resumed Lean
proof goal. Grant: 5,400 seconds; no earlier unused time carries forward.
This is a Lean formalization milestone under the existing Yulang semantics.
It authorizes no compiler change or new language semantics.

## Original goal and this milestone

The user's continuing goal is complete Lean proofs of Yulang semantics and type
inference under `notes/theory/lean`, with reviewed milestones committed and
pushed. The full parent, original inference A/B gates, source/native
correspondence, principality, and termination remain OPEN.

R6 established and independently reviewed a bounded Original-to-Control bridge.
The next concrete obstruction is the absent typed Call boundary: current
`Original.Val` and `Original.Comp` have no callable, lambda, wrap, or Call, and
current Control metadata has no typed representation of Call receipts or
complete interface Views. This sprint adds one source-derived typed Call
fragment and proves its bounded value-type safety through the actual Call
administrative order. It must not be replaced with ordinary beta reduction or
an isolated function/substitution lemma.

## Semantic authority and exact source order

Use the existing operational source rules without altering their meaning:

- `docs/yulang-operational-type-safety-ja.tex`, §§ “値と計算”, “型付け規則”,
  “call の入口と adapter”, and “View、transport、受領を生成する全規則”;
  especially lines 145–245, 362–400, 535–602, 1029–1044, and 1231–1266.
- Current accepted design/approval constraints in `rules/design-authority.md`.
- `notes/theory/2026-10-24-corrected-core-value-continuation.md` is an
  independent-review-pending candidate proof outline only. Its V1–V7 claims
  are not premises and cannot be cited as established theorems.

For `Call(f,t)` with `f:C(A,B)` and `t:UA`, the represented steps must retain
this exact order and data:

1. select one fresh receiver owner and enter its Scope;
2. peel wraps from outermost to innermost, retaining that same owner;
3. retain each argument adapter inside a delayed
   `Delay(let z <- Force t in a(z))`; do not run it during peeling;
4. attach the source lambda's receipt to the designated carrier observation
   paths before the first force;
5. Value entry forces the received carrier; Computation entry substitutes that
   carrier without forcing it;
6. execute the typed body and declared-result consumer;
7. execute pending result adapters in the source-prescribed inner-to-outer
   order under the complete Call View; on normal completion leave Scope while
   retaining returned value views and latent code.

A request keeps its operation instance, payload, response, saved continuation,
Call context, Scope/View context, and literal old suffix. A failure retains its
reason and follows only the existing specified propagation/cleanup relation.
World is explicit and follows the represented source transition; this sprint
must not invent a cleanup or observation policy. Where the represented body or
adapter syntax can produce Req/Fail, preserve those cases. If the source-derived
fragment cannot represent an actual required rule, return the exact obstruction
instead of silently omitting it.

## Exact metadata-realization boundary

The formal fragment must retain explicit typed data for the one receiver, the
source profile/receipt template, designated receipt slots, carrier and View
occurrences, call.effect and result ports for each represented interface, typed
adapter path correspondences, and captured views. These are immutable
source-plan inputs and are threaded through the actual ordered transitions;
they are not arbitrary callbacks and cannot be fabricated from endpoint type
equality.

The milestone proves that the represented Call path preserves its value type
and pending typed-adapter context when supplied those explicit inputs. It does
not prove that the full source/frontend/compiler constructs a complete or
adequate decorated plan, that receipt generation is authentic for every source
program, or that all event observations/eligibility/current-world hygiene are
correct. Those source-plan, effect-hygiene, and observation premises remain
OPEN and must be named in the outcome. The result is a bounded type-safety
component, not full Call semantics or production approval.

## Required propositions and theorem outcome

Implement a concrete typed evaluation-context decomposition for the represented
Call syntax. The context must expose the active typed hole and retain pending
delayed argument adapters, the body/result consumer, pending result adapters,
Scope/owner, receipt/View data, and an arbitrary independently typed Control
suffix. Prove each actual source/administrative step preserves this context and
its result type, using the syntax-directed typing and the actual substitution
function. Apply the checked arbitrary-suffix bridge or an explicit Call-specific
extension of it; preserve the literal suffix and exact prefix/exit arithmetic.

The frozen result is divided into two named propositions in separate Lean
modules. Their mathematical claims are fixed here; the Lean signatures must be
written against the implementation's frozen names and hashes, without
weakening these claims or adding an assumed safety premise.

**Proposition A — `call_context_plug_preservation` (`CallContext.lean`).**
For every represented typed Call evaluation context with its active typed hole,
plugging a computation of the hole type yields a computation of the context's
result type. Inversion must expose the actual typed hole, pending delayed
argument adapters, body/result consumer, pending result adapters, Scope/owner,
receipt/View inputs, and literal suffix. Advancing the active computation or
any actual administrative Call transition must either preserve that context
judgment, result type, current world, and suffix while internal, or produce its
explicit typed handoff/terminal witness while retaining the result type, world,
and suffix. Prove this from the represented syntax and typing rules, including
the actual substitution path; do not assume a body-safety or Call-preservation
law. Helper propositions for plugging, inversion, or one-step preservation
belong to this module and are part of A's frozen result.

**Proposition B — `bounded_call_finite_prefix_safety` (`CompleteCall.lean`).**
For every closed represented typed Call configuration, every independently
typed arbitrary old Control suffix, and every actual finite internal prefix,
the prefix preserves the typed Call-context judgment and result type, literal
suffix, and represented world, or reaches its explicit typed handoff or a
represented terminal `Ret`/`Req`/`Fail` case. Every state in the prefix is not
`Bad`. The proof must classify every actual successor constructor, use A's
frozen theorem and the actual substitution, and preserve exact prefix/exit
arithmetic. Any progress alternative must follow from the represented syntax;
no same-body `BodyLaws` or equivalent safety premise may establish internal
lambda/adapter safety. If `Req`/`Fail` are outside the represented fragment,
the theorem and outcome must state that limit explicitly and must not label the
result complete Call safety.

Keep all existing r6 public theorem statements and source/Control transition
meaning intact. Extend their proofs only as needed for a genuinely extended
relation, then recheck the old declarations. No weakening, hidden premise,
assumption, proof hole, unsafe declaration, `native_decide`, or imported V1–V7
claim is permitted. The actual `Original.substComp` path remains actual if the
representation reuses it; any new substitution must be defined over its real
syntax and proved type-preserving.

## Frozen baseline and exact dependency component

Branch: `research/simple-sub-intrusion`.
Baseline: `7262f16cf58f0236a1a140e044d8fbbeb6cf61c6` (local and remote agreed
before contract creation; includes the pushed r6 integration receipt).

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
| `notes/theory/lean/YulangClosure/CoreSyntax.lean` | `4c036531cdd599799d0b943b4c8e2f1398aa91f5cf32296d7d6c50be1ff7a001` |
| `notes/theory/lean/YulangClosure/CoreSubstitution.lean` | `6d7d5da463480fbb618072b086c5092452575c56526579e4f898babd37b4567c` |
| `notes/theory/lean/YulangClosure/CoreExecution.lean` | `2cc68ffc79f17c0cb478802fec10ca2861e1a558a8202796bd7599595e5907ed` |
| `notes/theory/lean/YulangClosure/CoreComposition.lean` | `1527cd3c5961b413ec2b97495744b218aba6247956881318485364d15065294c` |
| `notes/theory/lean/YulangClosure/ControlSyntax.lean` | `801f5ff354d0546aaca6fbd353cf261d3e49c915f78687d76167eab7b9aa8bc9` |
| `notes/theory/lean/YulangClosure/ControlTyping.lean` | `67e0d5d8840090ad7adf06b33c65725dc0901488c16f9dcc235c5c0372ae0135` |
| `notes/theory/lean/YulangClosure/ControlComposition.lean` | `9a48a5f2ef15eb947478757e0fa74457579183ccdbab90f2518886590e33fc40` |
| `notes/theory/lean/YulangClosure/CoreControlBridge.lean` | `30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a` |
| `notes/theory/lean/YulangClosure.lean` | `04a209f4aa4a9e8c2848aee11eb16befb6fe4e0b566d4683dd0705f96ccf3b2f` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| r6 accepted outcome | `b6def9a2c248ccbd7a8bda1cba9489b6dab84abd8a9131f0b24ce573e0eefd4a` |

Pinned toolchain: Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`).
Luna rechecks the complete direct/transitive dependency component and the
r6 outcome hash before dispatch, at the frozen-representation seam, and before
review. A changed dependency returns to Luna; workers do not expand their
leases.

## Lanes, exact leases, and frozen-representation seam

**Luna/high implementer**, 1,800 seconds maximum:

- `notes/theory/lean/YulangClosure/CoreSyntax.lean`
- `notes/theory/lean/YulangClosure/CoreSubstitution.lean`
- `notes/theory/lean/YulangClosure/CoreExecution.lean`
- `notes/theory/lean/YulangClosure/ControlSyntax.lean`
- `notes/theory/lean/YulangClosure/ControlTyping.lean`
- `notes/theory/lean/YulangClosure/ControlComposition.lean`
- `notes/theory/lean/YulangClosure/CoreControlBridge.lean`
- handoff only: `tasks/agent-loop/inbox/20261025-lean-complete-call-implementation.md`

Deliver the source-derived grammar, typing, substitution, actual transition
sequence, metadata witness boundary, typed adapter context, request/failure
cases included, and bridge interface. Do not edit root imports, docs, contracts,
current state, `CallContext.lean`, `CompleteCall.lean`, or Git. Freeze the exact
interface and handoff before dependent proof construction. If the source rules
cannot be represented without a semantic choice outside this contract, stop
and return the exact obstruction; do not settle that choice yourself.

**Sol/high constructive prover A**, 1,200 seconds maximum:

- `notes/theory/lean/YulangClosure/CallContext.lean`
- handoff only: `tasks/agent-loop/inbox/20261025-lean-call-context-proof.md`

Until the implementation interface is frozen, perform bounded read-only source
preparation and write only the handoff. After Luna confirms the implementation
handoff revision/hash, prove Proposition A and freeze its theorem signatures,
dependency hashes, and check instructions in the handoff. Do not edit
implementation files or the Proposition B module.

**Sol/high constructive prover B**, 1,200 seconds maximum:

- `notes/theory/lean/YulangClosure/CompleteCall.lean`
- handoff only: `tasks/agent-loop/inbox/20261025-lean-complete-call-proof.md`

Until the implementation interface is frozen, perform bounded read-only source
preparation and write only the handoff. Do not create or edit `CompleteCall.lean`
until Luna confirms the implementation handoff's exact revision/hash and grants
the frozen interface seam. After that, prove Proposition B. It depends on
Proposition A's exact frozen declaration/hash; do not assume A or weaken B if A
is incomplete. If a source rule cannot be realized, report it as an obstruction;
do not assume same-body safety or narrow this contract.

Authors and contributors are ineligible to review these artifacts.
Luna owns `YulangClosure.lean`, this contract, `current.json`, checks, outcome,
review assignment, adjudication, explicit staging, commit, and ordinary push.

## Checks, independent review, and falsifiers

Only Luna runs serialized Lean verification, one process at a time, with the
pinned Lean 4.35.0 toolchain and `-j1 -M1024`; each invocation has a 120-second
timeout. Check the frozen representation modules before proof use, then
`CallContext.lean`, `CompleteCall.lean`, all changed direct dependencies, and
the root module. Run no Cargo/native/test processes. Static
`python3 tools/agent_sprint.py check`
validates workflow state only; it is not proof evidence.

A fresh isolated `compiler_referee` reviews the frozen combined diff and
hash-pinned direct/transitive dependencies. Review must independently inspect
source-rule correspondence, the single-owner and receipt-before-force order,
outer-to-inner peeling, delayed argument adaptation, inner-to-outer result
adapters, current-world/suffix behavior for represented cases, actual
substitution, typed context preservation, public r6 statement preservation,
axiom receipts, and proof-hole/escape scans. No author reviews their work.

Independent falsifiers:

- a second owner appears while peeling any wrap;
- Force or argument adaptation runs before source receipt attachment;
- Value entry does not force, or Computation entry forces instead of
  substituting;
- a result adapter runs before an inner adapter;
- any receipt, View, latent value, request instance, saved continuation,
  failure reason, Scope, current world, pending adapter, or literal suffix is
  lost or fabricated;
- a request observes only after bubbling past a handler when the represented
  source rule observes at event creation;
- normal return, suspension, and failure cleanup are conflated;
- internal safety depends on `BodyLaws`, an assumed Call beta theorem, or a
  candidate V1–V7 claim;
- an existing r6 public theorem statement/domain is weakened or fails after the
  formal representation extension.

A new semantic choice or a mismatch with the operational source rules halts
that dependent part and returns the exact source lines and counterexample to
Luna. No source/native or production gate is promoted by this milestone.

## Resource grant and stop conditions

Fresh grant: 5,400 seconds total, distinct from all earlier grants:

- implementer: 1,800 seconds;
- Proposition A prover: 1,200 seconds;
- Proposition B prover: 1,200 seconds;
- Luna serialized checks/integration: 600 seconds;
- fresh independent review: 600 seconds.

The three author assignments may prepare in parallel, but only within their
exact leases. Before the representation seam, both proof authors are read-only
on Lean modules and may write only their own handoff. After the implementer
freezes and stops, A proves and freezes its result; B starts proof edits only
after A's declaration and dependency hashes are frozen. All three authors stop
before Luna's serialized checks and the fresh independent review. These ceilings
include preparation and all work already charged; later stages do not restart
or renew a grant. At most these three new author assignments may be active
alongside the three quarantined legacy reservations.

Astra: 0. At most one Lean process, one CPU, 1 GiB, and one 120-second
verification invocation at a time. All grants are reserved when dispatched;
actual UNKNOWN time remains charged. No automatic renewal or carryover. Stop at
the budget boundary, a source-rule contradiction, a changed dependency, an
unresolved proof hole, or a failed independent review. A bounded partial result
may be recorded only with its exact remaining premise; the full parent stays
OPEN.

Next dispatcher consultation: frozen-representation seam, a source-rule
contradiction, a new dependency/lease/resource requirement, integration seam,
or the next sprint boundary. Routine lemmas, checks, and handoffs stay inside
this fixed contract.
