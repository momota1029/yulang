# NPAIR pre-freeze observation: live storage, missing completion premise

Status: frozen candidate source/native audit and conditional ownership lemma;
not an independently reviewed theorem, implementation authority or parent closure.
Assignment `NPAIR-PREFREEZE-OBSERVATION-BOUNDARY-20261017`, revision 1.
Author `/root/npair_prefreeze_observation_boundary`, sole author, no descendants.
Requested model/effort: `gpt-6-sol` / high; observed: UNKNOWN / UNKNOWN.
Sprint revision 1; supplied baseline `d28b83ed498b6fb8d3959ca33c0d19c40f816f6e`.

## Result and application to the original parent

The lexical point immediately after successful `self.execute()?` in
`InferenceSession::run_candidate` has the original physical vectors available.
**A completed, owner-bound structural observation point is not established by
the frozen source set.** The exact missing premise is that every actual
candidate source/graph driver returning to this point has completed all route,
typed-drain, replay, restoration, source/local-use and intrusion work. The
inspected finish boundary supplies no such check. This is a missing source
correspondence proof, not a reachable counterexample or proof of unsafety.

Apply this immediately to `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`:
the pre-freeze alternative removes the post-solve storage-loss obstruction,
but does not discharge the complete structural-snapshot premise. Under this
sprint's discriminator, no safe point has been established, so snapshot work
stops. Readiness must record this blocker and WAIT. No code or another general
snapshot audit follows under this contract.

The original parent retains `f () -> install(g) -> fresh local use -> g ()`,
both ordinary formal edges, the original accepted source domain and all
providers, assignments, contexts, worlds, typed positions, guards,
continuations, interactions, Call demands, residual/witness lineages and
futures at their original scopes. `J1`/`J2` and F1/FK1 remain independent.
No local completion fact establishes the foreign-continuation cases.
Neither `eta_op`, `realization_op`, adopted `At`, source admission,
N-Transport, N-Subtract-Elim, receive consumption nor production follows.

## Exact seam and what the source actually establishes

`lib.rs:10413–10453`: `execute(&mut self)` admits facts when appropriate,
executes the SCC plan, then in source mode calls `execute_candidate_loose`
and each `execute_candidate_expression`, samples accounting and returns.
`run_candidate(mut self)` asserts candidate mode and absent legacy
finalization, calls `execute`, then immediately consumes self in
`finish_candidate`. That method repeats the mode assertion and consumes self
in `finish_observations`; its later assertions concern closed types/schemes.
There is no observation callback, completion certificate or global
quiescence check at this seam in the current source.

`InferenceSession` owns `bounds` and `effect_bounds` directly
(`lib.rs:7682+`); `finish_observations` reads their original rows to build
projections (`:17516+`). No intervening move of those fields occurs between
execute's return and that read. Thus the prior post-solve physical-vector
loss is avoided by a lexical shared borrow here. Finish later omits both
vectors from returned `FrozenInferenceData`; the resource-probe path also
explicitly drops them (`:17685+`). This is storage visibility, not completion.

`execute_scc_plan` dispatches candidate mode to
`execute_candidate_graph_plan` (`lib.rs:14790+`), rather than the ordinary
`execute_scc_plan_inner` implementation. Its actual body is in pinned
`candidate_scheme.rs:975+`; source mode calls `execute_candidate_source_root`
for each member before capture/publication and later clears active roots/uses.
The three source drivers `execute_candidate_source_root`,
`execute_candidate_loose` and `execute_candidate_expression` have call sites
in the pinned source, but their owning bodies are outside the inspected
six-file input set. No new source owner was opened or its historical pin
adopted. `lib.rs:213` declares the `candidate_source` module; the current
implementation owner/pin of these source-driver bodies must be supplied by
Luna before any expanded audit. A historical
candidate_source hash in an older proof is not a current authorized pin.

## Local completion facts and their limits

| Owner | Established source fact | Missing implication at observation point |
| --- | --- | --- |
| `finish_route_transaction_with_candidate_accounting`, `lib.rs:9281+` | On Ok, takes the active journal, commits replay operations/store, clears workspace, preserves a spare journal; publishes a completed Local only when its cursor says complete. Errors roll back. | Its generic operation's Ok does not force typed drains or Local/source continuations to be empty. |
| `Context::commit_replay_operations`, `candidate_context.rs:1899+` | Clears route undo, resets acknowledgement preparation on retained typed frames, reclaims eligible retired operations. | Explicitly supports committed continuations. Journal absence alone is insufficient. |
| `run_candidate_typed_drain`, `lib.rs:12285+` | Drives its own frame to terminal completion, restoring previous processing/relation; error removes its new frame. | Previous outer processing/frame state can still exist. Local return is not global drain completion. |
| `step_typed_drain`, `lib.rs:12340+` | When transport has no current item and queue is empty, settles intrusion; advances to diagnostics only with no popped item and dirty false. | Need actual driver coverage and no subsequent mutation before observation. |
| `candidate_step_typed_drain_terminal`, `lib.rs:12725+` | Validates top frame/stage and acknowledgement frontiers, completes acknowledgements, records Ready return when required, pops frame and restores previous context. | Child return receipt and ordered parent's receipt consumption remain distinct. |
| replay owner, `candidate_context.rs:2056+,2116+,3498+,3547+,3597+` | Queue transfer advances queued; completion advances consumed; Running/Ready/Idle barriers distinguish ownership. `drive_replay` may return `Queued`; only the outer consumer completes queued children. | Successful replay-driving call need not mean Complete. Need the actual source driver's handling of this result. |
| restoration owner, `candidate_context.rs:1985–2033` | Retains an owner/polarity/bound/emission, next-opposite frontier and optional replay; updates/retirement are separate operations. | No seam-wide check proves every restoration advanced and retired. |
| intrusion owner, `candidate_intrusion.rs:489–517` | `settle_candidate_intrusion` consumes pending entries to cursor=len and clears dirty, including newly appended pending work in its loop. Row merge may dirty/enqueue further work. | Need proof the last relevant mutation is followed by settling and the typed queue is drained. `execute` has no final explicit settle/check. |

These are synchronous source control-flow facts, not tests of assumed
transitions. No claim is made that retained continuations actually survive
the successful top-level path: that reachability question is precisely the
unavailable driver-return premise. Likewise errors and semantic conflicts
are distinct; an Ok solve does not establish conflict-free source admission.

## Same actual owner and escape boundary

Conditional lemma: a shared borrow derived directly from the still-owned
`self: InferenceSession` can read that session's physical rows and pinned
candidate graph. Relevant row mutation, intrusion settling, evidence insertion,
rollback and finish require exclusive or consuming session access. Safe Rust
excludes those actions while that shared borrow remains usable. The read-only
representative walk uses shared vectors and does not compress paths, as the
prior pinned intrusion audit established. No transitive immutability theorem
about unpinned source/scope/term/HIR owners is asserted.

To enforce same-owner provenance, a hypothetical private view must retain
`&InferenceSession`, minted only from this actual self. Every subordinate
handle must resolve through that owner alone, or carry that same reference
and check reference identity whenever combined with another view. Lifetime,
row/record ID, HIR key and generation equality are insufficient. No external
bare descriptor can supply an alternative owner. Live reference identity is
stable while the borrow is usable; no owner move/drop is then permitted.

The existing code has no callback/view/result of this kind, so actual
non-escape enforcement cannot be certified. A candidate contract could use
a private `for<'s> FnOnce(View<'s>) -> ()` boundary, with private borrowed
certificates and no lifetime-erased export. The universal callback borrow
prevents safe retention of its usable view/handles in caller storage; unit
return prevents a returned borrowed certificate. This requires the entire
private export surface to respect the rule. Ordinary owned summaries may
escape only as uncertified data. Consuming finish alone is not such a callback
contract, and a generic returned R must not be assumed non-escaping without
its signature/export audit. This conditional construction is not implemented
or a substitute for the missing completion premise.

## Evidence exclusions, reuse and exact TODO

`BoundEvidence::admit` (`candidate_context.rs:683+`) marks OwnerEmission and
ExtrusionLink with unavailable processing/ordinary-seed antecedents and a
missing antecedent. FreshUse inherits coverage and adds
`ReplayUseAntecedentsNotRetained`; absent relation adds further gaps.
Live storage and complete enumeration do not authenticate any of these.
They must remain explicit incomplete/reject results.

Reused within actual premises: the pinned post-solve physical-storage audit,
its local shared-borrow and representative-read facts, and the reviewed-partial
API handoff's unresolved quiescence/evidence obligations. Rejected as proofs:
Ok execute, journal commit, an empty queue at one inner return, copied IDs,
captured graph storage as a physical lane, enumeration as authentication,
and historical driver-source pins as authorization. The adopted negative-pair
definition, under its adoption receipt, supplies only its original source
interface; N-Transport and N-Subtract-Elim remain obligations.

**NPAIR-PREFREEZE-DRIVER-RETURN-20261017**, owner Luna and the actual owners of
`execute_candidate_source_root`, `execute_candidate_loose`,
`execute_candidate_expression`, `Context` replay/restoration and
`InferenceSession::run_candidate`: first missing evidence is a pinned
source-return invariant covering all successful source/graph paths. Required
input: exact approved current driver bodies and this completion-frontier map.
Proposed output, only after Luna's new authority/lease decision: a source proof
or minimal provisional checked gate showing no active route, typed frame,
queued/current task, unconsumed replay child/return, unfinished restoration,
source/Local continuation or intrusion pending/dirty work at this boundary,
with processing restored to the correct top-level state. Falsifier: any actual
successful top-level return with such unfinished work, or an alleged gate
that checks only journal absence/queue emptiness/Ok. No code is authorized by
this TODO. Under this frozen sprint the next step is WAIT, not another audit.

**NPAIR-PREFREEZE-EXPORT-20261017**, owner Luna and future private API owner:
if the completion premise is independently established, require actual owner
minting, checked physical row/lane/index/operand resolution, non-escape and
incomplete-evidence disposition. Falsifier: cross-session equal-ID acceptance,
a usable certificate surviving finish, or clearing an unavailable antecedent
because iteration/solve completed. This is deferred, not implementation-ready.

## Frozen inputs and resource receipt

Every sprint/direct pin below matched before reliance. Authority reads do not
expand the source domain or adopt historical source pins.

| Path | SHA-256 |
| --- | --- |
| `tasks/agent-loop/sprints/npair-prefreeze-observation-boundary-20261017.md` | `88a4a99d4b65cd7d582343455344e916300f168eb1d03d3b8aafed8066793b08` |
| `crates/yu-solver/src/lib.rs` | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `7a57a93481095c6e7d4b8781810b1a5aa0d174e41ede29ac3f2b2b96bce10b0c` |
| `crates/yu-solver/src/candidate_context.rs` | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` |
| `crates/yu-solver/src/candidate_effect.rs` | `11a1477ff2c35c03dccb70bdc6121d89d3ced9fadb1921cb8cf8cd5c093b07fb` |
| `crates/yu-solver/src/candidate_scheme.rs` | `52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a` |
| `crates/yu-solver/src/shadow_apply.rs` | `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf` |
| `notes/theory/2026-10-17-npair-postsolve-snapshot-capability.md` | `9e1ae6e71f095b89b09796e5da375d1f152427b658b6fe3bc045553632a4a3d6` |
| `notes/design/2026-10-17-npair-postsolve-snapshot-api-contract.md` | `ee0cf9823b0cb7e44e512f535ec0dc4980df73fa69cf83aed0e0b4d4739f7488` |
| `tasks/agent-loop/inbox/20261017-npair-postsolve-snapshot-api-contract.md` | `59454380a265393359cc1e8c2340ed0e8b27a78055e4552ea4a991569b3bc79c` |
| governing adoption receipt | `d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa` |
| adopted negative-formal proposal | `0a73aaf7016e86dd5babbdd5482b05a793764418bc003607207ef0375ee46006` |
| top-level inference principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

Four stages: authority/pins; live storage and finish seam; local completion
frontiers and exact unpinned-driver obstruction; parent application/freeze.
Static reads and SHA-256 comparisons only; some aggregate output truncated,
decisive seam/terminal/replay/intrusion definitions reread in bounded excerpts.
No tests/builds/probes/Cargo/source execution, Git, children, network, nested
CLI or code edits. New paths: this artifact and the one assigned inbox only;
scratch paths: none. No descendants or unresolved descendant leases.
Time/charge and final writer STOP are recorded in the inbox. Fresh independent
review and adjudication belong to Luna; this producer cannot certify the result.
