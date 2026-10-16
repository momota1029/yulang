# NPAIR snapshot borrowing and evidence enumeration

Status: frozen candidate source audit and conditional borrow argument; no
reviewed theorem, runtime guard, implementation authorization or parent closure.
Author: `/root/npair_snapshot_borrow_enumeration`, sole author; no descendants.
Assignment: `NPAIR-SNAPSHOT-BORROW-ENUMERATION-20261017`, revision 1.
Sprint: `npair-snapshot-owner-interface-20261017`, revision 1.
Baseline: `7a281f6e4ecfc34dc9b9a722714d845e205e17bd` (supplied; no Git used).
Requested model/effort: `gpt-6-sol` / high. Observed model/effort: UNKNOWN / UNKNOWN.
Current-session active receipt: 2026-10-16 23:20:08 UTC; 240-second cap.

## Result and parent application

The proposed interface is **not implementation-ready**. The four pinned files
establish the mutable owners and several retained evidence classes, but supply
neither the proposed complete read interface nor its successful/quiescent route
constructor. This is an exact owner-interface obstruction, not an impossibility
result or a source-qualified counterexample to Simple-sub.

The useful conditional fact is limited: a live shared session borrow prevents
safe exclusive borrowing of that session and its owned descendants while a
certificate still uses the borrow. This covers the audited rollback, truncation,
physical-bound update and context-canonicalization paths requiring `&mut self`.
It does not establish successful completion, complete evidence, owner identity,
absence of relevant interior mutation, or an actual certificate API.

Apply this directly to `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`: the
one-shot structural suffix still lacks an enforced complete snapshot premise.
Even a future successful structural check cannot supply `eta_op`,
`realization_op`, adopted `At(D,w,delta)`, actual source admission, whole
N-Transport or the receive consumer. Preserve the original dependent witness,
providers, source occurrences, worlds, assignments, guards, continuations,
interactions, Call demands, residual lineages and futures. F1/FK1, J1/J2,
mixed/multiple-symbolic coverage and the independent parent gates remain OPEN.

## 1. Borrow, identity and expiration

`InferenceSession` owns `candidate_graph`, `store`, `bounds`, `effect_bounds`,
`typed_pairs`, `typed_worklist` and `route_journal` (`lib.rs:7665+`).
`rollback_route_transaction(&mut self)` restores the store, intrusion state,
local-use cursor and route vectors (`lib.rs:9429+`). Effect rollback truncates
Permission/view/contribution vectors (`candidate_effect.rs:278+`); context and
BoundEvidence rollback restore heads and truncate records
(`candidate_context.rs:572+,1780+`).
`candidate_context_canonicalize_bounds(&mut self)` adds transports and Derived
dependencies after representative changes (`candidate_context.rs:3612+`). None
of those operations can safely acquire their required exclusive borrow through
the same session while a live shared borrow is used.

Consequently, **if** construction derives every subreference from one live
session, all relevant mutation requires exclusive access or is separately
excluded, and every certificate operation retains that borrow, then those
operations cannot interleave with certificate use. An exported plain index or
copied `EvidenceSnapshot` does not inherit this property. Nonlexical lifetimes
may end an unused borrow early; the actual requirement is that no later
certificate use remains possible after mutation, not that lexical scope ends.

Two simultaneous sessions can share the same lifetime parameter. Therefore
`Handle<'a>` alone is not a session brand. The Draft's private-constructor and
no-bare-ID conditions must also prevent passing a handle from snapshot A to a
resolver on snapshot B. Deriving both records and queries through the same
snapshot without foreign-handle inputs, or checking their retained owner
identity at every combining resolver, is a required implementation obligation.
Matching numeric IDs, matching source owners, equal endpoints, or the same
lifetime cannot perform that check. No such new API exists in the pinned code.
The explicit comment on `DirectTransportAdmissions` already warns that bare
IDs authenticate neither another State nor rollback-retired records
(`candidate_context.rs:508+`).

The universal mutation-exclusion proof also stops at a scope boundary:
`GraphState::intrusion` is a type owned by unpinned `candidate_intrusion`;
`canonical_value`/`canonical_effect` call its `value_rep`/`effect_rep`
(`lib.rs:11565+`). Their transitive representation and any interior-mutation
behavior are not established by the four-owner audit. No extra source owner was
opened or adopted. This is a missing audit premise, not a claim that those
methods mutate. The `Cell` in `candidate_scheme::CaptureEvidenceMeter` at :347
belongs to separately constructed capture scratch, not a field of `GraphState`;
its presence alone does not refute session immutability.

Quiescence requires an owner-checked successful route, no active journal,
completed typed drain/replay/restoration continuations and a retained exact
route. A shared borrow can be taken from an unsuccessful or suspended state;
`route_journal.is_none()` alone does not prove success. The context owner has
private `replay_operations`/`restorations` and visible `typed_drains`/`processing`
(`candidate_context.rs:820+`), and replay may return `Queued` (:3597+). No
snapshot constructor establishes the required conjunction. A blanket
`replay_operations.is_empty()` is also unjustified: retired operations can be
retained. The owner must distinguish completed retained records from unfinished
continuations without changing ordinary inference scheduling.

## 2. Evidence inventory and precise omissions

| Required class | Pinned actual source evidence | Missing interface or proof |
| --- | --- | --- |
| Raw Permission and D | Private `FormalPermission` retains parameter, occurrence, source owner, scope, typed path, row and concrete operands (:189). `candidate_formal_effect_port` allocates a raw row and records its path (:1215+); `candidate_formal_annotation` publishes after links 43/44 (:1294+). | Full immutable Permission iterator; path recovery from this session's actual `formal_domains` negative root, preserving raw row separately from representative. Permission stores no direct raw-port field; do not invent one. |
| Current physical lower and slot | `VariableBounds`/`EffectBounds` own eight typed lane vectors (`lib.rs:4036+`); `PhysicalBoundSlot` stores owner RowKey, lane and index (`candidate_context.rs:464`). | The Draft table must explicitly cover session `bounds` and `effect_bounds`, not only captured `Graph::bounds`. An owner resolver must check row kind, lane, index and actual operand against admission/emission BoundKey. |
| Function premises | `positive_function_children`/`negative_function_children` read real Function tags/children through `store.term_view` (`lib.rs:14180+`); Dependency::FunctionPort retains parent, child, field, operation (:255+). | Check actual child pair, field and Swap/Preserve against both real parent endpoints. An edge or enum tag alone is insufficient. |
| Ordered Replay | Dependency::Replay retains child, lower, upper and both input BoundKeys (:267). `candidate_context_begin_replay` enumerates lower/upper fiber pairs, composes both contexts/scopes, records the dependency and recipe (:3400+). | Expose and validate both relation memberships, both ordered inputs and actual child endpoints. Equal lower/upper IDs still require two premise positions. |
| Origins and alternatives | Context relations/dependencies/origins/bound fibers, View::Operation provenance and Contributions are retained; `CircuitEvidence` exposes selected projections (:954+). | Complete owner-local enumeration with raw occurrence and every relevant association; no first-Origin shortcut or canonical-row merging. |
| Admission history and transport | BoundEvidence owns groups, linked admissions/emissions, snapshots, recipes, reverse edges and transforms (:549+). Causes distinguish OwnerEmission, ExtrusionLink, FreshUse and BoundTransport (:468+). | Full checked access to these associations, not just admission/emission arrays. Historical snapshot heads are retained prefixes; they are not today's full group. Any relevant unsupported cause/transport must fail the check rather than disappear. |

`CircuitEvidence` allocates selection masks and repeatedly closes selected
relations/contexts/views. Its iterators expose no physical evidence arrays or
Permission records. `retained_input` checks both Replay memberships but reports
FunctionPort/Replay context operations as inert and adds missing readiness
reasons (:1062–1213). It is precedent for borrowed projections, not a complete
structural certificate or owner-identity proof. `observed_dependencies` also
does not provide the missing physical evidence.

There is a stronger limit on the Draft's phrase “records needed in principle.”
`BoundEvidence::admit` (:683+) explicitly adds
`ProcessingAntecedentsUnavailable`, `OrdinarySeedAuthenticationUnavailable` and
`MissingAntecedent` for OwnerEmission/ExtrusionLink; FreshUse propagates snapshot
coverage and adds `ReplayUseAntecedentsNotRetained`. Exposing every existing
record cannot synthesize those absent premises. A structural validator may
reject or independently authenticate the precise required premise from actual
pinned owner evidence; it cannot clear coverage merely because enumeration
finished. This audit does not prove every successful native route necessarily
fails: the exact relevance and authentication policy remain to be specified.

## 3. Traversal and accounting qualification

The Draft correctly requires repeated-work charges and both ordered Replay
inputs, but supplies requirements rather than a concrete deterministic algorithm
or allocation bound. The following are the proof obligations for its proposed
shared witness, not executable implementation approval.

For one fixed raw query, represent each retained alternative as a distinct
derivation alternative with ordered premise edges. Replay is a two-premise
requirement within one alternative; independent Origins are alternatives. Share
validation only for identical evidence obligations, including expected endpoint
and occurrence context where those affect validity. Memoizing solely by numeric
RelationId can merge distinct query obligations. Preserve every incoming edge
even when its target is already validated. Sharing a DAG need not enumerate all
tree unfoldings, but cannot erase alternative or premise positions.

A deterministic iterative depth-first traversal can use explicit frames with
the next alternative/premise cursor. “Active” means on the current premise
ancestry, not merely scheduled elsewhere in a work queue: a diamond with a
shared child is not a cycle. A back edge to an unresolved active obligation
fails; completed shared obligations may be reused after checking the new edge.
Only publish after every required root and alternative is checked. Array order
can supply stable order; HashMap iteration cannot. If an ordered index or sort
is needed, its full scan, comparisons and temporary capacity must be charged.

An adequate work meter charges each actual operation, for example the checked
sum of record/slot reads, premise and alternative inspections, stack operations,
identity lookups including repeated references, key comparisons/hashing work,
and any sorting/index construction. A whole dependency scan for each expanded
node charges every scanned entry including rejected candidates. With n
expansions and m dependency entries that scan alone is n*m inspections; n
unique visited nodes is not a bound. Enumerating a Replay fiber product with a
lower count l and upper count u charges l*u pair visits with checked arithmetic.
The current producer's incremental pairing optimization does not prove the
future validator avoids repeated scans.

Storage must charge simultaneous capacities for frame stack, identity table,
node/alternative/edge witness arrays, masks, sorting/index scratch, gap/error
buffers and every owned nested path/key/vector. Check multiplication and sums;
reserve before publication and reject overflow. If the metric claims physical
allocated bytes, table bucket/control storage and overlapping old/new buffers
during growth also need an audited bound; capacity times entry size alone is
not such a bound. Borrowed retained solver payload may be excluded from new
validator-owned bytes only under an explicitly stated metric. No numeric
ceilings, exact layout or audited growth bound is supplied by this Draft, so
no resource theorem or implementation readiness follows. Missing size bounds
remain an implementation-contract gate, not permission to narrow source meaning.

## Mutual TODOs, reuse and stop

**NPAIR-SNAPSHOT-OWNER-PREMISES-20261017**, to Luna and the four native owners:
first supply a reviewed private constructor establishing exact route selection,
success/quiescence, same-owner resolution, full Permission/physical evidence
access, historical/current-head distinction and explicit coverage handling.
Minimal later implementation TODO is this read-only owner interface only,
under a new lease and gate. Falsifiers: foreign-session handle accepted; stale
snapshot head treated as all current admissions; physical lane/index unchecked;
unavailable antecedent accepted; suspended replay called successful; mutation
possible while a usable certificate exists. This packet authorizes no code.

**NPAIR-SNAPSHOT-TRANSITIVE-OWNER-AUDIT-20261017**, to Luna: if universal mutation
exclusion remains required, approve the exact representative/lifecycle owner
pin before extending beyond the four files. First missing input is the relevant
`candidate_intrusion` owner definition and mutation contract. Falsifier: relying
on `&InferenceSession` to exclude relevant interior mutation without auditing it.

**NPAIR-SNAPSHOT-TRAVERSAL-BOUND-20261017**, to Luna: after the interface gap is
resolved, freeze qualification rules, obligation keys, deterministic traversal,
coverage/cycle failure and the work/allocation metric. Falsifiers: one Replay
premise, one Origin, unique-node-only charges, unordered iteration, or uncharged
scan/branch/capacity growth. This is the next discriminating input; another
conditional shared-borrow note would leave the current premise untouched.

Reused only within actual premises: Luna's readiness Draft and previous one-shot
Draft; forward proof by `/root/npair_forward_source_witness_realization` for its
fixed successful snapshot structural suffix; supplier boundary by
`/root/npair_operation_contribution_supplier` for the missing original Operation
clause; adopted negative-pair definition by `/root/negative_formal_pair_proposal`
under Luna's adoption receipt. Native authors and unreported effective settings
remain UNKNOWN. Rejected: bare-ID authentication, same-lifetime branding,
captured graph as live physical storage, coverage-as-authentication, graph
reachability as derivation, unadopted Operation image or substitute historical
Call proof, and local frame action as F1/FK1 closure.

Four stages: pins/authority; borrowing/lifecycle; complete-evidence audit;
traversal/accounting and parent application. Checks were static source reads,
actual SHA-256 comparisons and output-scope/hash checks. No tests, builds,
probes, Cargo, compiler/source execution, Git, network, nested CLI or children.
Some aggregate reads truncated; decisive owner definitions and constructor
clauses were reread in bounded excerpts. Exact timing/charge is recorded in the
frozen handoff. The owner-interface blocker is the assignment stop condition.
Only this file and the one assigned inbox are new/written; no scratch paths.
After the final hash receipt, writes STOPPED; no worker activity is claimed
while awaiting Luna's fresh review. This author cannot certify the combined
readiness/proof result.

## Frozen direct dependencies

All listed actual file hashes matched issued pins. Provenance stays with the
named dependency authors; this author claims no authorship of their contents.

| Path | SHA-256 |
| --- | --- |
| `tasks/agent-loop/sprints/npair-snapshot-owner-interface-20261017.md` | `243525db31b3999778f6fd79eeb3de52399cff0e1a864c555615bb55bf6afed5` |
| `notes/design/2026-10-17-npair-snapshot-owner-interface.md` | `45b789c89c81cf335b25e6ff79b622572cf5d6e4d58932023ab8fe7843225e27` |
| `tasks/agent-loop/inbox/20261017-npair-snapshot-owner-interface.md` | `cef3388c3887e71cb292782a7813191f83ba467593fff4c5fe89408a95bdfafd` |
| `crates/yu-solver/src/lib.rs` | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` |
| `crates/yu-solver/src/candidate_effect.rs` | `11a1477ff2c35c03dccb70bdc6121d89d3ced9fadb1921cb8cf8cd5c093b07fb` |
| `crates/yu-solver/src/candidate_context.rs` | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` |
| `crates/yu-solver/src/candidate_scheme.rs` | `52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a` |
| `notes/design/2026-10-17-npair-one-shot-structural-validator-contract.md` | `2cf0d473f0c3a3f75474e54a99b5c1d4470ab338320272445eae0a5fe263e23f` |
| `notes/theory/2026-10-17-npair-operation-contribution-supplier.md` | `1ee864b00d61b774e56c5a965a062448151652ad45ab4ec8956e1f02e7fd685b` |
| `notes/theory/2026-10-17-npair-forward-source-witness-realization.md` | `1d2c827cdf7661cc77a9edbb869bffd3cdcca7b51afba418789eaae9abf3cb3a` |
| `notes/design/2026-10-17-negative-formal-pair-formation-proposal.md` | `0a73aaf7016e86dd5babbdd5482b05a793764418bc003607207ef0375ee46006` |
| `notes/design/2026-10-17-source-formation-proposals-adoption.md` | `d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
