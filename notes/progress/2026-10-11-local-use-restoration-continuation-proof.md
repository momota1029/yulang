# Local-use freshening and restoration continuation: bounded source bridge

Date: 2026-10-11
Status: unreviewed research checkpoint; conditional derivation and proposed
constructional invariant. No suspension, lifecycle, or production gate closes.
Baseline: `18f13d938be7e7c85df8525c5dd2fb6a4c999671`.
Producer: assigned `prover` leaf `/root/freshening_restoration_bridge_proof`.
Exclusive output: this note. No delegation or implementation authority.

## Objective, authority, and frozen statement

Construct the next local-use continuation seam by induction over the actual
freshening/restoration/replay/typed-terminal owners. Governing authority is
`notes/design/2026-10-11-private-candidate-suspension-contract.md` §§3–6;
§7 supplies required future assertions, not established source behavior.
The recorded user approval selects retention of existing execution order,
saved opposite count with live indexed lookup, accepted-edge retention,
transactional rollback, and deferred unresolved external incidence changes.
The resumed-restoration source-correspondence note is conditional prior evidence.
The typed-drain terminal-handoff note describes a narrower synchronous foundation;
the actual source below supplies the bridge used here.

Fix one execution of the actual `Action::Local` selected by immutable source
schedule `S` at action index `a`. Its original binders are local slot `s`, local
identity `l`, source occurrence `O`, target component `v`, and use level `L`.
Fix the selected live scheme root `R` and boundary `B`, its one captured graph
`G`, occurrence `I = ConstraintOccurrenceId(O,0)`, cause `K`, and the one
`context_use` identity `U` allocated by freshening. Rows at or below the boundary
and nongeneric coordinates retain the existing source algorithm's meaning.
Canonicalization never rebinds any of these identities to another use.

Fix the completed fresh construction output `F`: mapped rows and terms, effect
operands, bundle/view/context/weight remaps, imported evidence remap, and original
`G`. Let `j` denote the next captured bound in **G's original ordered vector**.
For active bound `G.bounds[j]`, retain its prepared mapped relation, antecedent
snapshot, source-bound identity and owner polarity. If physical admission has
completed, fix restoration handle `r`, accepted emission `e`, retained raw owner
`o`, raw bound `b`, saved opposite count `N`, next index `n`, and active replay
handle `q`, if any. Fix q's frozen fiber heads/prior progress, ordered relation
batch `C`, queued cursor `t` and consumed cursor `c`. Repeated relation IDs in
`C` remain distinct indexed child occurrences. Fix any active typed drain's exact
ordered acknowledgement list `A`, completed cursor `d`, stage and return owner.

Required conclusion: for every finite successful continuation segment starting
at one of the stable boundaries below, interruption/resumption yields the same
ordered logical local-use event trace as uninterrupted execution under the
frozen hypotheses. It preserves one `U`, one accepted emission per original
bound admission, the saved `N`, live lookup order, exact replay lineage,
provenance, typed completion prefix and parent handoff. Completion is conditional
on the underlying segment completing; no termination assertion is added.

Logical events include fresh construction identities and remaps, mapped-bound
transport, accepted emission, indexed opposite selection, ordered replay
dependencies, child transfer, typed execution/diagnostics, acknowledgement,
parent advancement, final value link and local-route publication. Journal
preparation, resource samples, wait registration and pauses are administrative
steps. Their capacity/rollback duties remain required but are not equated with
an uninterrupted execution's allocation trace.

Exclusions: arbitrary external incidence commutation; authentic source reachability
of every compared state; lifecycle invalidation/withdrawal/recomputation;
readiness, recognizer or production certificates; complete Call/effect hygiene;
soundness, required principality, general mixed recursion and F5 cutover.
No provider, attachment, witness, or residual identity is quotiented away.

## Actual source constructors and consumers

All line locators refer to the pinned commit, not live worker edits.

| Responsibility | Owner | Exact local fact |
| --- | --- | --- |
| Source action selection | `candidate_source.rs:17–49,611–658,660–685` | `Action::Local` retains s/O/v/L in an immutable schedule. `Frame` currently stores schedule/index and Execute/PublishLocal, not a LocalUse child handle. The action index advances only after `execute_candidate_action` returns. |
| Actual local-use caller | `candidate_scheme.rs:1265–1302` | Looks up R/B/l, captures G once inside a route transaction, constructs I/K, freshens, admits the final link, then publishes `LocalFreshRoute { slot, local, occurrence, graph, rows }`. G and freshening locals currently live on the synchronous call stack. |
| One use and row mapping | `candidate_scheme.rs:891–940` | `begin_use` allocates U once. Canonical-row map shares one replacement per canonical source row; allocation depends on captured local status, level>B and nongeneric metadata. Resuming from this caller's beginning would allocate another U and can allocate another row family. |
| Fresh output before restoration | `candidate_scheme.rs:941–1138` | Bundle copies, view/operand copies, weight/context renaming, Function terms and evidence imports complete before the captured-bound loop. Terms for EffectOperand nodes may remain absent; their endpoints are in effect_operands. No currently retained freshening frame owns these vectors/maps. |
| Bound provenance and order | `candidate_scheme.rs:1141–1185` | Iterates G.bounds in order; preserves captured side, fresh-transports the original parent using U/context remap/source-bound identity, attaches mapped bundles, and supplies `FreshUse { antecedent, use_origin: U, source_bound, mapped_relation }`. Only after all bounds complete does it return root term and rows. |
| Accepted restoration | `candidate_extrusion.rs:406–564,655–675` | Origin/evidence admission and physical append produce e. Begin reserves restoration storage first, inserts once, canonicalizes o/b, saves N, and retains r/I/K. There is no safe exposed suspension point between insertion and ownership of r. |
| Live indexed restoration | `candidate_extrusion.rs:567–627,677–721` | Each future index re-reads the current canonical owner, current direct length and exact vector, canonicalizes selected endpoints, builds oriented task/fiber inputs, generates q, and links it to r. An active q is driven before n increments. |
| Restoration ownership | `candidate_context.rs:75–93,1760–1799` | r owns e/N/n/I/K and q. q has its restoration backpointer. Advancement takes the q pointer and increments n once; retirement is separate. Drive never calls insertion again. |
| Exact replay batch | `candidate_context.rs:50–73,2855–2936` | Snapshots heads/prior; incoming-use prior is `(None,None)`. Traverses lower cursor outside upper cursor, retains both parent IDs in Replay dependencies, and stores ordered C/t/c independently of replay-head progress. Generation is synchronous; no mid-generation cursor is yet retained. |
| Transfer and completion | `candidate_context.rs:1808–1863,2938–2970`; `lib.rs:12351–12377` | Transfer reserves undo/queue capacity before t advances. Incoming provenance requires t=c on entry. Once transferred, queued work owns the child; replay's c cannot advance until exact acknowledgement. The synchronous replay driver is not a suspension-aware parent. |
| Typed body and terminal | `lib.rs:11840–11957,12190–12306`; `candidate_context.rs:20–43` | Owns initial task/I/K, prior processing scopes, popped item, Function stage, transitions, ordered acknowledgements and d. Diagnostics finish before Acknowledgements. Terminal completes A[d], increments d, reaches ReturnReady, then pops/restores scopes and returns transitions. The body has no general resume entrypoint. |
| Terminal commit/rollback | `candidate_context.rs:1569–1598,1661–1712,1725–1741`; `lib.rs:9162–9190` | Commit resets only preparation fields on live drains; retired replay remains while a live r points to it. Undo can restore a pre-existing drain with exact acknowledgement allocation and stack position. These facts do not journal a future freshening/local-use frame. |

The baseline's outward source suspension observes synthetic support only at
`step_candidate_source` entry (`611–623`). Completed callers supply READY
(`569–578`). It does not establish a nested fresh-use suspension route.

## Required retained state and stable boundaries

The following is a proposed continuation invariant, justified by the source
reads above. Names describe ownership, not a prescribed new public API.

| Parent stage | Required retained state | Allowed next transition |
| --- | --- | --- |
| FreshReady | S/a/s/l/O/v/L/R/B, owned G, I/K/U and F, original accounting ownership, j=0 | Prepare the next captured bound using F. Never recapture G or restart `begin_use`. |
| Restoring(j,r) | Same fresh output; current bound's mapped relation/evidence; r/e/N/n and any linked q | Drive r; never call begin-restoration for j again. |
| ChildActive(q,index,drain) | Exact q/C/t/c, I/K, queued work/current popped work and drain stage/scope/A/d | Resume its existing owner, or run its still-atomic body. Never choose another child while the existing drain is unfinished. |
| ChildReturn(q,index,result) | Terminal result and exact completed child ownership, with the child frame no longer active | Consume the return exactly once, then select the next C index or record q completion. |
| ReplayComplete(r,q) | q retained/retired, every C child consumed, no active child return, n unchanged | Advance r once, release its q pointer, then perform the next live opposite lookup. |
| BoundReturn(j,e) | e retained by parent after r retires; no active restoration | Advance j once and prepare G.bounds[j+1]. |
| FreshReturn | Original G/rows/root term/I/K retained; all captured bounds complete | Admit the original final value link and retain its completion before publication. |
| PublishRoute | Final link complete; original G/rows and source/local identity retained | Publish LocalFreshRoute once; then complete the source action and advance a once. |

Any implementation can combine adjacent stages atomically. It cannot leave an
observable pause between retiring/popping a child and recording its return in
the parent. A handle to a removed frame is insufficient. A typed drain's final
acknowledgement alone does not mean its ReturnReady scope restoration/return
handoff has completed.

FreshReady is the boundary **after construction/imports at line 1138**, before
restoration. It is not the return from `freshen_candidate_graph`, which is after
all restoration. If suspension is supported only after r exists, the parent
still needs F for the remaining bounds and final root/rows. Graph capture,
structural freshening, mapped-relation/bundle preparation, physical insertion
through r retention, whole replay generation through parent link installation,
and typed body through diagnostic completion may remain indivisible in this
bounded seam. No suspension inside those intervals follows from this note.

The owning frame must retain all needed F values. `canonical_rows` and the
structural work stack have no subsequent reads after construction; view/weight
remaps and context roots likewise finish construction before the bound loop.
They may be dropped at the completed boundary only with corresponding accounting
transfer. G, rows, terms, effect_operands, bundle/context/evidence remaps and U
have later consumers. This is a direct forward-use argument, not recovery from
endpoints. Under §3 a more general mid-construction frame must also retain the
unfinished work and completed remaps; that broader frame is outside this seam.

## Hypotheses of the conditional derivation

1. Both runs begin at the same successful source-owned prefix with identical
   retained graph, identities, exact evidence/fiber/context records, physical
   bounds, semantic memo/diagnostic state, queue and logical continuation stages.
   The future frame representation stores the required state above before pause.
2. Original G and source schedule remain immutable while owned. Resume dispatches
   the innermost retained stage, and parent cursors advance only on explicit
   complete returns. Atomic intervals have no suspension exits or hidden callback
   that returns suspension without retaining its own continuation.
3. Mutation schedules are matched at the same logical callbacks/lookup boundaries.
   Unmatched external mutations during a pause are allowed only when their exact
   dependency/representative/vector/fiber/context/provenance footprint is disjoint
   from this continuation. Otherwise they are deferred under §4. This premise is
   **not established** by the five inspected owners.
4. Current representatives transport retained raw endpoints with their original
   relation/evidence parent. All saved indices are valid; N is never recalculated,
   n is never replaced by an endpoint cursor, and an already generated C is never
   regenerated from current heads. Typed execution and its ordinary callbacks
   are deterministic from the compared state.
5. Typed work and diagnostic helpers run atomically until their retained terminal
   boundary unless a separately justified resume path owns them. The completed
   diagnostic state, ordered A and d are retained; the queue and processing scopes
   remain owned. Acknowledgement order is valid for each operation's c frontier.
6. Every necessary allocation/preflight succeeds for the compared successful
   segment. Route commit journals/retains the new parent frames and handles, and
   failures restore their exact pre-route state. Existing terminal preflight resets
   are honored on each new route. Accounting includes retained and rollback storage.
   These are future adapter obligations, not proven from old route success.
7. No lifecycle invalidation/recomputation occurs in this compared segment. A later
   lifecycle proof must insert original-order recomputation ahead of these stages
   and retain their inputs; it cannot infer validity from c/d or memo success.

## Constructive induction and terminal handoff

Relate states by equality of the semantic data in the frozen statement and the
logical owner stages. Administrative route-preparation fields may differ:
`d <= prepared_acks <= |A|`, with terminal preparation referring only to the
current journal. Induct over original captured-bound position j, saved opposite
position n, ordered replay-child consumption c, and typed acknowledgement d,
with each atomic source operation as one transition. These nested counters are
progress cursors, not a termination measure for arbitrary solver work.

At FreshReady both runs use the same G/F/U. Bound preparation computes the same
owner/item and mapped parent with the same source-bound identity and antecedent.
Atomic begin produces e once and stores r/N/n=0 before the boundary. Resuming
Restoring(j,r) enters drive rather than begin, so it cannot repeat admission.

When q is absent, equal current state yields the same live lookup at n, oriented
task and exact fiber inputs. The replay constructor enumerates the same ordered
parent pairs and contexts and installs the same C before its child boundary.
When q exists, the retained batch is used even if aligned earlier callbacks
appended other fibers. No marginal parent is independently selected on resume.

Transfer increases t once after reservations and gives ownership to exact queued
work. Until typed execution, diagnostics, and terminal return complete, the parent
remains ChildActive. Atomic typed body steps and matched callbacks produce equal
diagnostic results and ordered A. Terminal selects A[d], validates the corresponding
c, increments both semantic completion frontiers exactly once, and preserves
the still-unconsumed suffix. ReturnReady restores the saved scopes and transfers
the result to ChildReturn before the parent can advance. Only then may it select
the next child. A fully consumed q enables ReplayComplete, which increments n
once. At n=N, r returns the original e; BoundReturn advances j once.

At the final j, the original root term/rows are returned without freshening.
FreshReturn admits the same I/K final link, and PublishRoute publishes the original
G/rows exactly once before the source action index advances. This extends the
restoration-local conditional argument to its actual local-use parent obligations.

Commit resets `prepared_acks = completed_acks` and `terminal_prepared = false`
(`candidate_context.rs:1677–1682`). It leaves A, d, typed stage, q's c/t, r's n/N,
and all semantic identities unchanged. The next terminal step reserves its new
journal undo before A[d] completes. Thus the reset stutters under the relation:
it neither undoes a completed child nor proves parent completion. It needs **no
additional semantic completion counter in the parent solely for the reset**.
It does require the parent to keep its child/return/replay stage independently of
prepared fields and to journal its own advancement in the new route. The original
parent's absent LocalUse stage remains a real representation gap.

At this baseline, `retire_replay_candidate` refuses to reclaim retired q while a
live r points to it (`1661–1667`). That now covers the prior final-replay absent-handle
interval for both transactional and nontransactional restoration. After an ordinary
child returns, c can select the next batch entry without repeating its body. The
empty batch is retired by its own replay step. None of these cases permits advancing
n merely because the transfer returned `false`: `2938–2950` also returns false when
all work is queued but typed completion remains outstanding. The synchronous
incoming-use caller never exposes that state; a new suspension adapter must inspect
completion/owner state explicitly.

Under the hypotheses, insert/remove pauses and terminal journal resets by stuttering
between equal logical transitions. Induction yields equal finite event traces and
the required uniqueness/order properties. This is a **conditional derivation**
about a representation satisfying the stated invariant. The source map establishes
the old constructor order and the retained terminal facts, not the missing adapter.

## Falsifiers, obstruction, and proof-obligation economy

Concrete falsifiers for the proposed adapter are a second `begin_use`, recapturing
G after FreshReady, repeating an accepted bound's begin, reconstructing C from new
heads, advancing n on queue transfer, restarting a popped child, using a preparation
cursor as completion after commit, or pausing after ReturnReady pop before a parent
owns its return. Each violates a named forward owner invariant above.

The remaining incidence premise is unchanged from the conditional prior note.
For example direct opposites `[A]` and exact opposites `[X,Y]` give saved N=3;
after index 0, an unmatched external direct append B changes live indices 1/2
from X/Y to B/X. Saved count plus current canonicalization does not commute that
append with restoration. This is an internal operational discriminator, not a
source-generated counterexample or a contract-permitted disjoint mutation.
Representative merges can likewise change the flattened incidence. Aligned
ordinary callbacks must keep the live behavior, so freezing the original list
would violate §4.

After this one constructive attempt, the precise missing owner fact is: the
suspended mutation admission/scheduler identifies every retained continuation's
remaining representative/direct-length/exact-vector/fiber/evidence/typed-result
footprint and defers each unmatched intersecting mutation. The inspected source
checks synthetic support at source-action boundaries; it does not implement that
inventory/deferral at this nested local-use seam. No equivalent retry is attempted.

Economy audit: obligation preservation/deferral is A (correctness); natural local
fresh use and its original callback order are B. Arbitrary mutation commutation
is a stronger C assertion and is excluded here. Reconstructing the lost fresh
maps, accepted child return or original incidence from graph endpoints would be D.
The forward owners already possess F/r/q/A/d, so retaining typed parent stages
removes that reconstruction debt without changing inference. The audit leaves
the actual incidence/lifecycle correctness gates open.

## Checks, resources, runtime, and commit packet

Static checks only: committed `git show 18f13d938:<path>` line reads, committed
caller lookup, baseline/HEAD SHA256 comparison, and leased-note whitespace check.
Read-only Git inspection obtained the pinned input blobs. No Git mutation, Cargo,
test, source execution, benchmark, delegated agent or build process was launched.
One reasoning leaf; sequential lightweight read/hash commands, including short
read pipelines; no concurrent verification. The assigned reasoning envelope was
30 minutes; elapsed reasoning time and CPU/RAM were not instrumented. This is not
independent review.

Direct pinned SHA256 dependencies (all inspected committed HEAD blobs matched):

```text
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
f2e8c33ac3e0a61ec6611285adbb866a055ae791cebf5a7440de1f8795fa822e  crates/yu-solver/src/candidate_scheme.rs
beebddb214b80335a33a6e307e7809b98a21a286bbe73aef0fdfab4bfa7c570c  crates/yu-solver/src/candidate_extrusion.rs
085f98e667c47648986c052e2a3411f39361fe85017f8bc3ec2d5ca74e0e64f3  crates/yu-solver/src/candidate_context.rs
97a2fed4e4be960b9fbf0d97adb454dc72cc8d4683cef2963234f2cc22e76fca  crates/yu-solver/src/lib.rs
734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d  notes/design/2026-10-11-private-candidate-suspension-contract.md
032e5877d28e60cce2955a15bfffd1761dbc22f75975223f9ee4a396d51271e5  notes/progress/2026-10-11-resumed-restoration-source-correspondence.md
1f2df0b82beecd62572a1a5d9ae384627403beadcc3dd6e05fbeb148a8d706f8  notes/progress/2026-10-11-typed-drain-terminal-handoff.md
```

Routing: actual assigned role `prover`; configured requested default
`gpt-6.1-sol/high` (confirmed by primary; registered unpinned prover with those
agent defaults). Observed effective runtime model/effort: unknown. No Astra or
configuration reload is claimed.

One implementation-relevant invariant: **the source action owns one captured
fresh use and ordered bound cursor; each accepted bound owns one restoration;
each generated replay owns its indexed batch; each transferred child has exactly
one queue/drain/return owner; only a completed return advances its parent cursor.**
Journal preparation is separate from these semantic completion frontiers.

Next action: primary implements/reviews that retained LocalUse parent seam with
stable boundaries, keeping external intersecting mutations deferred until the
named footprint bridge is established. §7's authentic nested suspension,
late-edge invalidation, sibling recomputation, rollback and grouped publication
assertions remain unverified.

Commit packet: exact lease
`notes/progress/2026-10-11-local-use-restoration-continuation-proof.md`; baseline
`18f13d938be7e7c85df8525c5dd2fb6a4c999671`; changed dependency hashes: none
among inspected committed HEAD blobs. Concurrent working edits were not consumed
and require primary revalidation. Review status: producer-only, unreviewed,
conditional; no theorem/gate promotion. Checks already run: static committed
source/caller reads, dependency hashes and note whitespace. Proposed checkpoint
message: `Record conditional local-use restoration continuation bridge`.
Shared-record deltas left for primary/curator: record the retained parent invariant,
terminal reset distinction, baseline's final-replay handle retention, and unresolved
actual nested adapter/incidence deferral; keep lifecycle/source/production proof
gates open. Writes are stopped for adjudication and fresh independent review.
