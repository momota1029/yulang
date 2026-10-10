# Current-component generation: source and lifecycle correspondence

Status: frozen, unreviewed research characterization. No implementation,
independent certification, language decision or gate closure.

## Objective and authority

Inventory the current candidate's recognizer inputs, mutation owners, dependent
reuse/publication and route undo against Authoritative
`notes/design/2026-10-10-contextual-attachment-admission-design.md` §§4–6.
This is complementary source correspondence; it does not repeat ordinary-HIR
fixture search, the origin falsifier, or the constructive lifecycle theorem.
The primary owns their adjudication and the main proof lane.

Baseline: `4e5e60c81d834aafd736d45f28a1f197d012254a`. The assigned output
lease is this note alone. Static readers inspect the owning solver modules;
there are no tests, builds, executable models, child workers or Git mutations.

Accepted decisions retained: exact contexts for the two reviewed circuit
classes; attachment grouping per concrete set of one exact annotation
occurrence; retain unsupported late edges; withdraw dependent results and
privately defer without source rejection; atomically restore on failure and
allow a supported retry. Negative concrete source admission remains disabled.
The callback example has no established output. The reviewed interpretation
allows certification of the complete **currently generated** component with
future mutation invalidation; a schedule-completion token is not required and
does not establish complete current input or observation coverage.

Direct dependency SHA-256 values, inspected at the baseline:

| Path | SHA-256 |
| --- | --- |
| governing design above | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `crates/yu-solver/src/candidate_context.rs` | `2897c168c02640443a2f1280286a648853afe08324294c53f1c95d373ac3a337` |
| `crates/yu-solver/src/candidate_effect.rs` | `2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/candidate_scheme.rs` | `582bfb741315534dacf7290bb5618452bb55d9949a8aac691d8d01b93720de11` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `3fd1c7234c38013343e1c2e72bfed06c4eecdf7173e27d7581e11d6df84f0b3a` |
| `crates/yu-solver/src/candidate_source.rs` | `8adc289142dd78a625184dd661fb162e49f24532a19c7c4f9e114e604c0966a0` |
| `crates/yu-solver/src/lib.rs` | `9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1` |

Line locators below refer to these bytes. `context`, `effect`, `intrusion`,
`scheme`, `extrusion` and `source` abbreviate the corresponding modules above.

## Claim class and bounded derivation

**Source fact:** no current production caller uses `State::retained_input`
(`context:393`). Its callers found by repository source search are tests.
`CircuitEvidence` borrows live retained records and owns selection masks; it
does not retain an authorized certificate or publication generation.

**Bounded derivation:** for any arguments for which this function returns
`Ok(input)`, `input.completeness` is `Incomplete` and includes
`FilterObligationsUnavailable`, `ProducerReadinessUnavailable` and
`DependentObservationsUnavailable` (`context:535–545`). Each flag is appended
unconditionally, and the only successful constructor chooses `Incomplete`.
Thus even valid identity-only input with no missing references cannot yield
`Complete` through this implementation. This is a direct control-flow result;
it assumes only these frozen Rust statements execute with their ordinary
meaning. It does not prove a source cycle class or a compiler failure.

The borrowed Rust reference prevents mutating the same state during this one
borrow. It supplies no persisted-generation guard after the borrow ends.
`ProducerReadinessUnavailable` is the existing enum spelling, not authority
to require completed source schedules. Its future discharge must establish
the current-component coverage required by §5.

**Missing implementation premise:** a recognizer and every user of its results
must share a complete mutation/dependency contract. `intrusion::generation`
currently increments only in `merge_candidate_rows` (`intrusion:535,594`).
That counter cannot alone authenticate the different retained-input changes
listed below. Existing ordinary memo reuse is not thereby a demonstrated bug:
there is no accelerated certificate result to become stale today.

## Recognizer input closure and mutation inventory

`retained_input` closes roots in both directions through typed dependencies,
ordered/shared context children, payload/view links, referenced bound keys and
all fibers at keys touching selected views. It retains origins, bundles,
inferred-entry incidence and borrowed parent records. This closure is not the
SCC graph built by `settle_candidate_intrusion`; the latter follows physical
Value/Effect bounds, Function ports and view tails, and uses actual recorded
parent/copy pairs to select equality merges (`intrusion:358`). A future
recognizer needs both complete generated structure and authenticated incidence;
neither graph alone supplies all §5 inputs.

The table is an exhaustive category inventory of the inspected owners' retained
input and dependent state. It is not a proved enumeration of every possible
compiler transition. Future recipes/certificates have no current writers to
enumerate. An unrelated allocation need not invalidate a component; relevance
must include changes that enlarge its closure or merge its previous boundary.

| Mutation / exact owner | Input or consumer affected | Existing undo / missing lifecycle owner |
| --- | --- | --- |
| `State::context` (`context:1256`) and `rename_contexts_impl` (`:793`) intern exact constructors | Operation order, shared child identities, weight/certificate handles. Existing nodes are append-only; new reachable nodes change input | Context length/intern table rollback; no component invalidation hook |
| `source_weight` (`context:1360`), `candidate_signature_view` (`effect:598`), view copy/remap (`:671,:697`) | Allowed set, owner, exact position, scoped attachment instance, ordinals, tail, dormant unit-PUSH evidence and payload/view agreement | Weight/view length checkpoints; copies retain independent source weights. Live words remain zero-sized arrays. No live PUSH/POP producer or circuit authority |
| `candidate_effect_contribution` (`effect:729`) | Nominal effect, exact source origin and contribution instance underlying a Contribution endpoint | Contribution length checkpoint. `RetainedInput` accepts views/parents but no contribution slice; it does not itself expose this resolved operand metadata |
| `retain_bundle`, `bundle_incidence_insert`, `bundle_link`, `bundle_edge`, `activate_bundle_transports` (`context:1283–1350`) | Annotation set incidence can grow on existing relations and through existing/new diagnostic or transport paths | Bundle/source index/incidence/transport append logs rollback. Transport index is a derived index; incidence additions, not lazy index allocation alone, affect coverage |
| `State::relation` (`context:1418`), `candidate_context_admit` (`:1652`), Function admission (`:1675`) | Typed endpoints and exact context; Function field, Swap/Preserve, optional Derived incidence | Relation keys/pair-head chain checkpoint; dependencies/edges checkpoint. Nonidentity Swap is structurally retained but live consumer rejects it; Function incidence is marked inert by input builder |
| `retain_inferred_entry` (`context:762`), `admit_lambda_fact` (`lib:11121`), `candidate_context_seed` (`context:1614`) | Actual lambda entry/returned row incidence, cause, exact seed occurrence and optional entry handle; a repeated relation can acquire another origin | Entry/origin lengths checkpoint. No entry-authorization consumer. Origin append needs coverage independent of relation/dependency insertion; existing falsifier already establishes that seam |
| `State::dependency` and `edge` (`context:1445,:1479`) | Derived, ordered Replay, FunctionPort, Transport, exact source keys, use origin, reasons; edges also propagate bundles | Dependency/edge logs checkpoint. Diagnostic adjacency deliberately excludes Transport; cannot be reused as a complete certificate invalidation index |
| `State::attach` (`context:1546`), `candidate_context_bound` (`:1870`) | Context fibers at an existing physical key, post-check context and origin dependency | Bound-head stack checkpoint; another fiber may change recognizer input without another physical bound |
| `candidate_insert_bound_impl` (`extrusion:402`), `candidate_apply_effect` (`:726`), candidate Value dispatch (`lib:13015`) | Canonical owner, level-selected side, direct rows, exact lowers/uppers, cached lower/upper flags, future opposite replay and filter receiver registration | Existing row-length/flag/metadata journal plus contextual fiber before physical push. Sets SCC dirty; does not increment certificate generation |
| `candidate_bound_origin`, transfer (`effect:327,:436`) | Bound's source owning pairs and conflict-replay incidence, including duplicate physical endpoints | Effect origin journal. Context fiber/dependency is installed before origin-key dedup; origin changes remain separate input changes |
| `candidate_context_execute`, `post_check_context` (`context:1807,:1560`) | Discharged state changes later transport/capture semantics; receiver Allowance bounds keep executable current/future checks | Discharge append log; synchronous `checking_filters` scope restored on return, not checkpointed. A future certificate must authenticate checks/registrations, not infer them from discharge alone |
| `candidate_capture_incidence`, splice, register (`effect:372,:402,:426`) | Which source/Allowance relations are discovered from symbolic tail capture, including third-owner incidence after equality | Effect bucket/link/key undo. Metadata is deliberately not a solver/SCC edge |
| `candidate_context_replay_impl`, `replay_progress` (`context:1930,:1539`); restore/replay (`extrusion:635,:684`) | Ordered lower/upper product, exact contexts, replay dependencies, and cursor-based suppression; incoming use replays diagnostic obligations even with old dependencies | Replay-head undo; cursor is derived progress, not proof of complete observation coverage. Certificate-dependent cursor reuse would need generation checking/reset/recompute |
| Extrusion (`extrusion:1` onward), parent retention (`intrusion:171`), row merge/compression (`:513,:305`), canonical bound transport (`context:1996`) | Level/polarity maps, parent/copy provenance, representatives, effective endpoints, levels/non-generic metadata, transported fibers/bundles and opposite products | Parent length, representative edits, row undo, context transport logs. Equality generation exists. No authenticated certificate component union/split/rebase owner |
| `candidate_annotation_variable`, `candidate_formal_effect_variable`, formal domain installation (`effect:823,:844,:938`) and fresh row constructors | Scoped source-coordinate identity, level and genericity; formal Function endpoints | New rows truncate, named/domain maps have effect checkpoint undo. No lifecycle proof covering their relevance to a persisted certificate |
| `initialize_candidate_source_levels` (`source:507`), `fresh_value_at_level` / `fresh_effect_at_level` (`lib:10061,:10092`), Function term construction (`lib:10171,:10187`) | Initial levels, formal registration `native_root`, newly available rows and immutable Function ports referenced by future relations | Initialization precedes candidate execution; new row lengths are journaled. Native-root setup has no route undo and must remain outside any persisted pre-initialization certificate. Immutable term allocation alone does not enlarge a component until referenced |
| `capture_candidate_graph_inner`, `freshen_candidate_graph_inner` (`scheme:567,:813`) | Capture's row/bound/context/bundle/view closure, canonical row selection, per-use attachment map, renamed sharing, replay on retained/nongeneric rows | Capture is local observation; freshening mutates live state under caller transaction. Local scratch remaps drop; context-use counter checkpoints. Capture has no certificate stamp or dependent observation registration |
| Source action execution and local installation (`source:549`, `scheme:1087,:1091`) | Current/future producers and availability of live local roots; `Action::Local` may capture before later actions | Local slots installed inside a route are journaled. Root action schedules are restored after removal but are not route undo records. No persisted schedule cursor or certification readiness token |
| Active roots/uses and staged graph publication (`scheme:681–775`) | Which recursive/module roots and uses can supply constraints; member graphs become visible after member schedules, but future uses can mutate live roots | `active_roots`, `active_uses`, `graphs[position]` have no entries in `intrusion::Undo` or `RouteMutationJournal`. Current failure discards session; resumable component deferral needs an explicit owner |
| Pair completion, typed memo/diagnostic edges, conflict creation/report (`intrusion:223,:257`; `lib:12164,:12272,:12719,:13331`; `effect:469,:524`) | Work suppression, diagnostic completion/witnesses, exact source errors and result observations | Existing insertion/save-once undo and diagnostics scratch clearing. No dependency-indexed certificate withdrawal/recomputation owner |
| Fresh routes/local routes, final observation freezing (`scheme:1039,:1117`; `lib:10273,:16755`) | Visible use records, captured graphs/rows, final frozen candidate data/errors/projections | Route lengths/slots undo; member publication and final freezing are outside that footprint. No dirty/deferred publication barrier |

Resolved effect declarations, HIR source positions, source schedules and immutable
Function term children are read dependencies, not arbitrary in-place mutation
sites in these modules. A future certificate must retain their identities and
actual operand/port incidence. Session brands and allocation/capacity/peak
counters are identity/resource bookkeeping; increasing capacity alone is not a
semantic input mutation. Exhaustion remains an allocation failure, not the
private unsupported-component deferral selected by §5.

## Dependent reuse and publication inventory

Requirements below come from §§4–5; they are not claims that the listed objects
already depend on an accelerated certificate. Existing ordinary facts and checks
must not be indiscriminately erased. Withdrawal targets only the consequences
whose justification used the invalidated generation, retaining exact newly
admitted input and all independent origins/support.

| Reuse/publication seam | Current behavior | Required certificate-dependent treatment |
| --- | --- | --- |
| `pair_is_current` (`lib:11354`), completed map (`intrusion:223`), `enqueue_item` (`lib:12123`) | Relation + SCC equality generation suppresses work; raw endpoint pair owns diagnostics | Guard accelerated completion by current component/certificate generation; withdraw/reopen affected work before duplicate suppression; queued old results cannot publish |
| Replay heads and post-check discharge | Cursor suppresses old products; discharged relation supplies identity to transport | Withdraw or recompute certificate-based progress/discharge and resulting fibers/registrations; preserve authentic ordinary checks |
| Context relations, fibers, origin/dependency graph | Exact construction/provenance retained | Keep original inputs and unsupported late edges; identify acceleration-created outputs separately so withdrawal cannot erase inputs or alternate justification |
| Value memo children, witness/completion and reverse/SCC diagnostic scratch (`lib:12280` onward) | Ordinary diagnostics settle and cache witnesses | Withdraw certificate-dependent edges/witnesses/completions and resettle affected ancestors; ordinary diagnostic adjacency is insufficient for all observation dependencies |
| Effect conflicts and reported errors (`effect:469,:524`; `lib:13331`), operand observation (`effect:256`) | Conflict cache replay reaches source occurrence/cause; reported keys deduplicate errors; handles check session brand and current array bounds | Recompute any certificate-dependent conflict/report and its occurrence projection; cached pair identity, brand or reported-key presence cannot authenticate certificate generation |
| Receiver filters, active-family checks, residual recipes and gamma projections | Ordinary Allowance bound consumer exists; complete authentic attachment/filter/recipe implementation absent | Register every current/future check/query and reverse feedback, including both projection directions, in the certificate dependency set. Future recipe owner is missing, not discharged |
| Captured `Graph`, source-local scheme, `FreshRoute`, `LocalFreshRoute` | Graphs are use-time live observations; member/local roots route subsequent uses | Generation-stamp/recompute any accelerated view or dependent publication; local root identities alone do not establish valid captured contents |
| Member graph staging and `finish_candidate` / `finish_observations` | Member captures publish after schedules; finish returns frozen data with no closed types/schemes | Block affected graph/result publication while dirty/deferred; require recomputed dependent observations before visibility |
| Detached fold/evaluation and rename maps | Scoped local memoization, no production source consumer/certificate authorization | Do not promote detached numerical equality or local cache success to persisted admission authority; invalidate escaped per-use mappings on rollback |

The authoritative invalidation point is **before any old result can be reused
or published after a relevant mutation**. Hooking only newly allocated relation
IDs, only dependency insertions, or the end of `settle_candidate_intrusion`
does not cover this table. Component membership changes can bring an existing
origin, bound, filter, observation or outside edge into scope; closure-index
updates themselves therefore need one transactional owner. The present input
builder has no persisted component map or observation index to own that event.

## Private deferral and transaction ownership

The current candidate has no circuit state corresponding to
`dirty -> exact recertification -> clean new generation / privately deferred`.
`InputCompleteness::Incomplete` is borrowed diagnostic preparation, not a
suspension state. `SolveAvailabilityError::IdentityExhausted` from unsupported
nonidentity context consumption is an error, not §5 deferral. No recognizer,
count-family certificate, deferred observation queue or publication guard was
located. These are missing implementation owners under the approved contract,
not a proposal to change language meaning.

`with_route_transaction` (`lib:9155`) calls `begin_route_transaction`, commits
the store and releases intrusion undo on `Ok`, and calls
`rollback_route_transaction` on `Err`. Nested source work must fit the existing
single active route; `begin` asserts no journal and empty worklist/diagnostic
delta. A future private deferral must not use the error path to erase the newly
unsupported edge: retain exact inputs and suspension on the successful route,
while a genuine later route failure restores the pre-route state. No new public
return type or selected deferral representation follows from this audit.

Current undo hierarchy:

1. `RouteMutationJournal` (`lib:8102`) owns store facts/provenance, row lengths
   and metadata snapshots, new typed pairs, reported error keys/error lengths,
   routed-use records, extrusion generation, candidate route/local-route lengths
   and installed local slots. `journal_value_row` / `journal_effect_row`
   (`:9180,:9229`) save before mutation; rollback truncates and restores these.
2. `intrusion::Undo` (`intrusion:29,:85,:103`) owns representative/parent state,
   SCC generation/dirty flag, previous completions, prior typed memos and new
   diagnostic edges; it nests the effect checkpoint. It does **not** own active
   roots/uses or member graphs.
3. `effect::Checkpoint` (`effect:109,:159,:178`) owns views/contributions,
   processing, bound origins, capture buckets/links/keys, conflict and scoped
   annotation/formal maps; it nests the context checkpoint.
4. `context::Checkpoint` / rollback (`context:243,:1061,:1081`) own append tails
   for entries/bundles/weights/contexts/relations/dependencies/origins/bounds,
   bundle propagation index, replay-head previous values, edges, use counter,
   processing and discharge. `checking_filters` is scoped synchronous scratch.
5. Existing rollback restores semantic records while retaining some charged
   allocation capacities/peak counters. Retry equivalence concerns justified
   semantic observations and restored generation, not byte-identical capacity.

There is no undo slot yet for the proposed circuit certificate, its component
membership/dependencies, invalidated generation, observation support/index,
withdrawn **preexisting** results, deferred queues or publication status. Existing
length-only undo cannot restore an old result deleted in place; prior content
or an equivalent exact restoration owner is required. Also missing is the
component orchestration undo for `graphs[position]` and active-frontier edits.
`execute_scc_plan` (`lib:13831`) on error clears accounting scratch only; current
session discard avoids returning a partial frozen result, but is not evidence
of rollback followed by a supported retry in the same component.

§5's required failure/retry sequence is consequently still unimplemented:
certify the complete current component; add a late unsupported Function/Swap
edge; mark dirty and withdraw all dependent observations before reuse; retain
the edge and exact contexts while privately deferring publication; on route
failure restore certificate, dependency graph, observations and publication;
retry a supported route using only the restored generation. The conditional
proof can establish this sequence only after its actual source owners satisfy
the premises above. No source execution is claimed here.

## Smallest source-owned next gate

One recommended next action: freeze and independently review an implementation
contract assigning current-component mutation, observation and undo ownership
at the existing `candidate_context::State` / `RouteMutationJournal` seam,
including the member graph/active-frontier publication seam. Then implement that
bounded lifecycle foundation under a separate exact compiler lease.

The current source can exercise identity relation, origin, bundle, bound,
Function-incidence, equality and capture mutations. A lifecycle foundation can
therefore obtain source correspondence without enabling negative concrete
annotations. Its useful exit evidence is complete hook/undo/publication coverage
for the table, guarded reuse and restoration of preexisting results. It is a
partial internal gate; using synthetic certificates there would prove only the
lifecycle adapter under supplied certificate validity.

Exact two-circuit admission additionally needs source-owned executable
PUSH/POP formation (`source_weight`/`candidate_signature_view`, currently dormant
and zero-word), authenticated Function/entry operations, receiver/filter and
transport witnesses, actual component recognition and dependent finite observers.
No supplied fixture spelling or detached algebra can replace these owners.
The lifecycle foundation cannot certify the two cycle classes or authorize
concrete contravariant rows by itself. Complete mixed admission, residual/gamma
generation, Catch/Call, hygiene, soundness/principality and public cutover remain
unverified.

## Commands, coverage and resource report

Read the three mandated rules, orchestration/proof role guidance, yulang-proofs
skill, governing design, relevant current task/handoff records and owning source
sections using `cat`, bounded `sed`, `rg -n` and `sha256sum`. Searches establish
the located producers/consumers and absence of a production `retained_input`
caller in the inspected solver; they do not establish every source-wide path.
Two attempted nonexistent locators (`candidate_bound.rs`, `route_journal.rs`)
returned missing-file errors; their owners were resolved to
`candidate_extrusion.rs` and `lib.rs`. Some broad reader captures were truncated;
the relevant state definitions/owners were reread in narrower slices. There is
no incomplete executable search, seed/range, mutation run or oracle result.

Oracle independence: no Oracle binary or fixture was executed. The design is
the normative contract; frozen Rust is source evidence of current ownership.
They share selected authority and prior adjudicated premises, so this is not
an independent semantics oracle. The successful-input derivation above depends
directly on current source control flow and does not assume a modeled solver.

Resource use: one leaf, short shell readers (at most three independent readers
in an initial batch), one note write, zero heavyweight processes/builds/tests,
zero children and zero benchmark samples. CPU/RAM and whole-lane wall time were
not measured or specifically allotted in the packet; no numerical consumption
claim is made. Writing stops on delivery for frozen review.

Workflow deviation: two early `git rev-parse HEAD; git status --short` reader
calls were issued before the stronger packet prohibition on Git was noticed.
The primary was notified. There were no Git mutations and no further Git calls.

## Commit packet

- Exact leased path: `notes/progress/2026-10-10-current-component-generation-bridge.md`.
- Baseline SHA: `4e5e60c81d834aafd736d45f28a1f197d012254a`.
- Direct dependency hashes: table above; no changes observed at final recheck.
- Claim/review status: frozen unreviewed source characterization and bounded
  successful-return derivation; no independent review or implementation closure.
- Checks already run: narrow static source reads/searches, dependency SHA-256
  capture/recheck, artifact locator/lease integrity check. No tests/builds/probes.
- Proposed checkpoint message: `research: inventory current-component lifecycle owners`.
- Shared-record deltas left for primary/curator: link this inventory; separate
  SCC equality generation from certificate mutation generation; track missing
  dependent withdrawal/private deferral and member publication/frontier undo;
  keep exact recognition/source operations and negative admission gates open.
  No shared task, index, authority, theory or question record was edited.
