# Value intrusion: retained-event activation correspondence

Status: Independently reviewed bounded mechanism theorem and source correspondence.
Baseline: `e450c1836c008aa0bb81d4ad7edab9788e2fb9c2`.
Owner: delegated constructive proof leaf; exclusive output is this file.
Authority: top-level inference principles §1.1; intrusion-value-type-association
“Approved extrusion-event qualification” and “Definition-root origin”;
parent-copy-scc-intrusion “Value-reference SCC clarification”, “Apply-result
source-fragment ownership”, “Nested Apply membership”, and “Definition-root
Value ownership”. The October 14 implementation record locates the code scope;
its review verdicts are not premises of this derivation.

This note proves a necessary mechanism correspondence for the current
private LocalSource route. Independent review is recorded below. It does not close native
source-global equality preservation, soundness, required principality, complete
Call, hygiene, termination, or public/F5 cutover. No source restriction or new
transport semantics is proposed.

## 1. Frozen obligation, domain, and meanings

The delegated obligation is: for every finite successful operation sequence of
the actual retained source graph/extrusion/reuse/settlement construction, every
current pending/activated type parent-copy group corresponds exactly to an
actual immutable source association whose endpoints share a Value-reference
SCC; successful complete drains enforce all and only equalities requested by
that qualification, modulo equality closure; distinct logical reuse retains
original event ownership; rollback restores the invariant. Additionally, the
Fragment DAG must preserve reachability and SCCs on original Values.

Quantify over one successfully collected, sealed candidate batch and its finite
single-session operation histories through the production entrypoints below.
Successful operations include successful suspensions, not merely whole-program
success. An error followed by the existing route rollback is a history step;
an interrupted private attempt before rollback is not a successful published
state. Complete drain means the actual drain reaches its completion receipt,
not that it merely stores constraints or generates a replay operation.

The original source envelope is authenticated successfully formed LocalSource:
Unit, Operation, Integer, Name, Apply, Group, Ascription, Lambda, and Block,
with exact ModuleDef/Local/Parameter resolved identities. Unresolved/ambiguous
Names produce no resolved-reference edge and are not asserted to have a
successful typing. The current carrier has no If/Boolean/String constructors.
Forged LocalSource arenas, arbitrary test-only calls that manually set processing
fields, direct mutation of a sealed Graph, cross-session IDs, and unsupported
source constructors are not actual production construction histories. They are
excluded at the statement's entrypoint, not after a failed proof attempt.

Let V be the tagged semantic identities interned by `candidate_value_graph`:
Module(DefId), Local(HirLocalId), Parameter(HirParameterId), and
Expression(HirOccurrenceId). Helpers are not members of V. Binders and lexical
owners remain their original tagged identities; no type row becomes a Value.
Let E be the immutable array of call associations `(origin,receiver)`. Let S(r)
be the immutable finite set of complete event IDs on relation r; None means
the empty set. Write Q(S) iff some e in S has mutually reachable endpoints
in the selected reference graph. No separate origin/receiver projections or
independently chosen witnesses are used.

An original extrusion occurrence o has its actual polar parent/copy records
P(o), including both Value and Effect kinds. A finished group g contains its
fixed interval of these records, with original source set S0(g). Each retained
reuse u has its own occurrence ID, group g, and complete source-set handle Su.
Define A(g) = Q(S0(g)) or Q(Su) for at least one retained reuse of g.
“Exactly” below is an iff for A(g), not a bijection between groups and events:
replay can retain several original events, and one event can reach several
extrusions. Original unqualified records remain unqualified historical records
when a later reuse qualifies the group. `activated` means its equality requests
have been registered; it does not mean all requests have already been consumed.

The mechanism claim has four precise conclusions at successful operation
boundaries:

1. On original Values, the retained helper graph has exactly the reachability
   and SCC relation of the source-selected direct reference graph.
2. Each group has immutable actual copy records and actual event handles;
   `activated(g)` iff A(g). Every activated group contributes its entire pair
   interval exactly once to `pending`; no unactivated group contributes one.
   The suffix at `pending_cursor` is the undischarged equality request sequence.
3. After complete drains, the row forests represent exactly the equivalence
   closure of all consumed retained requests, separately by kind. Thus all
   qualified requests are enforced, and no additional primitive row union is
   attributed to intrusion. Equality can incidentally identify other rows by
   transitivity, as allowed by the frozen “modulo equality closure” clause.
4. Reuse preserves each original record's occurrence/comparison/source set;
   rollback restores the preceding logical records, qualification registration,
   consumption position, row partition, and relation/source-set state.

These conclusions describe the actual retained event qualification. A further
claim that every transported event is the semantically required association for
every future source-global extrusion needs the source-global construction law.
This note supplies the current owners and operational retention below; it does
not silently assume that missing law or identify it with overall soundness.

## 2. Independent premises and owning entrypoints

| Premise / operation | Actual owner at this baseline | Use and limit |
| --- | --- | --- |
| Finite authenticated arena and original resolution/scope | `yu-hir/src/module/local_source.rs:262` (`form`), `:449` (`slot`), `:557` (Apply children); existing flat-formation proof §§2–4 | Fresh child slots, one completed expression per slot, lexical publication/restoration. This is the separate source-formation premise; no arbitrary arena assumption is hidden. |
| Register actual module root identity | `yu-solver/src/lib.rs:995–1001` | Original root/DefId registered; duplicate definition ID aborts collection. |
| Retain graph before native actions | `candidate_source.rs:170–176` | Uses the same LocalSource passed to emission. |
| Match call-check identity | `candidate_source.rs:397–414`; `candidate_value_graph.rs:120` | Both form `ConstraintOccurrenceId(apply.occurrence,0)`; source identity, not spelling, joins them. |
| Seal complete collection and session graph | `lib.rs:1409`, `:10112` | Graph precedes solving; solving does not append graph vertices, edges, or events. |
| Seed and propagate whole event sets | `candidate_context.rs:2589–2609`, `:2296–2343`, `:2630–2704` | Sources are relation-key fields; Function ports inherit the same whole set. |
| Copy and retain actual polar pairs | `candidate_extrusion.rs:21–28`, `:79–125`, `:226–255`, `:358–365` | Record only actual younger-row copies; level-local rows and atoms create no fake pair. |
| Group and reuse actual transformed child | `candidate_intrusion.rs:283–335`; `lib.rs:12362–12388`, `:12425–12467` | Original comparison plus actual rewritten endpoint indexes the group; current relation controls memo completion. |
| Settle and make equality operational | `candidate_intrusion.rs:473–596`; `lib.rs:11451–11463`, `:12238–12319` | Consume requests, canonicalize rows, retain/replay bounds, then drain the worklist. |
| Transaction checkpoint / inverse | `lib.rs:8989–8990`, `:9142`, `:9364–9494`; `candidate_intrusion.rs:107–166`; `candidate_context.rs:1605–1620`, `:1700–1722` | One route journal; exact saved logical sizes/cursor and inverse forest writes. |

The existing flat-formation result is used only for authenticated source arena
shape and original identity/scope. Its reviewed status does not prove graph
construction, qualification, source typing, or equality preservation. The graph
and activation statements below are derived from their actual constructors.

## 3. Fragment projection and SCC derivation

Define the direct graph D on V by two source-selected edge families.
First, a definition root owns every resolved Name in its initializer/body;
traversal changes owner only when entering a Block binding initializer, to that
binding's original Local ID. Lambda, Group, Ascription, Apply, and the Block's
final expression preserve the current definition owner. Second, each Apply
result owns the resolved Names reached through its callee/argument subtree by
recursively traversing only Apply and Name. Boundaries at other forms are the
existing selected Apply envelope; no wrapper/Lambda/Block membership decision
is invented here. Receiver resolution through Group/Ascription is a separate
operation and does not add Apply-fragment edges.

The first loop at `candidate_value_graph.rs:63–88` emits exactly the first
family: induction on the authenticated expression tree gives `owners[index]`
equal to its innermost owning definition root. Every Name emits its owner edge
to the actual tagged resolution, and no other arm emits a reference edge.
Local initializers switch to their own Local identity; their references never
become references of the enclosing root by traversal.

The second construction at `:93–116` allocates a fresh helper F(x) for each
Name or Apply, separate from the Value interning map. Name helper F(n) has
one outgoing edge to its actual resolved Value (or none for an unresolved
Name). Apply result R(a) has edge R(a) -> F(a). Its helper points exactly to
F(callee) / F(argument) when those immediate children are Name/Apply. In
particular, there is no edge to a nested Apply result Value. A helper-to-helper
edge follows a proper descendant in the source tree, so the helper subgraph
is a DAG. Names terminate such chains at original Values.

Consequently, every path between original Values with only helpers in its
interior starts at an Apply result, descends the exact selected fragment, and
ends at a resolved Name Value. It contracts to one edge of the second family
of D. Conversely each such direct edge expands to its result/helper/Name path.
Edges of the first family are retained directly. Decompose any retained path
at successive original Values; contraction gives a D path. Expanding each edge
of any D path gives a retained path. Empty paths are preserved as well. Thus
for every original u,v, `u reaches v` is equivalent in the two graphs, and
mutual reachability (including singleton SCCs) is equivalent. This proves the
projection without using a comment's asserted invariant as a premise.

`seal` at `:131–154` is iterative Kosaraju: the first traversal marks a vertex
before descent and appends it after all outgoing edges; reverse finish order
then traverses exact reverse adjacency, assigning one component label to each
reverse search. `edge` at `:39–44` installs both directions together on success.
The standard finish-order argument applies: a cross-SCC edge places the source
component later than its target in finish order; the reverse traversal started
at its maximal remaining component cannot enter a different remaining SCC.
All vertices are visited. Therefore component equality is mutual reachability,
and `qualifies` at `:156–157` is exactly Q on singleton event sets. The graph
must remain sealed: equal vertex counts alone do not validate arbitrary later
edge mutations. The actual collection/session ownership supplies that premise;
this is not a theorem about arbitrary public Graph method sequences.

Events at `:117–121` retain the original owner from the first traversal and
the actual callee Value selected by `expression_value` (`:51–56`). Name receivers
are resolved binder identities, not provider identities. Group/Ascription
stripping preserves that identity. An Apply-valued callee remains its own
Expression identity. No returned provider, subtype comparison, Function port,
copy metadata, or solver row installs an edge or changes these event endpoints.

## 4. Source-set and original-pair induction

Base state has no relations, parents, groups, reuses, or pending requests.
`candidate_context_seed` joins the exact checking occurrence to one existing
event and interns its singleton. `intern_sources` sorts/deduplicates complete
event IDs and returns a stable handle; `relation_with_sources` keys on
`(pair,context,sources)`, so differing source sets cannot disappear in endpoint
memoization. Neither interner edits an existing record.

Derived queue work obtains its relation from `candidate_context_admit`; the
`relation` helper copies the current processing relation's sources. Function
ports likewise use `relation` and retain their own field and parent dependency.
Canonical task transport (`:2807–2823`), bound formation (`:2910–2951`), fresh
transport (`:3242–3250`), and witnessed transport (`:3279–3291`) copy the exact
parent handle. Replay (`:3032–3067`) combines the two parent sets with
`union_sources`; it never forms the Cartesian product of origin endpoints and
receiver endpoints. Thus induction gives: every event ID in any retained set
names one unchanged actual E record. Attachment, witness, dependency, and
FreshUse IDs remain separate fields; this argument does not collapse them.

At production extrusion, `candidate_task_scope` sets the original comparison;
the transported work item's relation is installed before dispatch
(`lib.rs:12233–12288`). `candidate_extrude` assigns a fresh occurrence and saves
the parent-array start. Every actual younger-row branch allocates the same-kind
copy at target level, records copy/parent/polarity/target/occurrence, memoizes
it before following row bounds, and adds the ordinary one-sided link. Local
rows do not copy. Function argument/effect ports reverse polarity and result
ports preserve it. Effect-view tails and incoming allowances traverse their
actual row copies. Operation-local memoization deduplicates by endpoint,
polarity, and target, preserving opposite-polarity pairs as separate records.

The insert/transfer operations called inside this extrusion retain facts and
capture incidence (`candidate_extrusion.rs:390–570`;
`candidate_effect.rs:553–601`); they do not dispatch nested drains or change
processing. Thus the successful interval is homogeneous in its occurrence,
comparison, and sources. This discharges the premise behind the debug
assertion at `candidate_intrusion.rs:296–297`, rather than assuming it.
`finish_candidate_extrusion` indexes that actual interval by its producing
comparison and returned output. A copy-free extrusion has no group.

For every appended pair, `retain_extrusion_parent` tests Q of its unchanged
source set and, iff qualified, appends that exact parent index to pending.
The resulting group's initial activated bit uses the same immutable set and
frozen graph. Therefore initial activation equals Q(S0), and exactly one
pending index is present for every pair in a qualified new group.

## 5. Reuse, settlement, and complete drainage

The production memo-reuse branch first distinguishes a new relation/generation
from already completed work (`pair_is_current`, `lib.rs:11474–11483`). A new
relation's source handle is part of that identity. It recaptures each actual
retained diagnostic child before enqueueing it, rather than extruding the old
structural input again. `by_output` lookup uses the original comparison and
the returned endpoint actually present on that child (`:303–315`). A group
that produced a different endpoint is not selected by mere source SCC equality.

For a selected group with a different source handle, `recapture` records a
fresh reuse occurrence, original group index, and entire current source set.
It edits none of the original Parent fields. `(group,sources)` deduplication
means repeated identical evidence need not allocate another reuse record; it
does not identify two different source sets or rewrite the original event.
If Q(Su) and the group has never activated, it logs the group, flips its bit,
and appends precisely its entire original interval. A second qualifying reuse
cannot append it again. Hence induction establishes `activated(g) iff A(g)`
and the exact once-per-pair pending multiplicity. The event witnessing Q may
be in the qualifying reuse, not in the immutable original Parent.sources.

Settlement at `:473–501` reads only `pending[pending_cursor]`, loads that
actual Parent record, merges its copy and parent, and increments the cursor
only after merge returns successfully. Exhaustion resets dirty and returns.
Compression changes no partition. `merge_candidate_rows` computes the two
current roots; if equal, it consumes an already satisfied request. Otherwise
it points the copy root to the parent root, in the same kind. Therefore by
induction the represented partition is exactly the equivalence closure of
consumed requests. Representative writes occur only here, compression, and
rollback in `candidate_intrusion.rs`; row extension installs singleton roots.
This establishes both directions of the partition claim, not just that each
requested pair is eventually equal.

Equality reaches consumers: `canonical_value`/`canonical_effect` consult these
forests; bound insertion and replay canonicalize endpoints; both copy bound
sides are appended to the parent; parent level becomes the minimum and
non_generic becomes the disjunction. Context incidence is transported with
ParentCopy witnesses, then all retained bound keys undergo canonicalization
without editing their original fibers. Every current parent lower is replayed
against the current uppers. These are actual loops at `:539–596`, not an
inference from stored constraints alone.

Crucially, that settlement replay calls `candidate_replay_bound`, whose
`candidate_context_drive_replay(...,None)` path queues explicit child relations
and acknowledgements (`candidate_extrusion.rs:766–807`;
`candidate_context.rs:3186–3201`). It does not synchronously dispatch another
extrusion or recursively enter settlement before the cursor increments.
Thus the falsifier “nested settlement consumes the same current index twice”
is excluded by the actual settlement call chain. Synchronous restoration
replay elsewhere has its separate owned typed drain; it can settle pending
work before returning, but it is not invoked on this settlement chain.

At Transport with no current item, `step_typed_drain` calls settlement when
the worklist is empty. It then pops any newly queued child and repeats normal
Transport/Context/Dispatch processing. Diagnostics is entered only when no
item remains and dirty is false. Any later extrusion sets dirty; the next
empty-worklist visit settles its new requests. Therefore a finite successful
complete drain cannot return with an unconsumed pending suffix or unprocessed
queued settlement child. Replay completion is owned by the drain's explicit
acknowledgements, not by storage of its child list. No termination or fairness
claim for infinite histories is made.

The operational row-union/consumer conclusions above do not assert that adding
these equalities preserves all original source typings. That is the separate
equality-preservation theorem. Nor do append/replay loops alone prove global
physical-incidence completeness under every source/generalization route.

## 6. Rollback derivation and failure boundary

`begin_route_transaction_for` rejects an already active route journal. At the
checkpoint it saves the intrusion arrays' lengths, pending cursor, activation
log length, reuse length, generation, next occurrence, dirty, forest inverse
log, and effect/context checkpoint. For each root union the prior pointer is
logged before publication; compression logs each old pointer. Row journals
precede target bounds/level/non_generic changes. Worklist pushes/pops are
inverse logged by their owning queue. Thus failures after partial copying,
reuse recording, registration, merge, or queueing are not assumed atomic.

`State::rollback` first restores effect/context state and replays forest
inverses in reverse order while rows still exist, then truncates new roots and
parents. It resets each group newly activated after the checkpoint, truncates
pending, restores its cursor, and only then truncates new groups. It removes
exactly the post-checkpoint reuse keys/records and output-index entries for
new groups; existing group indexes are immutable. Generation/occurrence/dirty
are restored. Context rollback removes only new interned source sets and
relations and restores original processing. The route owner restores row
bound lengths, flags, levels, metadata and workspace queue effects. The sealed
source graph is unchanged throughout.

Consequently the projected logical state for conclusions 1–4 equals the saved
state. In particular, an old unqualified group activated on a failed reuse
becomes unqualified again, and a failed drain's consumed prefix becomes pending
again. Repeating an occurrence ID after rollback is confined to discarded
records; no surviving occurrence is retargeted. Capacity/accounting/diagnostic
identity equivalence is not part of this conclusion. A failed attempt that is
discarded instead of rolled back likewise cannot publish its partial equality.

## 7. Scope still open and next action

This is a direct induction and source-path projection, not an executable probe.
The mechanism theorem supplies retained-event authenticity, exact activation
registration, cursor consumption, operational representative equality, and
rollback on the inspected private path. The original source-global parent
still needs its native construction law: that actual origin/receiver event
sets propagated through every source constructor, replay, fresh-use and
generalization are precisely the occurrences the selected semantic operation
requires, and that their equalities preserve source typing and required
principality. In particular, replay unions retain whole events but retaining
them does not itself justify their applicability to every newly formed
extrusion. No authority for a new general association convention is inferred.

The first remaining premise belongs to those source/transport owners, not a
new inverse reconstruction layer. This packet attempted one direct construction
method; it did not repeat two equivalent failed routes. If the same global
association law remains untouched after a second different attempt, the
existing proof-obligation-economy audit applies: retain evidence at its original
owner without weakening ordinary inference or changing the selected theorem.
No parent gate is reclassified or promoted here.

Independent `compiler_referee` review passed the frozen theorem at baseline
`e450c1836c008aa0bb81d4ad7edab9788e2fb9c2`, artifact SHA-256
`4cf75387df6c88b1fac939b15de2042e909687005ecb38847a714afa2a4a7564`.
The review checked source formation, helper projection, group/source homogeneity,
memo output selection, settlement non-reentrancy, exact registration and equality
closure, and rollback order. It found no blocking or major issue. Its sole minor
finding concerned the read-process provenance sentence corrected below.

The primary accepts the four mechanism conclusions in §1. They discharge that
bounded mechanism obligation and supply its lemma to the existing source-global
gate; they do not discharge the separate applicability or typing-preservation
premises above. The executable playground now exposes the same retained events,
groups, representatives and pending cursor, so subsequent source construction
work can check these concrete owners while reusing this result.

## 8. Checks, snapshot, and commit packet

Static inspection used `nl -ba`, focused `rg`, read-only Git HEAD/diff/status,
and SHA-256 hashing. No compiler code, tests, expectations, shared records,
configuration, or questions changed. No Cargo/build/test, executable probe,
benchmark sample, child process worker, or Git mutation ran. This leaf used
up to four concurrent lightweight shell reads; no heavy CPU/RAM process was started.
Requested runtime: `gpt-6.1-sol` / high. Observed effective model and effort:
unknown; role registration/pin inspection does not establish live settings.

Final dependency recheck: HEAD remains the pinned baseline. Concurrent playground
edits add only read-only observation accessors to `candidate_intrusion.rs` and
`candidate_value_graph.rs`, and make the latter's Value enum crate-visible.
The inspected delta changes no constructor, qualification, pending/activation,
merge, rollback, or graph edge. This derivation remains pinned to the original
baseline locators/hashes. Observed concurrent hashes are respectively
`77b145ed8a8bf2fae30a07ed74d11a29f38d18930f92e3c1c10456244fe9402e`
and `a8449a11b1db02080c8c8cea536a23e07a79917951174971e65ba05be1e2073e`.
They describe the observed delta, not independent review of the playground.

Direct dependencies (SHA-256):

| Path | Hash |
| --- | --- |
| `crates/yu-solver/src/candidate_value_graph.rs` | `a9f4510275793852353b0346b32247eb8b416c5d3f0966b188df175c508ec367` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `f6ef373b106b8d76a94053856b0dad0e9427462a782121c6af9d28932b1c3685` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `ed3e213e943a553943784e409194723f64acb810a0bcf06607ee95b0eb4e4ed1` |
| `crates/yu-solver/src/candidate_context.rs` | `ed2981e436e94353411b4a976c09872edd345e381a5847941a7908ffe04005e0` |
| `crates/yu-solver/src/lib.rs` | `7c2164a03c3f7aa4229c69daff557475fb7b2806907fc5950454fab947d6d917` |
| `crates/yu-solver/src/candidate_source.rs` | `e62256c55c68d815ef7f23f87bb7fe48d0f427571a836557e7314dd0f0616d1f` |
| `crates/yu-solver/src/candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `crates/yu-hir/src/module/local_source.rs` | `8008b84738990cb22199d386129ecb810f86c907e222da40411cddb18eb279f7` |
| `notes/theory/2026-10-13-flat-local-source-formation-proof.md` | `4f9c43ece1127baf29d3b5737a96abd41f9baeb16115b654b73d2f03bec74424` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/design/2026-10-12-intrusion-value-type-association.md` | `531a9efae0ab7e03bfbd2f41cd7da86078e2fc8e67675d2c5c941972409f4e89` |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |

Commit packet: exact leased path
`notes/theory/2026-10-14-value-intrusion-activation-correspondence.md`;
baseline `e450c1836c008aa0bb81d4ad7edab9788e2fb9c2`; dependency hashes above;
Original producer packet: Draft/unreviewed, no self-certification; the primary's
subsequent independent-review adjudication is recorded in §7. Proposed checkpoint message:
`research: derive retained value intrusion activation correspondence`.
Shared-record deltas left to primary/curator: record this necessary mechanism
candidate and its pending independent review; keep source-global association,
equality preservation, soundness/principality and F5 OPEN; link its exact
remaining source/transport-owner premise after adjudication. No shared record
is edited by this leaf.
