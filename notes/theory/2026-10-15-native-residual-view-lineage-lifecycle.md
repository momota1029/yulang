# Native residual views: lineage and lifecycle retention

Status: unreviewed research derivation and precise activation obstruction.
No theorem-status promotion or implementation authority.
Baseline: `146ca9d2a8713398c893a9cae026ae0c2fae593d`.
Branch: `research/simple-sub-intrusion`.
Exclusive lease: this file. Leaf; no delegation, compiler edits or Git mutation.

## 1. Frozen objective, quantifiers and exclusions

Original parent, unchanged: for every originally admitted shallow Catch H and
one original scoped assignment sigma, preserve its scrutinee, original
operation/value-arm binders, complete provider/dependent interfaces and raw
resumptions. Remove exactly consumed eligible contributions; retain protected,
independent, unmatched, outside-arm and resumed contributions, including
same-family survivors. No witnesses may be selected independently for marginal
projections. H1/H2/U remain OPEN; H3/P are disabled; production/F5 is separate.

Assigned structural H2 statement: for every finite successful native lifecycle
trace and every finite set of distinct admitted Allowance/view construction
events in its initial state, retain distinct constructor lineage through
extrusion, capture/generalization, fresh use and qualifying parent/copy
intrusion, even when their source or gamma row representatives become equal.
Retain within-use sharing and every current/future replay obligation. This
statement quantifies over actual recorded native constructions, not all possible
abstract residual recipes or source Catch implementations.

Freeze the following meanings before deriving anything. A native view is the
live index `v` of `effect_algebra.views`; write `A(v)` for Allowance(v), `S(v)`
for Support(v), `M(v,k)` for AnnotationMember(v,k), and `t(v)` for its optional
tail. A native admitted cut is a negative bound `s <= A(v)` admitted with its
actual relation/evidence; an allocated view alone is not an admitted cut.
`r(x)` is the actual row representative. Each row keeps its actual level and
non-generic metadata. The binder scopes and sigma of the parent are unchanged;
this native structural argument introduces no replacement assignment.

Hypotheses: valid session-branded handles and consistent input graph; successful
execution of each named native operation without discarded/rolled-back output;
only actual source-event-qualified parent/copy pairs are intruded; capture and
freshening complete using their existing level boundary. These are operation
preconditions, not an assumption that every necessary replay has been emitted.
Successful draining of work that was actually queued also does not imply that
every stored bound pair has been queued. Sections 3–5 establish structural
retention; section 6 identifies the first unproved activation bridge for the
stronger operational reading of the assigned statement.

Do not infer source protection from empty stored context words. Do not identify
native views with complete contextual ResidualRecipes. The annotation callback's
retracted expected scheme supplies no premise. Complete Call, effect hygiene,
soundness, required principality, general source reachability, arbitrary-context
termination and abnormal-path recovery are outside this derivation. No source
restriction, protected-gamma exception or alternative intrusion rule is added.

Governing authority: contextual residual lineage selection, Selected policy and
Preserved contract; attachment/admission §§3–4, especially extrusion,
capture/freshening and SCC intrusion; top-level inference principles §§1–5 and
§1.1; occurrence qualification, Approved extrusion-event qualification. Reuse
the independently reviewed native-handler-residual-cut §§3–4 under its explicit
successful-processing premises. That result establishes a native primitive,
not source H1/U or full recipe lifecycle closure. Proof economy is governed by
compiler-engineering, Natural compiler behavior and proof-obligation economy.

## 2. Invariant and exact transition equations

Use a proof-only event ancestry label L(v), assigned at initial construction
and inherited by an actual view-copy event. This is induction bookkeeping,
not a proposed compiler carrier or an attempt to reconstruct ancestry from
owner/position/family equality. The copy's input `id` identifies its predecessor
at the transition itself. Distinct initial view IDs receive distinct labels.
The implementation has no separate explicit ancestor-view field.

The structural invariant I consists of these properties:

1. Descendants of distinct initial views never acquire the same live view ID.
   Neither row equality nor equal allowed sets supplies a view substitution.
2. Within one operation/use map R, identical `(old_view, mapped_tail)` requests
   share one result. Distinct keys allocate distinct results. Different uses
   have different maps. Polar extrusion can select different mapped tails for
   the same old view; this intentionally produces different descendants.
3. Every retained cut keeps its exact `A(v)` endpoint. Its nonempty tail has
   capture incidence that continues to find the cut through canonical rows.
   Equality can accumulate duplicate records; distinct v entries survive.
4. Capture/freshening and bound transport retain the selected native bound,
   relation ancestry and available evidence. Replay enumeration sees every
   retained view endpoint separately; it does not deduplicate by `(allowed,
   r(source), r(tail))`. Physical duplicate insertion counts are not a semantic
   multiplicity theorem: capture and relation attachment deliberately intern
   identical recorded obligations. Distinct constructor multiplicity is the
   multiplicity preserved here.

Actual equations, with successful allocation implied:

```text
new_view(payload, tail) = views.len() before append
copy(v, t) = new_view(copy payload of v, t)
R(v,t) = prior R[(v,t)] if present
         otherwise copy(v,t), then retain R[(v,t)]
canonical(A(v)) = A(v)     canonical(S(v)) = S(v)
canonical(M(v,k)) = M(v,k)
canonical(Row(x)) = Row(r(x))
```

The first two equations come from candidate_effect.rs:733–778,871–913;
the canonical equations are lib.rs:11490–11504. No equality comparison of
sources, tails, allowed sets, owner or source position replaces `v` in R.

## 3. Construction and extrusion induction steps

Base case: candidate_signature_view appends a new View after checking the u32
index and reserving capacity. Payload contains owner, position, allowed heads,
tail and annotation/operation provenance. Distinct successful construction
events obtain different indices. candidate_copy_effect_view validates an
existing source-weight/view association when present, copies the allowed heads
and provenance, and invokes that same constructor with the selected tail.
Thus copies preserve native payload and extend the event ancestry without
coalescing labels. This is a native payload fact, not an eligibility theorem.

Extrusion uses one row map keyed by `(endpoint, polarity, target_level)` and one
separate view map keyed by `(old_view, mapped_tail)` for the whole operation
(candidate_extrusion.rs:21–38,76–122,183–213,260–293).
If a row's level is at most the target, the map returns that row unchanged.
Otherwise it allocates the existing polar copy at the target level, retains
the actual parent/copy occurrence and one-sided source link, then maps the
selected bound side. There is no rule keeping gamma artificially young or
non-intrudable. Function ports use opposite polarity for argument Value/Effect
and the original polarity for result Value/Effect.

An open view maps its tail using that polar row map and reconstructs A/S/M
through the one view map. A closed view has no tail and is returned unchanged
by extrusion; it is not merged with another closed view. Distinct original
IDs remain distinct even when their mapped tails are literally equal. Equal
keys reuse one view, including repeated Support/Allowance/member occurrences
with that same mapped tail. A positive and negative traversal may map the
same original tail differently, so the sharing statement is exactly the
map-key statement, not unconditional equality of opposite polar copies.

When a positive effect tail g is copied to g', the incidence owner supplies
every recorded `(source=s, view=v)` in g's bucket. It schedules
`IncomingAllowance(g',v,Key(r(s),+,target),original_bound)` after visiting that
source. The transition at candidate_extrusion.rs:295–309 installs

```text
s' <= A(R(v,Some(g')))
```

and transports original bound origins/evidence with an Extrusion witness.
The common view map handles both ordinary view traversal and this incoming
route. Distinct v entries therefore remain distinct even when s' or g' agree.
Bound initialization similarly retains selected copied bounds and transports
their original evidence (311–330). This establishes I for the returned native
graph; its current activation limitation is isolated in section 6.

## 4. Capture, generalization and fresh-use induction steps

Capture interns canonical row endpoints, but canonicalization leaves A/S/M
IDs unchanged (candidate_scheme.rs:293–330,473–490). Therefore graph node
interning cannot identify distinct views merely because their source or tail
rows agree. A local row is exactly `level > boundary && !non_generic`.
expand_row stops at older/non-generic anchors, retaining their mutable session
bounds rather than taking a stale independent snapshot (595–602).

For a captured local effect gamma, expand_row follows its incidence bucket
and records every `s <= A(v)` before enumerating both physical bound sides
(647–697). A graph exported through gamma can thus recover incoming native
cuts. Capture.bound keys include component, side, endpoint-node identities
and relation; every distinct v has a distinct upper endpoint-node identity
(547–594). Context payload discovery validates weight/view ownership and adds
context-only views/tails to the same capture closure (749–809). Generalization
here means this graph capture with the existing local/non-generic boundary;
no arbitrary new gamma binders or source sigma are manufactured.

For each successful fresh use, prepare_candidate_fresh_use constructs one
`canonical_rows` map. For a captured row x it first reads r(x), and maps that
representative to one fresh row at use_level only if the captured row was
local and its current representative still satisfies the generic boundary.
Otherwise it shares the representative anchor (1009–1051). This deliberately
respects an intervening intrusion that lowered a representative or made it
non-generic. Equal captured row representatives share one mapped row.

The use then creates one view_remap shared by effect operands and context
payloads (1070–1133). A(v), S(v) and M(v,k) all use R(v,mapped_tail), preserving
k. Distinct old views remain distinct; repeated references with the same
mapped tail share. Separate calls allocate separate maps, so reconstructed
view instances are independent even when nongeneric tails are shared. A view
reachable only through an unexpanded anchor remains owned by that shared
session anchor; it is not falsely claimed to have been freshly reconstructed.

Available local weights are validated against the copied view. Context roots
use one `context_remap` for the whole use; rename_contexts_impl recursively
retains operation constructors, child order and shared input identity
(candidate_context.rs:1424–1549). Unsupported capture/rename forms can fail;
this argument is for successful native operations and supplies no missing
all-source progress theorem.

Every captured bound is restored using its retained orientation, mapped
endpoints and evidence. begin_candidate_fresh_bound retains a FreshUse
transport with source_bound and use_origin before physical restoration
(candidate_scheme.rs:1251–1304); freshen_candidate_graph drives every such
restoration (992–1006). Thus this route has an actual replay-driving owner,
not merely retained storage. It does not turn the native view into a complete
contextual residual recipe.

## 5. Qualifying intrusion and replay-consumer induction steps

retain_extrusion_parent reads the actual processing relation's source events;
candidate_value_graph.rs:204–206 qualifies an event by equality of its recorded
origin/receiver Value SCCs. Qualified actual parent/copy entries enter pending;
transformed-output reuse preserves its original group and records the reuse
association (candidate_intrusion.rs:236–365). settle_candidate_intrusion
consumes those pending entries (487–523). Type-row endpoint SCC membership
is not the criterion. Freshening creates no intrusion pair by itself.

The actual function is named `merge_candidate_rows` at this baseline, rather
than the packet's locator `candidate_merge_rows` (candidate_intrusion.rs:525).
For distinct representatives c and p it appends both bound sides of c to p
without dropping source physical storage, transports each original bound's
origins/evidence, splices tail incidence, lowers the representative level to
the minimum and ORs non-generic metadata, then redirects c to p (525–597).
Neither this operation nor canonical_effect rewrites a view ID or its immutable
payload tail. Later tail reads canonicalize its row.

candidate_splice_capture_incidence concatenates the complete bucket lists
(candidate_effect.rs:529–552). Existing source records may contain raw aliases;
the consumers canonicalize them. Their `(source,view)` deduplication key
contains the original view ID, so it cannot erase two distinct v entries.
Source equality need not rewrite all incidence records: canonical source reads
and retained canonical bounds provide their continuation. Gamma equality moves
both lists; it does not merge recipes by equal tails.

candidate_context_canonicalize_bounds transports every changed bound key to
its canonical key with its retained parent context and source association
(candidate_context.rs:3346–3366). In particular, third-owner bounds whose
endpoint row changed are included. Its relation key is `(pair,context,sources)`;
since A(v) remains in pair, distinct views cannot collide there merely through
row equality. Multiple derivations may share a relation node, but their
Transport/Derived dependencies and bound evidence are retained. No general
claim of unique relation identity per history is needed.

After redirection, merge_candidate_rows explicitly enumerates every merged
lower and calls candidate_replay_bound against the merged uppers (598–609).
The nested enumeration at candidate_extrusion.rs:767–810 therefore includes
every retained native Allowance endpoint and gamma upper, including the
cross-side pairs created by the equality. Each pair reaches
candidate_context_begin_replay, whose new/old fiber quadrants retain both
ordered parents and their bound keys (3131–3216). Relation interning can share
the derived child while Dependency::Replay retains each pair of input bounds.

The live replay owner queues or drains children; Queued explicitly means
outer-worklist completion remains necessary (candidate_context.rs:3329–3344).
lib.rs::apply_effect_task reaches candidate_apply_effect. That owner retains
ordinary level-selected bounds and replays the opposite side; the concrete
Allowance consumer forwards an unmatched concrete endpoint to canonical gamma
(candidate_extrusion.rs:843–873; candidate_effect.rs:985–1015). Later source
lowers therefore encounter all retained Allowance uppers; later gamma uppers
encounter its existing lowers. This is actual fan-out for these activated
admission/merge/restoration paths, conditional on their work completing.
Lineage separation neither licenses subtraction nor disables required gamma
parent/copy equality.

By induction, I holds after any finite composition of these successful native
transitions. This is a structural source derivation pending independent review.
It does not prove that every logically necessary replay was activated.

## 6. First unsupported operational transition and falsifiers

The stronger conclusion that every current copied-cut obligation is actually
replayed does not follow from the inspected extrusion transition.
IncomingAllowance calls candidate_insert_bound and
candidate_transfer_bound_origins; neither it nor Work::Bound calls
candidate_replay_bound or creates a bound-restoration replay operation.
candidate_insert_bound_with_evidence ends after physical insertion, incidence
registration, dirty marking and evidence emission (candidate_extrusion.rs:
397–570). finish_candidate_extrusion records the parent group/output association,
not a traversal of copied source/Allowance Cartesian pairs.

The missing lemma is exact: for every current lower of each reconstructed
source s', the existing owning processing route must either activate its
comparison with each copied A(v') or independently establish that comparison's
full consequences, including symbolic tails and retained contextual obligations,
before its result is used/published. Subsequent new lower insertion and
qualifying equality have explicit replay owners; successful extrusion alone
does not provide this current-pair lemma.

This is an unsupported bridge, not a demonstrated missing effect or source
counterexample. Original source/gamma bounds and one-sided copy links can
already imply or later deliver some consequences. A proof cannot dismiss them.
Production invokes candidate_extrude from structural Value dispatch
(lib.rs:12469–12516), then queues the rewritten Value comparison; that fact
does not by itself show replay of every internal copied-source cut. No source
program, native transition probe or publication trace was run in this lane.
The earlier reviewed primitive explicitly leaves copied-bound initialization
and complete worklist processing separate; its conditional acceptance cannot
fill this lemma.

Static falsifiers of I are any view canonicalizer replacing v by a
family/source/tail-equivalence representative; a copy map omitting old v;
separate operand maps splitting equal `(v,mapped_tail)` requests within a use;
capture keys omitting the view endpoint; or an incidence splice dropping one
bucket. The inspected owners do none of these. A discriminating activation
check would retain two distinct source cuts with equal canonical source/tail,
then inspect actual copied-bound lower/upper Replay dependencies and worklist
receipts, including a symbolic-tail current lower and a later lower/upper.
Such a check must authenticate the real extrusion/source route and cannot be
replaced by a model assuming that replay transition. It was not run.

Proof-economy audit: distinct native view retention follows construction and
needs no additional carrier. Current operational activation is A/B when it
controls ordinary accepted inference. Attempting to reconstruct replay from
the mere existence of bound evidence would be D debt: the insertion/replay
owner knows whether it emits an operation. This lane stops at that owner rather
than adding another relation or equivalent conditional proof. This is one
native structural induction, not two failed attempts or a reclassification
closing the parent. Any source-hygiene/full-recipe issue remains H1/U and must
not be hidden in this native result.

## 7. Frozen dependencies, coverage and commit packet

Read-only checks: `git rev-parse HEAD`, `git branch --show-current`, initial
`git status --short`; bounded `rg`/`sed`/`cat` source reads; `sha256sum` of the
direct dependencies below; and `git diff --name-only 146ca9d2a -- <the named
source/design/rule dependencies>`. The named source/design/rule comparison
returned no changed paths. Baseline/branch matched the packet. No builds,
tests, probes, measurements, delegation or Git mutations were run. This
research note is the only write. Unrelated concurrent files were left alone.

Resource use: one proof leaf; lightweight source-reading commands only, with
one batch of four independent read commands. No Cargo/experiment process.
CPU, peak RAM and elapsed proof wall time were not measured; no invented
measurements are reported. Assigned wall-time cap: twenty minutes.
Runtime requested by the ordinary proof policy: Sol/high. Effective model and
effort are unknown because no runtime metadata is exposed to this worker.
The inspected prover role is registered and has no model/effort pins; that
does not prove inheritance, hot reload or an override. No Astra escalation.

SHA-256 dependencies (relative paths unless absolute):

```text
f414efa7efdb17644f4dfa6b0bba621c1bb7cccd0f83735c33a0acb875da6b91 crates/yu-solver/src/candidate_effect.rs
ed3e213e943a553943784e409194723f64acb810a0bcf06607ee95b0eb4e4ed1 crates/yu-solver/src/candidate_extrusion.rs
c8ef7cc472f0dcb60d793c6f9b4f6ba1aefb76f919ff2a3ce9310f85eb647dcd crates/yu-solver/src/candidate_scheme.rs
4a2b87ebf6e5e219c06763bc4e589517fd48c575c89038f2a11fc1e6494fe90e crates/yu-solver/src/candidate_intrusion.rs
6301ca80eec137df3f2c2c44e2edaa7dbdf1ed7a78c69617228888e63654e461 crates/yu-solver/src/candidate_context.rs
64b94da599dc10aef6fd06003fc6c1ab909bdce2a07c722fdb11eb1c8b690ec4 crates/yu-solver/src/candidate_value_graph.rs
e902da1c9a7f0fb4dcd806c87563d1ae46d35bbb999e69b7fee51c3c0f6e4bf5 crates/yu-solver/src/lib.rs
d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98 notes/design/2026-10-10-contextual-residual-lineage-selection.md
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc notes/design/2026-10-10-contextual-attachment-admission-design.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81 notes/design/2026-10-11-yulang-inference-top-level-principles.md
531a9efae0ab7e03bfbd2f41cd7da86078e2fc8e67675d2c5c941972409f4e89 notes/design/2026-10-12-intrusion-value-type-association.md
469677cc50b1dfd5327fa330e85bb83124c9e17cec391866dbf71ee23c40d50b notes/theory/2026-10-14-native-handler-residual-cut.md
8b418f8ed02606205ecdfedcf5da72dae074e1c799237b8cc034fdfbd71ab7a1 rules/agent-orchestration.md
3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69 rules/research-lab.md
e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1 rules/design-authority.md
4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9 rules/compiler-engineering.md
2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6 rules/git-concurrency.md
a0a114b589e8920af8e8fd871d15f63d68b735fc1a553f5a89952b1eab8489e5 rules/orchestration-budget.md
993d4c2a7743669b4c7a6c46f054c4caae492873f0a5f20a1ea566ebf9dea3c1 .codex/config.toml
485a26c7409e16c692ad10095031ab0e7084726ec5da5666082b3bbc4a5daf98 .codex/agents/prover.toml
db55dfb7568805ac6b6372fe8bc05cc00731ae5b5ed33c6af72007a7ce885810 /home/momota1029/.codex/skills/yulang-proofs/SKILL.md
```

One next action: primary assign the exact extrusion current-pair activation
lemma at Work::IncomingAllowance/Work::Bound and their structural Value
consumer, with complementary source-qualified falsification if needed. Do not
repeat the already construction-directed view-ID separation proof or enable
handler residual integration from this result.

Commit packet: exact leased path
`notes/theory/2026-10-15-native-residual-view-lineage-lifecycle.md`; baseline
`146ca9d2a8713398c893a9cae026ae0c2fae593d`; changed direct dependencies: none
in the checked baseline comparison. Review: unreviewed research-only structural
derivation plus activation obstruction; H1/H2/U OPEN, H3/P disabled,
production/F5 separate. Checks already run: static owner/consumer trace,
baseline/branch reads and dependency hashes; no executable verification.
Proposed one-line checkpoint message:
`research: derive native view lineage retention and isolate extrusion activation`.
Shared-record deltas left for primary/curator: native view IDs, per-use sharing,
capture incidence and qualifying-equality retention have the structural source
derivation above; complete copied-cut activation remains at the named extrusion
owner. No task, index, theory-status or question-board file was edited.
Writes stop at handoff; fresh independent review remains primary-owned.
