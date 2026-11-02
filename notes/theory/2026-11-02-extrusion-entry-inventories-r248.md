# R248: successful extrusion entry inventories and current return

Revision 1. **Candidate static source-native derivation; independent review pending.**
Author `/root/sol_r248_entry_inventories`; no coauthors or descendants.
Contract `tasks/agent-loop/sprints/extrusion-entry-inventories-r248.md`, SHA-256
`031438e3758719358f9b17fd383a0256431b629cd939fc507e92f94d645189ee`.
Baseline `87c54f43e645441ec21939ccf1dcfd980f9d5521`, observed by reading
`.git/HEAD` and its named `refs/heads/yulang3` file, without a Git command.

## 1. Parent, exact result and distinctions

The unchanged parent is Yulang inference soundness and its Rust implementation;
the immediate edge is `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1` /
`R70-ENTRY-WF-1`. The accepted source domain, original Simple-sub A/B, arbitrary
independent satisfying assignment, shared witnesses and F1/FK1 are preserved.
The frozen inputs locate this parent through R245 and R247; they contain no
fully quantified concrete full-inference Lean declaration. None is invented
here. Lean declaration, theorem type and axiom dependencies: NOT APPLICABLE;
checker NOT RUN under the no-Lean/no-build lease.

This packet derives storage correspondence, not the source typing judgment,
evidence completeness, semantic equivalence of solutions, or authority to
promote production. The following are informal source result types:

```text
D-INV248:
For each accepted non-test production prefix reaching call+ (lib.rs:14822)
or call- (lib.rs:14835), references actually used at that call and its visited
children satisfy the DERIVED view/member/incidence and context/relation/
source-set/evidence-index/exact-key-fiber/replay-head clauses in §§2–6.
The expressly CONDITIONAL later-owner clauses are not included in D-INV248.
The row/term projections are the reviewed R247 D-RT, with its actual domain.

C-RETURN248:
For either actual call, substitute D-RT and D-INV248 for their corresponding
storage premises in R245 §§4–5. Conditional on its residual WCurrent premises
and the current operation's checked helpers succeeding,
its map/snapshot/continuation, reconstructed-port, Parent, exact observed-fiber,
retention and queue-transfer postconditions follow as described in §7.
Explicit evidence gaps remain gaps. No every-slot coverage or later drain
completion is a conclusion.
```

**Parent edge REDUCED**: the named successful-history inventory assumptions
classified DERIVED below are replaced by producer arguments at their original
entry/return edges. The full inference parent and full WCurrent remain OPEN;
no full semantic parent conjunct closes. C-RETURN248 retains the residual
premises described in §8, successful-helper premises and the reviewed R245
current simulation. It is not a kernel-checked theorem or an independently
accepted R248 result.

Use one session's actual `candidate_graph.intrusion.effect_algebra` and its
embedded `context` as the inventory owner, not a numeric-ID namespace shared
between sessions. `start_candidate_graph` (`candidate_scheme.rs:2528–2552`)
constructs a default GraphState and initializes its algebra before publication;
the vectors/maps concerned start empty. A source graph is captured and reused
within this same session, as in R247 §4, rather than deserialized from a foreign
session. Independent FreshUses keep their own maps and use origins.

R246-EXIT excludes a failed production route followed by further inference in
that same session. It does not prove the following successful-history induction.
The induction includes successful histories with type diagnostics. It does not
claim persistence after arbitrary rollback or certify post-error readbacks.
Error-only local context renaming rolls back and returns Err
(`candidate_context.rs:1671–1787`); its successful branch retains the appended
objects. No successful-prefix extension below deletes a view, payload, relation,
context, bound-list record or evidence record. Operation retirement is treated
separately in §6, because operation maps can legitimately remove completed owners.

## 2. View-to-payload correspondence is a construction equation

`candidate_signature_view` (`candidate_effect.rs:1219–1278`) takes the checked
old `views.len()` as v, reserves the view slot, and obtains a payload w from
`context.source_weight(v, owner, position, allowed, attachment_source)` exactly
when the operation origin is absent and either the tail is absent or an
attachment source is present. `source_weight`
(`candidate_context.rs:2888–2911`) appends at old `weights.len()` and copies
exactly v, owner, position and the ordered allowed vector. It also constructs
attachment member ordinals as `0..allowed.len()`. The subsequent View push
uses the original same arguments. Neither operation calls extrusion while
the boundary is reserved but the View has not yet been pushed.

Consequently every successfully published source-weighted view satisfies:

```text
views[v].source_weight = Some(w)
weights[w].boundary = v
weights[w].owner = views[v].owner
weights[w].position = views[v].position
weights[w].allowed = views[v].allowed
views[v].closed_weight = if views[v].tail is None then Some(w) else None.
```

For an operation-origin view, both weights are None. An annotation view with
a symbolic tail and no attachment also has both None. Thus neither every view
has a payload nor every source weight is an executable closed filter. Operation
provenance retains the actual supplied declaration Arc and occurrence; copying
that field does not authenticate a source typing/effect claim about it.

All production births are this constructor: signature Effect ports
(`candidate_effect.rs:2675–2824`), operation-v1 Q (`:1395`), and copy
(`:1523–1546`). `candidate_effect_view` is cfg(test) and supplies no additional
production case. Signature local caches insert only returned view IDs; a hit
reuses that actual earlier view. R247 supplies the optional Effect-tail row
membership at these births.

`candidate_copy_effect_view` checks its old view by `get`, validates its old
source payload when present, and rejects a closed weight without a source
weight. It clones owner, position, ordered allowed vector, operation provenance
and attachment source, then calls the same constructor with the new tail.
The copied weight therefore belongs to the copied boundary, not to the old
boundary. `validate_payload_view` (`candidate_context.rs:1834–1842`) checks the
displayed field equalities, including the closed/tail equation; its success
is stronger than successful indexing. Its correctness here also follows from
the construction equations, rather than being assumed from a numeric w.

The operation-local remap (`candidate_effect.rs:1549–1567`) starts empty in
extrusion and FreshUse, and inserts only the result of this copy at key
`(original_view, mapped_tail)`. A hit therefore retrieves that same copy. This
is sharing inside one use/call, not equality of unrelated FreshUse identities.
No production write mutates an existing View or LocalWeight payload on this
successful branch; later append cannot change the equations.

**Classification DERIVED**: view range, exact payload/boundary/owner/position/
allowed correspondence, closed-weight condition and copy/remap correspondence.
**OPEN semantic boundary**: those copied source fields alone do not prove that
the source annotation/operation authorizes a particular occurrence or establishes
the parent's effect judgment. No such premise is used as an inventory witness.

## 3. AnnotationMember belongs to its particular view

The actual production creation and preservation cases are:

| Producer | Derivation of `member < views[v].allowed.len()` |
| --- | --- |
| Support decomposition, `candidate_check_effect_operand` (`candidate_effect.rs:1602–1635`) | Iterates `0..view.allowed.len()`, checked-converts that index to u32, and emits `(that v, that member)` |
| FieldBoundV1 (`candidate_effect.rs:1464–1473`) | Selects an enumerated operation view whose allowed vector equals the singleton field family; emits member 0 |
| Receiver path/provider enumeration (`candidate_receiver.rs:89–112`, `2750–2770`, `5648–5656`) | Enumerates the selected actual view's allowed vector; checked-converts its index; readback selection at `1885–1898` separately compares the retained view/member/family |
| Capture (`candidate_scheme.rs:2214–2217`) | Saves an existing AnnotationMember endpoint and the same view's tail; it does not generate a member from a different ordinal |
| FreshUse (`candidate_scheme.rs:4660–4683`) and extrusion (`candidate_extrusion.rs:354–369`) | Copy the view through §2 and preserve the member. Equal ordered allowed vectors preserve its range and selected family |
| Bounds, canonicalization, tasks, replay | Preserve the endpoint value; canonicalization changes rows, not view/member indexes |

The receiver observation conversions in `shadow_apply.rs:1137`, `:1324`,
`:2964` do not add a live unchecked member producer: they expose existing
endpoints or bounded observation selections. Readback conversion is not treated
as a new inference constructor. All newly selected live member endpoints use
the actual owning view above. Contributions similarly originate from an append
at old `contributions.len()` (`candidate_effect.rs:1584–1601`); FreshUse copies
the actual effect/origin into a new contribution before storing its new ID.

**Classification DERIVED**: range and the exact equation
`effect(member(v,m)) = views[v].allowed[m]`, retained by copies. This permits
repeated/equal allowed atoms and empty allowed vectors; it asserts neither
member uniqueness nor a member-to-origin/fiber association. **OPEN**: semantic
provider/occurrence licensing and common-witness claims beyond these field
equations; receiver checks do not close the general parent theorem.

## 4. Capture incidence is a finite partition, not an increasing-index list

Induct on mutations of `capture_records` and `capture_incidence` in successful
history (`candidate_effect.rs:959–1042`; merge caller
`candidate_intrusion.rs:599–680`). Invariant: each bucket is a finite simple
chain of actual records, its stored tail is the last record with next None,
and chains of distinct keys have disjoint record-index sets.

Base: both containers are empty. A duplicate `(source,view)` registration is
a no-op. Otherwise registration takes fresh index n = records.len(), links
the old bucket's tail to n if present, pushes `(source,view,None)`, and sets
the new bucket tail to n. Fresh n belonged to no old chain, so this preserves
disjointness, simplicity and exact endpoints. The old tail was terminal by
the induction hypothesis; this is not an assumption inferred from indexing.

Splice first rejects `from == to`. If source is absent it is a no-op. Otherwise
source and destination chains, when both present, were disjoint because their
keys differ. Linking destination.tail to source.head concatenates these two
finite simple chains; removing `from` and placing the concatenation at `to`
leaves one owner. With no destination it simply moves the chain. The resulting
tail is source.tail. A splice edge can point to a numerically smaller index;
an increasing-index proof would be wrong. Disjointness is the reason no cycle
is introduced. No other production successful mutation aliases bucket heads.

`candidate_register_capture_bound` creates the tuple only from an actual
negative EffectRow-to-Allowance bound, reads that actual view's tail, and uses
its canonical Effect representative as bucket key. §2 gives the view; R247
gives source/tail allocation and representative validity. A same-kind merge
copies bounds and then splices between its distinct Effect roots before
linking the forest (`candidate_intrusion.rs:635–680`). Even if copied-bound
registration adds a record before splice, fresh append preserves the partition
first; splice then applies to the resulting disjoint chains. Record source
fields remain their actual allocated raw rows; later canonicalization does
not turn them into view IDs or alter which View they name.

**Classification DERIVED**: finite/disjoint/simple chains, valid record
indexes, exact head/tail linkage, allocated source rows and valid record views
at actual reads. This does not claim that the dedup key equals a semantic
relation identity after every merge, that each raw bound slot has a fiber,
or that incidence itself is an ordinary solver/SCC edge.

## 5. Context, relation, source and evidence inventories

The following is an induction over the actual producer families, not a blanket
claim that their unchecked indexing validates inputs.

**Contexts and weights — DERIVED.** `context` (`candidate_context.rs:2784–2810`)
accepts only identity or existing child ContextIds; a newly appended context
therefore has strictly older children. An interner hit retains exactly the
old equal constructor. Production source prefixes use §2's closed weight
(`:3780–3791`); Function/Tuple/Record/Variant ports reuse inherited valid
contexts and this actual prefix (`:3930–4078`); replay combines actual parents
(`:4456–4467`). Discharge stores a traversed residual from that same finite
context DAG (`:4090–4305`). It never manufactures a new context index. The
rename path checks source nodes against its entry checkpoint, older children,
both old/mapped weights, and exact caller-seeded constructors before accepting
a result (`:1671–1787`). `BothFromRight` is rejected by live capture payload
discovery (`:1818`), rather than silently interpreted as another operation.
No claim that the relation/dependency graph itself is acyclic follows.

**Relations and source sets — DERIVED inventory projection.** Source seed,
ordinary admission, current Value rewrite, structured ports, bound emission,
task/equality transport, FreshUse and replay all obtain new relations from
`relation_with_scoped` (`candidate_context.rs:3481–3513`). Their context is one
of the preceding constructors or an existing parent's post-check context.
An interner hit has the same full key; a miss appends at old relations.len(),
and `previous_on_pair` is that pair's old head. Thus the pair chain is finite,
decreasing and retains the actual pair. `processing` is copied from a real
seed/queued relation and restored from its actual typed frame
(`lib.rs:14302–14361`, `14394–14465`); transport checks its pair against the
current task (`candidate_context.rs:4186–4217`). No relation is selected from
an origin-table count.

`candidate_context_seed` gets the optional source event from the frozen
checking map. The newly admitted owner `candidate_value_graph.rs:335–344`
stores precisely old events.len() at that checking occurrence and appends the
actual Association. R247's accepted occurrence construction supplies its source
identity premise. `intern_sources` (`candidate_context.rs:3514–3525`) copies,
sorts and deduplicates these valid events; inheritance copies an existing set
ID; `union_sources` copies actual parent sets. Hence set IDs and their element
event indexes belong to the same batch's inventories. This is not a proof of
the semantic adequacy of source reachability or intrusion qualification.

**Scoped IDs — DERIVED stored-index projection; semantic interpretation OPEN.**
`relation_with_scoped` stores either identity flow 0 or an interned appended
flow; transformer 0 is identity. Nonzero transformers come from `intern_scope`
(`candidate_context.rs:2949–2983`), exact old-flow reuse, checked composition,
or FreshUse remap followed by that interner (`candidate_scheme.rs:4859–4883`).
The identity short-cuts in compose are justified by the old IDs, not by their
numeric nonzero value. Initial scope/input IDs are produced by Plan's region/
computation-scope births and Apply's old call-vector length
(`candidate_source.rs:141–171`, `1868–1922`); ScopeInventory copies those
inventories and freshens at its old typed lengths (`:223–244`, `299–358`).
`candidate_scope.rs:98–174`, `214–266` constructs finite payloads and rejects
remap collisions. A missing local remap uses the existing old inventory member,
not a newly authorized foreign identity. Demand terms follow R247's checked
capture/reconstruction and `transported_scoped` (`candidate_context.rs:3286–3297`).
None of these storage equations proves effect hygiene, authentic source
application of every scoped operation, or F1/FK1.

**Exact-key bound fibers and replay suffixes — DERIVED.** `attach`
(`candidate_context.rs:3702–3715`) either observes an existing equal relation
on that exact key or appends `(key,relation,old_head)`. The relation came from
one of the valid constructors above. Consequently every chain is finite,
decreasing, and belongs to that exact BoundKey. Successful canonicalization
(`:4649–4670`) adds transported fibers to canonical keys while preserving raw
lists; it does not clear or relink them. The mid-list removers at `:2097–2127`
are cfg(test). Rollback rewrites are excluded from this continued successful
branch by R246. Thus an old recorded head for the same key remains a suffix
of its current chain. `replay_progress` records precisely the observed heads
(`:3695–3701`), so begin_replay's old/current frontier premise follows by
induction. None is a claim that every physical raw slot has such a chain.

**Evidence IDs and heads — DERIVED storage; coverage OPEN.** Admission obtains
its actual relation from bound emission or the supplied successful FreshUse/
transport; `None` is allowed and carries gaps. `BoundEvidence::admit/emit`
(`candidate_context.rs:867–940`) append to actual groups keyed by the exact
`(bound,optional relation)` and keep the old same-group heads. A supplied
antecedent is checked in the snapshot inventory before admission. Emission
uses the just-returned admission, then stores the physical readback checked
against the exact bound (`candidate_extrusion.rs:852–873`). `snapshot` samples
those actual heads (`candidate_context.rs:845–866`). Capture saves that value
and its own new CapturedEvidenceRef (`candidate_scheme.rs:2352–2398`); FreshUse
imports that exact retained value in the same State and records the returned
snapshot IDs in matching order (`:4918–4948`). No surviving head can be truncated
in this successful history. Transform/recipe/reverse-head insertion
(`candidate_context.rs:953–990`) similarly appends actual returned IDs; reverse
links point to preceding entries for that antecedent.

Evidence completeness remains OPEN at the exact owners: OwnerEmission and
ExtrusionLink add MissingAntecedent/ProcessingAntecedentsUnavailable/
OrdinarySeedAuthenticationUnavailable (`candidate_context.rs:871–879`),
FreshUse adds ReplayUseAntecedentsNotRetained (`:891`), recipes retain that
gap (`:985`), and the origin-only transport fallback explicitly uses relation
None and MissingOriginAssociation (`candidate_effect.rs:1072–1090`). A valid
snapshot/head or equal payload does not remove any of these flags or certify
an ordinary seed, common witness or association. This is a precise open
producer premise, not a malformed-inventory counterexample.

## 6. Replay/restoration owners and queue references

**DERIVED creation and local ownership equations.** `candidate_context_begin_replay`
(`candidate_context.rs:4411–4499`) snapshots actual heads. §5 makes both
new-lower × all-upper and old-lower × new-upper walks finite and owner-correct.
Each pair reads actual relation contexts/source sets/scoped flows, obtains a
child from the same relation constructor, and retains the exact ordered
Dependency::Replay parents and input keys. Interning equal children does not
identify their distinct dependencies. A duplicate exact dependency may suppress
a child. Recipe coverage remains as above.

Operation IDs use one checked monotone counter shared with restorations;
creation advances it and never reuses an old ID in this successful branch.
The new operation owns its actual task, inputs, heads, prior heads, child vector,
queued=consumed=0 and Idle wait state. Bound restoration reserves before
physical insertion, stores the returned actual emission and saved opposite
count (`candidate_extrusion.rs:966–993`), then pairs its actual retained replay
bidirectionally (`candidate_context.rs:2466–2502`). Saved-count/live-index
selection reads physical append-only storage; canonicalization changes the
chosen endpoints without replacing the restoration identity.

For a fresh operation driven with provenance None, queue_next emits the stored
child relation with `(operation,index=queued)`. `enqueue_item`
(`lib.rs:15328–15355`) creates evidence/reserves storage before transfer, then
performs only infallible queue insertion after it; `transfer_replay_child`
(`candidate_context.rs:2536–2547`) checks that operation and cursor. It does
not manufacture relation IDs or acknowledge children. Within this operation's
local queue drive, `0 <= consumed <= queued <= children.len()` and every
transferred item has its exact retained owner. Old unrelated outer-queue work
remains unrelated. The final extrusion drive does not execute it.

Completed operation maps can be removed: retirement is guarded by retired,
Idle wait and absence of an active restoration owner
(`candidate_context.rs:2342–2400`). A newly queued nonempty operation has
consumed=0<n, so it is not retired by this local drive; the empty case has no
outstanding child reference. These facts justify R245's return handoff. They
do not prove all future acknowledgment/retirement behavior or eventual
completion of independent queued/foreign continuations. **CONDITIONAL on the
separate later drain invariant**: preservation through arbitrary later terminal
acknowledgment/settlement; **OPEN** `R70-DRAIN-1`, rather than a consequence of
the local checks here.

## 7. Application at both real calls and every visited child

At call+ (`lib.rs:14822`), R247 gives a visible Positive nonrow Value root and
allocated receiving upper Value row r. Therefore its actual target
`value_levels[r]` exists. At call- (`:14835`), it gives the Negative nonrow
upper root and allocated lower row r, with that row's actual target level.
In both cases §§2–6 concern the exact same embedded algebra/context inventories
from which that typed dispatch was formed. There is no separate foreign
view namespace or assumed direct Effect-root caller. Processing is retained
from that actual typed item through Transport/Context/Dispatch, not inferred
from a label or numeric endpoint equality.

Apply the row/term and new inventory facts together:

| Actual work edge | Applied fact and current-return consequence |
| --- | --- |
| Root and Value/Effect Row Visit (`candidate_extrusion.rs:94–195`) | R247 supplies row/level/forest and selected endpoint validity. Existing exact-key fibers are finite (§5), not assumed to cover every physical slot. Memoization retains the full endpoint/sign/target key before following bounds |
| Positive deep Effect-row incidence walk (`:180–193`) | §4 supplies finite disjoint chain, valid record/view and allocated source; R247 supplies canonical source. Each IncomingAllowance owns precisely that observed original source BoundKey |
| Allowance/Support/AnnotationMember Visit (`:195–223`) | §§2–3 justify view and member reads; R247 justifies optional tail. Child Visit uses the actual tail's typed representative and the current sign |
| EffectView continuation (`:334–370`) | Completed child is an Effect row. §2 yields actual copied view/weight with that tail; §3 preserves member range/family. The local `(view,tail)` map keeps copy ownership |
| IncomingAllowance (`:371–398`) | §2 copies its actual incidence view. §5 permits walking the original source's observed fibers and transporting each actual relation. The origin fallback retains its gap. Installed bound enters I only after transport succeeds |
| Function/Tuple/Record/Variant discovery and completion (`:224–333`, `:422–574`) | R247 supplies actual ordered signed children and stable structural nodes; the same §§2–6 invariants apply to every Effect or bound child they reach. Current four-port variance, nonempty Tuple, empty Record, nonempty Variant family and zero-payload alternatives remain represented |
| Bound continuation (`:399–421`) | Actual completed image, original physical BoundKey and copied destination stay distinct. §5 supplies finite owner-correct observed source fibers and new evidence IDs; no canonical-child identity substitutes for the physical source key |
| Final Parents/replay/return (`:575–593`) | R245's current retention argument applies with finite incidence and valid heads/suffixes now derived. §6 supplies exact new-operation queue ownership. Local scratch/maps drop after replay and sample success; retained Parents/views/evidence/operations/queued items remain |

Fresh append/copy during these visits preserves the same equations. In
particular copied/incoming view tails are target-or-lower row images: the
incidence constructor cannot append a new high-tail record into the currently
expanded high bucket. Thus the finite entry chains used in R245's discovery
argument are not replaced by a self-extending high-tail iteration. No intrusion
settlement or typed child drain runs inside the final provenance-None drive.

This is the promised consumption of justified WCurrent clauses in R245's
current return simulation, not an assertion that all WCurrent is now derived.
Besides §8's residual premises, its successful-helper assumption is explicit:
allocation, checked constructors, scoped rejection checks, transport, queue
reservation and resource sampling must succeed. Under those assumptions,
each visited deep key has its same-kind level-target image/Parent and actual
source link, each changed structure has its completed actual port images, and
each selected observed fiber is transported with its own dependency. A fresh
nonempty final replay has queued=n and consumed=0; this is transfer, not
acknowledgment. No immutable-entry-snapshot substitution is used.

## 8. Complete classification of the entry/return groups and remainder

| R245 WCurrent group / related obligation | Status after application |
| --- | --- |
| Rows, levels, metadata, representatives, receiving target levels | DERIVED by reviewed R247 D-RT at both calls and every visited child |
| Visible finite signed terms, current Function/Tuple/Record/Variant ports | DERIVED by R247 and applied above; all current constructors retained |
| Bound owner/lane/readback and endpoint row/term membership | DERIVED R247 plus actual emitter; no readback-as-item-validation shortcut |
| View IDs, payload/weight/boundary/owner/position/allowed equations | DERIVED §§2–3, including copy/remap and successful retention |
| AnnotationMember range and owning allowed entry; Contribution index | DERIVED §3; source semantic provider/occurrence licensing OPEN beyond storage |
| Capture incidence indexes/head/tail, disjointness, finite traversal, source/tail rows | DERIVED §4 with R247 row projection |
| Context IDs/older children/weights, relation/source-set/scoped stored IDs | DERIVED §5 storage equations; semantic scope/qualification interpretation OPEN |
| Exact-key fiber heads/next/relation indexes and recorded replay-head suffix | DERIVED §5. It neither assumes nor supplies R71 completeness |
| Evidence group/snapshot/admission/emission/transform/recipe indexes and heads | DERIVED §5 storage. Seed/antecedent/origin/replay-use completeness remains OPEN at named flag producers |
| New restoration/replay IDs, actual children/dependencies, local queue transfer | DERIVED §6. General later drain/ack/settlement preservation CONDITIONAL on its separate predecessor invariant |
| Current storage entry-to-return result | CONDITIONAL on residual WCurrent, successful checked helpers and reviewed R245 current simulation; only the DERIVED portions above are substituted |
| Every raw physical slot has needed canonical fiber (R71) | OPEN; owner Luna / actual emitter, canonicalization and replay enumeration |
| Later queue execution, terminal acknowledgment, intrusion settlement, foreign continuation | OPEN, independent R70-DRAIN-1/F1/FK1 obligations; no local-frame discharge |
| Full inference soundness, source/evaluator correspondence, hygiene, generalization | OPEN; no ordinary inference semantics or source restriction changed |

The exact residual retained-owner premise is `R248-PRIOR-OWNER-1`: for an
already pending replay/restoration/typed-frame handle created before this
call, preservation through earlier successful terminal actions must establish
that the saved handle/ack still refers to its live same operation, child index
and cursor frontier whenever later consumed. Owning mutation/consumer symbols
are `complete_replay_child`, `retain_replay_return`, `retire_replay_candidate`,
`commit_replay_operations` and `prepare_replay_child_completion`
(`candidate_context.rs:2342–2400`, `2557–2607`). §6 proves the new local
operation's creation/transfer and exclusion of its premature retirement during
this drive; it does not prove this all-prior-terminal-history invariant. It
remains CONDITIONAL on the independent R70-DRAIN-1 predecessor, not on a new
assumed ID-validation interface. The extrusion's final drive leaves the old
outer queue intact and does not discharge that predecessor. If WCurrent is
read as requiring authentic semantic evidence as well as inventory safety,
§5's explicit coverage gaps also remain OPEN; no complete-WCurrent label is
claimed under either reading.

There is no claimed accepted-source malformed-inventory counterexample. The
contract's falsifier remains a successful non-test prefix reaching one of these
actual calls/children with a wrong view/member/owner/head or cyclic/overlapping
incidence chain. Hand-built invalid IDs or test-only mutation/retained retry
are insufficient. Implementation disposition **NO_SAFE_CODE_SLICE**: the actual
emitter, copy, splice, capture, transport and replay owners were inspected, but
no reachable defect justifies a production change.

Mutual TODO `R248-EVIDENCE-AUTH-1`, owner Luna: retain the original parent and
separate inventory safety from the explicit evidence-coverage premises at
§5's OwnerEmission/ExtrusionLink/FreshUse/recipe/origin-fallback expressions.
Required evidence is the authentic source-to-admission/antecedent association
for the original parent, or a source-qualified counterexample; a green index
check, copied payload, origin-count equality or a renamed conditional theorem
does not satisfy it. This requests no code authority or new output lease.
R71 and R70-DRAIN-1 keep independent TODOs/owners; no cross-lane request
authorizes writing their paths. Next in-scope step is fresh independent review
of these frozen bytes and Luna's adjudicated parent-edge intake.

## 9. Reuse, pins, checks and writer stop

Reused with actual premises: R245 native/current-constructor equations and
current return simulation (author `/root/sol_r245_entry_return`), R246-EXIT
only for absent failed-route continuation (author `/root/sol_r246_error_lifetime`),
and R247 successful row/term/capture facts (author
`/root/sol_r247_successful_history`). The formal-permission r3 handoff is a
pinned predecessor locator, not an extra theorem or independent R248 review.
Historical R70 Function-only review is not extended to current forms by name.
Rejected: indexing as ownership, incidence increasing-index proof after splice,
source metadata as executable witness, relation interning as dependency identity,
raw/canonical lineage collapse, independent-use identity collapse, and queue
transfer as acknowledgment.

The initial contract hash was
`cf0912eef1b4dab067f856dc819139d6f533a058119ce1de87b631c966398db7`.
All initial 20 pins and baseline matched before citation. Luna then admitted
the exact candidate_value_graph/candidate_scope owner pins recorded below;
both and the revised contract were rehashed MATCH before body reads/citation.
No lease, source-domain, semantic or resource expansion was taken. All final
manifest paths/hashes are appended below; output hash is in the handoff, whose
hash is returned externally to avoid recursive self-hashing.

Checks: static reads/symbol searches, SHA-256 comparisons and read-only ref
observation only. One attempted read of the contract's scope-name ref failed
because the actual checked-out ref is yulang3; the actual HEAD/ref was then
read and matched. Some combined reads were truncated; the relied-on producer/
consumer passages were reread in bounded chunks. No build, test, probe, Lean,
Cargo, benchmark, production edit, runtime/quarantined path, Git command,
external contact, descendant, scratch/cache/generated output or model switch.

Requested `gpt-6.1-sol/high`; observed model/effort UNKNOWN. Actual worker
`/root/sol_r248_entry_inventories`, session
`01a1873a-a93b-7dc3-a8ce-028a7b543a80`. Parent assignment and active-work/hash
messages are the launch/work receipts. Budget <=2400 active seconds; exact
active time/CPU/RSS UNKNOWN, full reservation retained without refund or renewal.
Clock observations and final hashes are recorded in the handoff.

Only this note and `tasks/agent-loop/inbox/extrusion-entry-inventories-r248.md`
were written. Scratch NONE; descendants NONE; unresolved descendant leases NONE.
After final hashing revision 1 is **FROZEN / STOPPED / WRITES_STOPPED**. Fresh
independent review, adjudication, shared status, Git and integration belong
to Luna. The worker does not continue while waiting.

## Frozen dependency appendix

```text
429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be  crates/yu-solver/src/lib.rs
6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e  crates/yu-solver/src/candidate_scheme.rs
bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49  crates/yu-solver/src/candidate_source.rs
80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61  crates/yu-solver/src/candidate_extrusion.rs
d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1  crates/yu-solver/src/term.rs
a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905  crates/yu-solver/src/candidate_context.rs
475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97  crates/yu-solver/src/candidate_intrusion.rs
4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15  crates/yu-solver/src/candidate_effect.rs
5ca308e7b890e57a8458a151554ece55585d762565204d39c520c4b534e44ade  crates/yu-solver/src/candidate_receiver.rs
99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5  crates/yu-solver/src/shadow_apply.rs
aaaa88a374083f898188cd390b8cf0244855d8c09c8939b9e68ee2831bc692cf  crates/yu-solver/src/candidate_value_graph.rs
4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03  crates/yu-solver/src/candidate_scope.rs
6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646  crates/yu-hir/src/module.rs
7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1  crates/yu-hir/src/module/local_source.rs
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
104720837d86a40efafe1676bf23d756042ce78355d0bfc84c69918aa7676956  tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r3.md
7ef7ca1bb40fbe18370691b064edc3b24d9818076dbb63738fdb3d6b6f72101e  notes/theory/2026-11-02-ordinary-extrusion-native-entry-and-return-r245.md
647860bfec8b9b7b7b1809ace66c24181e1c9ad8c7b3f7616c7100acdb439322  tasks/agent-loop/inbox/ordinary-extrusion-native-entry-and-return-r245.md
6ec2b144b1976eed7f3fe6e8a2a2ea65f9e23c1836980d288ae695f55a0a408a  notes/theory/2026-11-02-production-error-lifetime-r246.md
77c8f198805891c9dfd2b8c33f8b03fdda99169aef294138ff6684439734160b  tasks/agent-loop/inbox/production-error-lifetime-r246.md
e10c1fbc1e378a816f6cee44ca4fb7679a6056b055637f264bcbc9c7fe8d64ba  notes/theory/2026-11-02-successful-row-term-closure-r247.md
dc0cf07ca3916c726cc1652c7a102071294e1ef6926c685a12039ab06142e3d9  tasks/agent-loop/inbox/successful-row-term-closure-r247.md
```
