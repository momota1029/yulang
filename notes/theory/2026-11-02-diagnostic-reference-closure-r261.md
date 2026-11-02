# R261: executable replay emission and diagnostic child references

Revision 1. **Candidate source-constructor proof; independent review pending.**
Author `/root/sol_r261_diagnostic_reference_closure`; no coauthors or descendants.
This is a source derivation, not a Lean theorem or production authorization.

Contract `tasks/agent-loop/sprints/diagnostic-reference-closure-r261.md`, SHA-256
`dd0858cc37c7512a9cfcc8ef17b7c045fd6464afd631a0e1769662c4a052a8a7`.
Fixed baseline `d7e886e6d1dd9a3a3318908a8425937b3ca7703d`; Luna's assignment
records administrative-only movement to
`c1c3e721664b43be640176ba45f3f1b23cea9ae7`. No Git command was run here.

## 1. Parent, domain and result type

The unchanged parent is Yulang inference soundness and its Rust implementation,
with the original accepted source domain, Simple-sub A/B, independent arbitrary
satisfying assignments, shared witnesses, F1/FK1 and foreign continuations.
Immediate application: `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1` / `R70-DRAIN-1`,
specifically the diagnostic-reference premise of reviewed R250 SUFFIX250 at an
actually reached Diagnostics cut. Reviewed R260 supplies ORDER260 there.

Use the inherited R249/R250/R260 initialized, non-test, successful-forward
session domain, including successful prefixes producing type diagnostics.
Failed-route continuation, arbitrary externally installed graphs and test-only
retained-resume transitions are not source evidence. No eventual entry into
Diagnostics is assumed. Success of fallible helpers remains a separate premise,
not a proof of an origin/fiber association or all-source successful inference.

The source result has this informal type:

```text
REF261:
For every finite history H in that domain and every actually reached
Diagnostics entry of a typed frame F:

  (a) every retained DiagnosticEdge.child K names an actual Value memo
      typed_pairs[TypedPairKey::Value(K)] in that very state;
  (b) every Pending Value memo is admitted to the current diagnostic delta;
  (c) delta and its index map agree, name actual Value memos, and contain no
      repeated key. Thus any child outside delta is Complete.

The identity K in (a) is the recorded raw pair, even if its endpoints have
subsequently acquired different representatives. A canonical replacement
memo, a Context relation, origin metadata or an enqueued but unprocessed
task is not substituted for that memo.
```

The proof below covers actual alias, retained/new rewrite, structural,
ordinary replay and settlement replay constructors in both initialized graph
modes. It supplies the memo-existence/completion-admission part of SUFFIX250's
valid-reference premise. Other index, witness-extension and well-formedness
premises retain their original owners. It proves neither diagnostic adequacy
nor complete semantic evidence. Full parent/A/B delta remains **0 -> 0**.
Lean declaration/type/axiom audit: NOT APPLICABLE; Lean/checker NOT RUN under
the explicit source-only lease.

## 2. Distinct inventories and the consumer

Write `b=(owner,p,item)` for a raw physical BoundKey and `C(b)` for its current
endpoint-wise canonical image. A physical slot remains on its original row;
reading an opposite bound canonicalizes its item. Let `Fib(b)` be the actual
linked list returned by Context's `bound_cursor/bound_entry` at the exact key
`b` (context:3684-3694). Its members are executable RelationIds, not diagnostic
origins from effect-algebra `origins[b]`. A transported fiber, its source fiber,
an origin pair, a Replay vector position and a child task K remain distinct.

`candidate_replay_bound` canonicalizes owner/bound/other, constructs K from the
two Value endpoints, and records P -> K **before** constructing Replay
(extrusion:1070-1111). The consumer does not infer that K exists from that edge.
In `complete_diagnostic_delta` (lib:15628-15991), delta/index membership selects
internal edges; every external or already completed SCC child is looked up at
the exact `TypedPairKey::Value(edge.child)` and must be Complete
(lib:15855-15872). A missing memo and an old Pending memo are separate invalid
cases. No lookup canonicalizes `edge.child`.

The proof therefore needs an actual task with that exact K and its real
Dispatch, plus delta discipline. A relation with equal canonical endpoints
alone proves neither. The weaker executable-fiber nonemptiness lemma in the
next section is sufficient to establish such an emission. It does not equate
raw and canonical fiber sets and does not solve full R71.

## 3. Physical bounds have a real executable fiber at replay boundaries

Use stable owner boundaries: completed insertion-plus-transport operations,
completed extrusion Work::Bound/IncomingAllowance actions, and the end of a
merge's canonicalization before replay. At these boundaries:

```text
FIB261:
For every physical slot s with raw stored key b_s:
  Fib(b_s) is nonempty, and Fib(C(b_s)) is nonempty.
All raw entries witnessing these facts remain retained on successful forward
execution. An in-progress scoped copied append instead owns the immediate
transport obligation described below; no replay or Diagnostics cut occurs
between that append and its transport.
```

Only existence is asserted. Different origins need not share a fiber, and the
canonical list may have additional fibers not represented at the raw key.
No identity-context alternative is manufactured for a scoped transport.

**Empty base and physical writers.** Session initialization appends default
empty Value/Effect bounds (lib:10412-10464); `try_new_candidate` then starts
the empty GraphState (lib:10501-10505; scheme:2528-2552). Fresh row constructors
also append default empty bounds (lib:10521-10578). Their FIB261 obligations are
vacuous. On a graph-enabled route, Value and Effect application return through
`candidate_apply_value/effect` (lib:16302-16305,13829-13842). Legacy direct
Value/effect vector pushes and their six diagnostic replay loops are therefore
inactive here. The capture graph's copied frontier vectors are observations,
not live solver bounds; direct test mutations are cfg(test).

The non-test live physical append owner in this closure is
`candidate_insert_bound_with_evidence` (extrusion:702-875), called through the
ordinary, copied, ExtrusionLink and restoration adapters. It canonicalizes both
endpoints, admits the cause before append, appends one addressed slot, reads
that slot back, checks the full key, and records its physical emission. Bounds
and Context's raw bound entries are not deleted by successful commit. Rollback
and cfg(test) mutation are excluded by the inherited domain, not used as
constructors.

**OwnerEmission and ExtrusionLink.** `candidate_bound_origin_with_evidence`
(effect:890-957) calls `candidate_context_bound` or
`candidate_context_extrusion_link` before the physical append. The shared body
(context:4317-4355) constructs an actual relation, records Derived and attaches
it at that exact canonical BoundKey. `attach` (context:3702-3715) either finds
that same relation already present or prepends a real entry to an existing
finite list; either case gives nonemptiness. The origin-table duplicate arm
is after this fiber construction, so duplicate origins cannot suppress it.
This covers ordinary Value/effect bound additions, signature/effect-port
initialization (effect:2694,2725,2815), and the one-sided source link created
for every actual deep-row copy (extrusion:137-138).

**Scoped copied bounds.** `candidate_insert_copied_bound` deliberately admits
BoundTransport with `relation=None` in scoped mode (extrusion:619-633;
effect:905-907). That append alone does not establish FIB261. There are three
production callers, each immediately followed by `candidate_transfer_bound_origins`:

| Caller | Exact source and destination |
|---|---|
| Work::Bound, extrusion:399-417 | Raw selected source `(endpoint,p,raw_bound)` saved at Visit; destination `(canonical(copy),p,canonical(mapped_bound))`. |
| Work::IncomingAllowance, extrusion:371-397 | Its retained exact incoming source key; canonical mapped source/Allowance destination. Replay is delayed until all selected copied fibers finish. |
| ParentCopy, intrusion:642-664 | Source `(copy,side,canonical(item))` read from the live canonical copy; destination `(parent,side,canonical(item))`, before changing the representative. |

For Work::Bound, the selected physical slot's raw key supplies a real source
fiber by the induction hypothesis. Its child map key is canonical, but that
does not replace the raw key used to read fibers. For IncomingAllowance, the
capture record was installed from the actual Negative Allowance bound through
`candidate_register_capture_bound` (effect:1035-1043); extrusion does not change
representatives, so its canonical source key is the current image of that
physical bound. For ParentCopy, `candidate_opposite_bound` already returns the
canonical item (extrusion:897-932), so the **canonical** clause of FIB261 is
used, rather than pretending the source slot stored that item originally.

The first transfer loop (effect:1051-1058) captures `bound_cursor(from)` and
transports every real member. Each successful
`candidate_context_transport_witness_with_evidence` records the actual source
snapshot/Transport/FiberTransform and calls `attach(to,child)`
(context:4737-4751). Thus any one retained source member supplies a real
destination member. The following origin loop is separate: it records
`MissingOriginAssociation` and relation None in scoped mode
(effect:1076-1084). It is not used to prove the existence claim. In unscoped
mode the bootstrap already creates an OwnerEmission fiber; transfer retains
additional actual fibers without destroying that one.

Between a copied append and its first-loop transport, helpers reserve, journal,
record metadata/capture incidence and sample resources; they do not dispatch,
replay or enter Diagnostics. In extrusion representatives stay fixed and raw
slots remain intact. The complete Work loop finishes pending copied actions
before the final initialized-Allowance replay (extrusion:580-586). Thus a
temporarily uncovered scoped copied slot is not a reached replay input.

**FreshUse and restoration.** `begin_candidate_fresh_bound`
(scheme:4948-4993) constructs the mapped endpoints from that same retained
FreshUse, calls `candidate_context_fresh_transport_scoped` for each captured
Some(parent), and only then begins physical restoration. In scoped mode that
transport canonicalizes the destination, creates its independently transported
flow/source/context relation, records the exact FreshUse Transport and attaches
it (context:4697-4710). The subsequent admission validates and reuses that
actual mapped relation (context:4678-4695; effect:901-904). There is no merge
between attachment and append. A captured None cannot silently seed an empty
scoped bound: it returns ReceiptMismatch before append. In unscoped mode the
ordinary context-bound admission still supplies a fiber even for None.

Graph capture (scheme:2351-2398) may represent an absent fiber by a None record;
this is not evidence that an accepted successful scoped restoration can append
it. Its all-source availability/authenticity issue remains open. The argument
here follows what the successful actual constructor emits, without treating
the None fallback as a proof of missing-origin authenticity.

The restoration owns the inserted canonical bound before it reads its saved
opposite count (extrusion:966-985). At each later step it re-reads the live
canonical owner/item and selected opposite (extrusion:1042-1067), after any
earlier child's merge has completed its canonicalization. Thus FIB261 supplies
both actual replay input lists then, even when the representative changed
between restoration children. The restoration path itself records no Value
diagnostic edge; its executed children can use the ordinary producers below.

**Merge and third-owner canonicalization.** A merge first copies both bound
sides and transports their executable fibers while representatives are still
unchanged (intrusion:642-664). It then redirects the actual representative,
calls `candidate_context_canonicalize_bounds`, and only afterwards increments
generation, reopens the Value root and replays the merged bounds
(intrusion:665-704). Canonicalization (context:4649-4669) takes the pre-pass
bound-entry count; each old raw entry `(b,r)` is retained and transported to
`C(b)` before any replay. Every preexisting physical slot already had a raw
witness in that prefix, including new copied slots. Therefore each has a
canonical witness after the pass. Newly attached entries need no second pass:
they are already at the final image under this fixed representative update.
This covers a changed item on a third owner's untouched physical vector as
well as the two merged rows. A later merge repeats the same argument.

Source qualification decides whether retained Parent pairs enter the pending
merge set; it does not remove an attached fiber. Unqualified copies keep their
source links/copied fibers; qualifying activation and retained rewrite reuse
can schedule more merges (intrusion:388-422), each using the same procedure.
No Link is treated as equality, and no R254 row-coincidence premise is needed
for this finite-prefix preservation statement.

These cases are an induction over actual physical writers and representative
updates. They prove nonempty exact replay inputs, while leaving full
raw/canonical fiber coverage, every source origin's association and transport
meaning in R71/evidence open.

## 4. Frontier and dependency suppression retain an actual child emission

For a `candidate_replay_bound` edge P -> K, let `l,u` be its exact canonical
lower/upper BoundKeys (extrusion:1105-1108). By FIB261, each list has a member.
Choose one actual pair of members `(a,b)`. Their existence is established from
the source constructors above, not assumed from P's origin metadata.

Context's `attach` prepends and preserves the old linked suffix. The two
quadrants in `candidate_context_begin_replay` (context:4427-4477) enumerate
new lowers times all uppers, followed by old lowers times new uppers; they
partition exactly the captured product minus the old/old product. Lists and
representatives do not change while this body builds its vector. Hence `(a,b)`
is either visited now, or lies in the earlier frontier's product.

The frontier is initially empty and is changed only by `replay_progress` at
the end of this actual enumeration, using that call's captured heads
(context:3695-3700,4479-4481). A successful-forward old frontier therefore
has an earlier enumeration event. Repeated backward lookup ends at the first
event containing `(a,b)`, strictly decreasing the finite history position.
An incoming FreshUse replay explicitly uses old=(None,None) and visits its
whole captured product even if an ordinary frontier already existed.

At an enumerated pair the constructor makes a concrete child relation with
the pair of its actual `task`, exact composed context/source union/scoped
payload, and exact `Dependency::Replay { child,a,b,l,u }`. Ordinary mode
suppresses vector insertion only if that full dependency already exists
(context:4463-4475). Replay dependencies have no other non-test creator:
`dependency` publishes them only from this callsite; the other dependency
calls construct Derived/Transport/structural ports. The dependency replacement
and synthetic Replay builders are cfg(test). Recipe retention alone is not
dependency publication or vector emission.

If the dependency was absent, the same nonreentrant iteration inserts it and
pushes its child into this real vector. If present, take its earlier first
publication; that first publication could not take the duplicate branch and
therefore pushed a real vector child. Incoming replay does not suppress that
push at all. A helper failure between dependency publication and vector push
does not supply a successful continuation; rollback/failed-route reuse is not
silently added to this domain.

Crucially, exact equal inputs `l,u` determine the raw Value task K at these
actual callers: K.lower=l.item and K.upper=u.item. They cannot denote a
different raw task after a representative change: changed endpoint keys give
different inputs, and canonicalization attaches fibers at those new inputs.
In the dependency-duplicate case the identical child RelationId also retains
the immutable pair field made by this actual constructor. Thus the earlier
real vector carried the **same raw K**, rather than just a canonically equal
pair. Context source union/interner sharing changes no raw operation task.

An earlier parent P0 or source occurrence can differ from P. The memo consumer
is globally keyed by exact `TypedPairKey::Value(K)`, not by `(P,origin,K)`.
P independently owns its new edge and admission/reopening. This argument
reuses only that same diagnostic child memo owner K; it does not merge P/P0,
source origins, residual/provider/witness lineages or operation identities.

**From a real vector to actual processing.** Ordinary production replay calls
`drive_replay(id,None)` immediately before another opposite is considered.
Reviewed ORDER260's nonreentrant batch argument (R260 section 4) gives the
whole vector's actual ack-bearing push_back items on successful return, not
just an abstract enumeration. The vector's task is K. The constructor cannot
yield a successful cut with a hidden untransferred async suffix. Every popped
item reaches Transport, Context, then Dispatch before its frame returns to
empty-current Transport (lib:14448-14471). Queue emptiness alone is not used
to skip that current item.

Restoration uses incoming=true, then its retained sync driver transfers one
real child into an actual typed frame before it can step that frame to
Diagnostics (context:4516-4550). Module restoration drives to completion;
the production local adapter continues its same restoration before moving to
the next bound (scheme:4513-4518,5430-5445). Every vector position has the same
K, so processing its first child already supplies K's memo; later positions
do not require fresh memo identities. The cfg(test) paused adapter supplies no
production reachability evidence.

Consequently an old emission witnessing suppression is either already
dispatched, on the actual queue, or currently owned by a real Dispatch
continuation. At the reached Diagnostics cut neither queue nor current nor
structural admission is outstanding (lib:14411-14445,14461-14509). If its sync
operation is still running, this cut is within its actual child execution;
that initial task has already dispatched. No as-yet-unprocessed successor
can be the sole witness: the first child has that very same K. Reclaimed old
operations are already completed; their exact K memo is retained. This proves
real processing, not merely an enqueue-is-memoized assertion.

## 5. Every actual Value Dispatch supplies its raw memo

For an actual item `Value(K)`, successful Context does not erase that task.
Transport may replace its relation with a canonical derived relation while
retaining the raw task (context:4186-4205). Context can consume exact Effect
Allowance work; it returns an error for filtered Value work rather than
silently consuming it (context:4218-4305). More directly, Value dispatch does
not branch on `context_consumed`; only the Effect branch suppresses semantic
application for that flag (lib:14545-14566).

`pair_is_current(Value(K))` explicitly requires `typed_pairs.contains_key(K)`
as well as current relation generation (lib:13594-13604). The duplicate return
therefore already has the **raw** memo; a canonical relation cannot suppress
first admission of a raw alias. Otherwise every successful Value Dispatch
arm admits K before returning or applying children (lib:14567-14974):

| Actual diagnostic producer | Actual child-to-consumer continuation |
|---|---|
| Canonical alias, lib:14571-14576 | Admit raw K, record K -> C(K), enqueue that exact canonical task. Subsequent representative changes can make it another raw alias, whose own raw memo is still admitted. |
| Retained extrusion rewrite, lib:14580-14600 | Re-admit K; replacement preserves its actual prior children/rewrite. Recapture qualifying groups; construct rewrite relation; enqueue the retained rewritten raw task. The original new-rewrite event already recorded its diagnostic edge. |
| New whole-Value rewrite, lib:14820-14866 | Finish extrusion, admit K, record K -> rewritten, retain this actual rewrite, enqueue that exact task. |
| Variant payloads, lib:14632-14700 | Admit K; missing alternative produces a direct witness and no child edge. Otherwise record every actual payload child, retain the finite dispatch vector and enqueue every entry through VariantAdmission/Enqueue. |
| Record fields, lib:14702-14762 | Admit K; missing required field produces a direct witness and no child edge. Absent optional fields produce none; unsupported optional-to-required adaptation fails before successful publication. All retained children pass RecordAdmission/Enqueue. |
| Tuple elements, lib:14764-14813 | Admit K and all exact indexed child edges; TupleAdmission/Enqueue consumes every retained entry. |
| Function, lib:14902-14974 | Admit K; record Argument and Result Value edges, retaining their field metadata. ArgumentEffect and ResultEffect are actual Effect tasks but no Value diagnostic edge is recorded for them. All four pass FunctionAdmission/Enqueue. |
| Ordinary row/bound application, lib:14890-14902; extrusion:1115-1145 | Admit K before `candidate_apply_value`, which records the replay edges handled in sections 3-4. Equal endpoints add no bound/edge; nonrow atom pairs add none. |
| Incompatible shapes, Bottom/Top and terminal compatible pairs | Admit K with direct witness or no witness; create no unsupported child edge. |

The four structural adapters (lib:15060-15160) read the actual retained vector
entry, admit its proper named port relation, save its exact pending TypedWorkItem,
enqueue it, then advance `next`. They do not drop an entry on relation/memo
equality. The frame cannot return to Transport until the adapter is exhausted.
The direct reverse-enqueue fallback is inactive on graph-enabled structured
drains: their Dispatch always passes Some(index). The noncandidate fallback
and legacy `apply_value_task` loops are explicitly outside this graph route,
not omitted accepted constructors.

At a reached cut all these actual child tasks have dispatched by the same
queue/current argument as section 4. Each gets its raw memo even when it is an
alias, already Complete, Context-related, or a memo duplicate. Admission
replacement preserves retained children/rewrite (lib:15459-15477), so old
edges are not silently discarded. Old child memos are not removed by successful
commit; the sole typed-pair removal located here belongs to rollback
(lib:9870-9872). Induction therefore retains their reference existence too.

Settlement replay is the remaining producer. A Value initial root has already
dispatched before its frame's empty-queue settlement. Each genuine merge
reopens that exact raw root, admits it into delta, then calls ordinary
`candidate_replay_bound(...,root)` after transport/canonicalization
(intrusion:693-704; lib:13585-13591). Sections 3-4 give all its actual children.
An Effect initial root supplies None and creates no Value diagnostic edge
directly. Same-representative settlement entries create none. The next
Transport iteration pops the resulting work; it cannot jump past it to
Diagnostics. This covers qualified activation and retained-rewrite recapture
without asserting all retained Parents qualify.

These are all non-test `record_diagnostic_*` callsites in the pinned production
closure: Dispatch's alias/structural/new-rewrite sites, the ordinary replay
site, and the inactive legacy loops. Retained rewrite reuses old recorded
edges rather than minting an untracked producer.

## 6. Pending memos, delta clearing and exact consumed state

`record_typed_pair_admission` reserves memo/delta storage, creates or replaces
the actual raw Value memo, and calls `admit_diagnostic(K)` before returning
(lib:15400-15488). All Value creation/replacement arms request Pending.
`candidate_reopen_root` is the other production Pending assignment; it admits
the exact root before setting Pending (lib:13585-13591). Section 5 establishes
its root memo, rather than assuming a missing lookup is harmless.

`admit_diagnostic` inserts K iff absent and writes its vector position to the
index map (lib:15255-15269). Between clears it never removes an individual key.
Thus vector/index agreement and no duplicates are preserved. Existing Complete
memos may be re-admitted and become Pending; their exact same K is in delta.
A duplicate Dispatch changes neither completion nor delta.

It matters that `clear_diagnostic_scratch` clears delta and its indices too
(lib:16039-16090). The proof does not treat delta as permanent. The relevant
clear sites are drain start and successful diagnostic completion/final clear.
The noncandidate loop is bypassed by graph-enabled execution. Failure cleanup
is not a successful-forward continuation; the test-only standalone clear is
not source execution.

There is no intervening clear in this actual nonterminal typed call graph:
Transport derives a relation; Context discharges filters and may apply/replay
Effect bounds; Dispatch performs the cases in section 5; structural adapters
only admit/enqueue; settlement copies/transports/canonicalizes/replays bounds.
Their replay driver uses provenance=None, never starts a synchronous drain.
Effect operand checks enqueue Support/tail/member work or record a conflict
(effect:1605-1675); view remapping only constructs a view
(effect:1523-1565). None invokes source generation, scheme FreshUse/restoration,
`start_typed_drain`, or scratch clear. Resource/journal helpers do not dispatch
or call source generation (the same nonreentrancy used by reviewed R260).

The actual source and module/local restoration drivers are outside that closed
nonterminal call graph. `run_candidate_typed_drain` loops until the frame is
removed before returning to its source caller (lib:14340-14364); synchronous
restoration similarly drives its actual child and delivers Ready before the
next child/source action. A saved terminal frame has already passed Diagnostics;
it contributes no Pending memo which a new start could orphan. The private
test retained adapter does not enlarge this domain. Therefore queue emptiness
is not incorrectly used as authority to clear an unfinished outer nonterminal
delta. A newly started real source/restoration drain begins after prior
diagnostic completion, not in the middle of one of these Value producers.

Induct over actual successful diagnostic completions, starting with no memos.
After one completion, every member of its delta has been written Complete
before the routine clears it (lib:15951-15989); by the inductive Pending
invariant there is no Pending key outside it. Until the next reached cut,
every new Pending key comes from the two admitted owners above and no such
key is cleared. Thus every Pending key at that cut belongs to its actual delta.
This does not assume the present cut completes: it uses only earlier finished
cuts plus the constructor preservation to this one.

Sections 4-5 show every recorded child has its retained exact raw memo at this
cut. The Pending invariant means any child outside delta is Complete. These
are the exact classifications consumed by the SCC pass, not a future state
after another drain. Within that pass, cross-SCC children become Complete in
the finite child-before-parent order already established by reviewed SUFFIX250;
same-SCC children are handled internally. No semantic work grows this graph
during Diagnostics. Witness extension validity/report adequacy remain separate.

## 7. Application to SUFFIX250 and remaining premises

Fix an actual Diagnostics entry H of frame F. The source guard has no popped
item and no dirty remaining settlement work; all semantic producer continuations
for this frame have completed (lib:14411-14509). REF261 gives actual child
memos, Pending-in-delta and Complete external children there. ORDER260 gives
the authoritative ordered uncompleted ack suffix, with R249 owner retention.
Instantiate SUFFIX250 with these two constructor-derived inventories at this
very H, retaining its successful helpers and remaining finite/index/witness
well-formedness premises. Its fixed diagnostic graph work and terminal rank
then apply: Diagnostics creates no typed work/pending merge; the ordered suffix
reaches ReturnReady and frame removal on successful steps, with exact sync
Ready delivery where present.

Before R261, memo-reference validity at that edge was an unproved all-source
condition. This candidate supplies that condition through actual physical
writers, executable fibers, real Replay vectors, actual dispatch and delta
consumers. It does not rely on R259's one-route emission certificate. The
source-wide successful-helper premise and eventual entry into Diagnostics are
unchanged, so R70-DRAIN-1 and the full soundness parent remain OPEN.

Remaining owners/premises:

* Eventual Diagnostics: ordinary dispatch/extrusion/settlement/replay owners,
  including the cross-invocation birth charge investigated by R250 onward.
* R70's other W clauses and all-source successful helper execution: their
  original initialization/term/view/forest/context consumers. REF261 proves
  the named memo-reference clauses, not a complete W predicate.
* R71/evidence: full raw/canonical fiber coverage and source-origin-to-fiber,
  antecedent, FreshUse and transport authenticity. FIB261's one real member
  per exact physical key is weaker; no such semantic association is inferred.
* Diagnostic witness-extension validity, effect-root report coverage and
  adequacy: complete_diagnostic_delta/replay_witness/effect conflict owners.
  R250's observation that completion clears delta before the later Effect-root
  witness loop is preserved; no reachable missed report is asserted here.
* Full Call, hygiene, qualifying-intrusion adequacy, generalization, F1/FK1,
  foreign continuations and source/evaluator soundness: unchanged independent
  obligations. No local typed frame supplies a foreign-continuation theorem.

No accepted-prefix unadmitted-child counterexample was established. No
production defect follows from the open stronger authenticity obligations.
**NO_SAFE_CODE_SLICE**: the actual lib memo/diagnostic consumers and
extrusion/context/merge bound-replay owners were inspected; no concrete
accepted-source violation of an approved clause justifies production edits.

## 8. Reuse, checks, resources and freeze

Reused at actual premises: R70's conditional mutable extrusion body/call graph
by `/root/r70_ordinary_extrusion_proof` with complementary
`/root/r70_extrusion_countertrace`; R249 lifetime retention by
`/root/sol_r249_prior_owner`; R250 SUFFIX250 by
`/root/sol_r250_drain_progress`; reviewed R260 ORDER260 by
`/root/sol_r260_replay_ack_order`, independent review
`/root/sol_r260_independent_review`. Their reviewed dispositions are supplied
by R260's frozen inputs. R259's local route does not establish this result.
Manifest inclusion does not claim every historical note was newly read.

Rejected methods: edge recording as emission; enqueue as memoization; canonical
relation completion as raw memo admission; origin count as executable fiber
coverage; scoped BoundTransport relation None as an identity alternative;
full raw/canonical fiber-set equality from mere nonemptiness; frontier
suppression without an earlier real Replay vector; clearing delta while
assuming it remains populated; testing synthetic transitions as source proof;
source narrowing; converting reached-cut suffix progress into eventual entry.

Three substantive stages: (1) constructor/consumer inventory and pin validation;
(2) physical-fiber/emission/raw-memo/delta induction and parent application;
(3) bounded adversarial reread, dependency/output validation and freeze.
Skills used: yulang-proofs and yulang-proof-portfolio; required Lean skill
policy read, with no Lean execution under the explicit prohibition; sprint
skill/rules govern this leaf. No descendants or reviewer appointment.

Active receipt sent to Luna: actual task identity
`/root/sol_r261_diagnostic_reference_closure`; first explicit clock
2026-11-02 08:42:17 UTC with setup reads shortly before. Requested Sol/high;
observed runtime model/effort and session UUID UNKNOWN. Central snapshot
labels are not substituted for exposed runtime metadata. Provider active
time/CPU/RSS UNKNOWN. Hard grant 2400 active seconds; conservative charge and
terminal clock appear in the frozen handoff. No budget expansion/reset.

Checks: bounded read-only body/symbol/physical-writer searches, SHA-256, source
constructor/consumer derivation and final output whitespace/hash checks. The
first local manifest regex expected plain hash lines and matched zero table
rows; that vacuous result was rejected, the table parser corrected, and all
36 actual direct pins verified MATCH. Luna's initial revalidation before the
assignment was also part of the admission receipt. All four R260 inputs and
the R261 contract matched. Some oversized display output was truncated;
relevant bodies were subsequently read in bounded chunks.

No Lean/build/test/probe/Cargo/benchmark, production/test/expectation edit,
Git/ref command, external contact, central-state write, runtime/quarantined
access, scratch/cache/generated output, nested CLI or model switch. Only the
two exact leased files are written.

Dependency authority: R255 manifest
`tasks/agent-loop/sprints/source-owner-coincidence-r255.md`, SHA-256
`f6138d36052934093328e34c01102fc9155ea9d8a0ccfd19182af6e7e2d946ef`,
all 36 direct pins; the four separately frozen R260 inputs in the R261
contract authenticate the admitted reviewed R249/R250/R259 inputs transitively.
No new source dependency is introduced. Final verification and exact artifact
hashes are in the handoff/external freeze receipt.

Mutual TODO `R261-REVIEW-1`, Luna: fresh independent review of sections 3-7.
Falsifiers: an actual successful non-test writer leaves both relevant raw and
canonical replay inputs empty; a recorded old frontier/Replay dependency has
no earlier same-raw-K vector emission; a reached cut still has its sole K
task unprocessed; a real Value dispatch skips raw admission without an existing
raw memo; or an actual nonterminal source callback clears Pending delta before
completion. Inputs/outputs remain this frozen contract and these two paths.
This TODO grants no writer or production rights.

Mutual TODO `R261-REMAINDER-1`, Luna: retain the distinct section 7 premises
with their source owners. In particular do not relabel FIB261 as full R71
coverage or origin/fiber authenticity, nor REF261 as full R70 closure. The
next in-envelope action after freeze is independent review, owned by Luna.

All new paths: this note and
`tasks/agent-loop/inbox/diagnostic-reference-closure-r261.md`.
Scratch/generated/unresolved descendant paths: NONE. Revision 1 freezes only
with the final hash/stop receipt. After that receipt the author is
**STOPPED / WRITES_STOPPED**; review/adjudication/state/Git remain with Luna.
