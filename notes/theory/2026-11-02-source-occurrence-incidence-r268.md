# R268 — source occurrence incidence stops at required-lineage coverage

Revision 1. **Candidate source-native evidence; R268 INCOMPLETE/BLOCKED.**
Sole author `/root/sol_r268_source_occurrence_incidence`; no descendants or
coauthors. Contract R268 revision 1:
`tasks/agent-loop/sprints/source-occurrence-incidence-r268.md`, SHA-256
`719497ad1921be23329a8df790e942ba5c63170ed2bae4880c9656634389ad72`.
Baseline supplied by Luna: `8d646ac2ed171e13a529e25e035fc75f91678b0b`.

## Parent and result

The unchanged edge is inference soundness → R70 copy correspondence →
`R71-RAW-CANONICAL-FIBER-COVERAGE-1`. Preserve the complete accepted source
domain, Simple-sub A/B, independent satisfying assignments, shared witnesses,
F1/FK1 and foreign continuations. Parent/A/B delta is **0→0**.

This packet reconstructs the forward source-event/Parent-index/selected-slot
equations and compares their information with actual ordered Replay incidence.
It does **not** construct an accepted-source history realizing the required
canonical candidate and consumer. In particular, the formulas below for a
reached constructor instance are not evidence that an aliased instance is
source-reachable. No required candidate is inferred from bucket membership.
No source-qualified counterexample, source-wide coverage theorem, or production
defect is established. The first missing preservation obligation is §4.

Lean theorem declarations/types/axiom audits: NOT APPLICABLE; no Lean work or
checker execution was authorized. The result has not received independent review.

## 1. The forward source spine and its exact stopping point

The governing occurrence association selects an actual extrusion occurrence,
its source origin and receiving Values, and its produced polar parent/copy
pairs. It explicitly supplies neither a permanent type-row owner nor a new
fiber transport convention. The top-level principles §1.1 require ordinary
constraint generation, extrusion and qualifying intrusion with retained pairs.
Neither authority says every candidate in a canonical bucket is independently
required at a particular copying occurrence.

For an Apply actually retained by the accepted source constructor, let a be its
HIR occurrence, e its checking event and i its call index. These names refer to
the actual constructor's identities, not invented source rows. The inspected
owners give the following partial forward chain:

1. `candidate_value_graph.rs:329–344` inserts
   `checking[ConstraintOccurrenceId(a,0)]=e` and retains
   `events[e]=(owners[a],resolved_callee_value)`. The enclosing definition owner
   and an Apply result remain distinct Values. `:395–397` qualifies e by the
   actual sealed component comparison of those two Values.
2. `candidate_source.rs:1869–1924` retains the Apply endpoints, recipe,
   checking/cause, level and source call index i. `Action::Candidate` executes
   the retained recipe through `execute_candidate_action:2492`.
3. `shadow_apply.rs:4302–4399` constructs the negative Function demand U from
   the actual argument, argument effect, invocation effect and application
   result; stores the native registration before admission; and admits
   `(actual_callee,U)` at checking slot 0. This does not identify application
   result, Lambda body and definition root. `Action::Link:2482–2486` admits a
   constraint, not a row equality.
4. `candidate_context_seed:3793–3838` looks up that exact checking event and
   seeds its source set. A scoped demand with `original_call=i,use_instance=0`
   is added only when scoped mode and the retained introduction permit it.
   Source-event retention alone does not imply that introduction exists.
5. The actual structural/row branches at `lib.rs:14814–14843` call extrusion
   with the structural endpoint, its sign and the opposite row's actual level.
   This establishes the entry equation when that task is reached; it does not
   establish that every accepted Apply takes either branch or creates a Parent.

No concrete accepted-source fixture with the aliased selected direct-row slot
and a named necessary canonical candidate was established. Consequently the
rest of the trace is a source-body characterization of reached local instances,
not a completed accepted-source occurrence construction.

## 2. Parent indices determine a complete local slot family, not its necessity

At `candidate_extrude:24–34,84–180`, let Ω be the allocated occurrence. For each
first deep-row Visit `(v,p,L)` in R70's successful local envelope, let j be
`parents.len()` immediately before `retain_extrusion_parent` appends. Let v' be
the actual fresh same-kind row at L, and d/x the selected direct/exact lengths
sampled **before** the opposite-side ExtrusionLink. The code gives:

```text
parents[j] = (copy=v', parent=v, polarity=p, target=L,
              sources=S(processing_relation),
              comparison=processing_typed_pair, occurrence=Ω).
pending contains j iff the retained source set has a qualifying event.

Sel(Ω,j) = every addressed selected slot n with 0 <= n < d+x.
k_n = (v,p,actual_stored_item_n).
child_n = (canonical(actual_stored_item_n),p,L).
destination_n = (v',p,operation_local_image(child_n)).
```

The Parent fields and existential qualification are read directly from
`candidate_intrusion.rs:305–365`. They do not include a selected RelationId or
physical slot. The index j is a proof index for this actual append, not a new
runtime field. Sign-specific memoization can reuse a previously completed Visit;
it does not create a second Parent for that same Visit key.

Each n schedules its own raw key and canonical child separately. All duplicate
physical slots are included. A repeated row child may share its image while
each scheduled Bound remains. Function ports use the actual four child keys,
opposite sign for Argument/ArgumentEffect and the original sign for the result
ports (`candidate_extrusion.rs:290–335`). Earlier opposite-sign links can be
in a later Visit's selected snapshot: d/x are not entry-time snapshots.

At the later `Work::Bound:399–417` transfer cut t_n, the executable prefix is
exactly the linked list captured by `bound_cursor(k_n)` at that cut. It need not
be the list at row Visit time. `candidate_effect.rs:1045–1089` saves each next
cursor and transports every retained relation r in that captured prefix. The
actual witnessed child and FiberTransform retain r, k_n, destination_n, reason,
antecedent snapshot and coverage. Missing evidence associations remain missing.

Insertion/readback certifies the physical destination at constructor time
(`candidate_extrusion.rs:702–875`). In scoped mode copied BoundTransport bootstrap
can have relation None; it supplies no absent executable candidate. Unscoped
bootstrap has its own Owner-style relation. The metadata origin loop is separate
from the executable prefix. These facts establish local forward incidence for
actual raw parents; they do not establish which canonical parents are required.

## 3. Meeting ordered Replay exposes a projection gap

For an actual ordinary Function Replay at canonical owner o, the exact keys are
`(o,+,PositiveFunction(L))` and `(o,-,NegativeFunction(U))` in that order,
independently of insertion polarity (`candidate_replay_bound:1070–1111`). The
builder `candidate_context_begin_replay:4411–4497` reads those exact heads and
prior heads, enumerates new-lower × all-upper and old-lower × new-upper, and
retains each actual `(lower_relation,upper_relation,lower_key,upper_key,child)`.
Incoming restoration resets prior heads under its own rule.

For those actual parents l,h and child q:

```text
K(q) = J(K(l),K(h));     S(q) = S(l) union S(h).
flow(q).transformer = compose(flow(l).transformer,flow(h).transformer).
flow(l).demand = None;  flow(q).demand = flow(h).demand.
```

Thus e∈S(q) gives a disjunction of parent memberships. It does not identify the
upper parent, nor identify e with an upper scoped demand's original call. No such
identification is needed or asserted as a new semantic law. A proof must instead
retain the actual ordered parents and whatever source ancestry each has.

Qualification uses the whole processing source set (`extrusion_sources:3535–3538`)
and an existential component match. Parent comparison retains a TypedPairKey;
Context processing retains a RelationId. Those are different identities. The
Parent/source-set projection does not invert Replay or select a canonical
candidate. This is an information boundary in this reconstruction, not proof of
source-reachable ambiguous or missing execution.

At the Function port the authentic root check uses the actual processing
relation's negative Function root; it then creates the field-specific scope
operation (`candidate_function_port_admit:3924–3988`). Passing that check cannot
construct an earlier slot/canonical-candidate incidence. Exact dependency novelty
and equal interned child IDs likewise do not identify different Replay recipes.

## 4. First missing preservation equation

Fix an independently justified accepted-source derivation D and an actual reached
copying occurrence Ω. The following is the **unproved obligation**, not a
conditional theorem or a newly assumed interface. Write `Need_D(Ω,j,s,c)` only
for the missing judgment that D requires canonical candidate c for the selected
slot s belonging to Parent index j. It must be justified from the unchanged
source typing/occurrence obligation, independently of bucket membership and
successful helper execution.

Let Family(Ω,j,s) include every selected physical slot in the relevant canonical
class, with each slot's own transfer-time captured prefix. The first missing
slot-family lineage-cover equation is:

```text
For every source-required (Ω,j,s,c),

Need_D(Ω,j,s,c)
  ==> c's required continuation is covered by the union, over
      s' in Family(Ω,j,s) and r in captured_prefix(B(s'), transfer_cut(s')),
      of the ACTUAL witnessed copy continuations of r,
      together with ACTUAL independently supplied bootstrap/restoration paths.
                                                        (INC268)
```

“Covered” here requires the original proof-relevant source/consumer
correspondence: exact pair, source/scoped identities, all transport witnesses,
and actual ordered opposite inputs at each reached Replay. It is not equality
of RelationId sets, scalar contexts or endpoints. No covering relation with those
properties was constructed. More fundamentally, no instance of the left-hand
need judgment for the proposed canonical c was independently established. This
is the first failed source-to-carrier proof step; it is not a falsified runtime
equation. A particular c cannot be chosen just to make the right-hand side fail.

The first constructor case that would require this preservation step is a
successful earlier EqualityCanonicalization `r:k → c:C(k)` followed by selection
of a stale direct-row slot k. Forward sweep supplies c at C(k), and the later
raw prefix supplies r at k. To apply INC268 one must establish c's independent
necessity and either its actual covering continuation or a justified square
using r, preserving c's distinct equality witness. The code's forward transports
do not themselves supply that square or reverse saturation.

Owners: source necessity starts at `emit_candidate_source` / Apply recipe
admission and the unchanged R70/R71 source-to-copy proof interface. Native
preservation meets at `candidate_extrude`'s selected-slot scheduling and
`Work::Bound`, `candidate_context_canonicalize_bounds`, witnessed transport,
`merge_candidate_rows`, `begin_candidate_fresh_bound`, and the exact Replay
builder/Function-port consumer. Parent provenance alone is insufficient input.

Both attempted directions stopped at this same obligation: forward source
association yields Ω/j/slot equations but no necessary c; backward consumer
incidence yields exact l/h but no accepted-source slot-family inverse. No renamed
conditional theorem is offered. Luna directed freeze at this material obstruction.

## 5. History coverage, application and remaining work

The necessary competing paths are identified but **not completely accounted for
in an actual accepted-source history**:

- every selected direct/atom slot, duplicate, canonical-equivalent slot and its
  own captured transfer prefix;
- both pre-merge polarity sides, earlier completed canonicalization and all
  third-owner aliases; the current merge's later sweep cannot justify its earlier
  canonicalized lookup (`candidate_intrusion.rs:599–705`);
- scoped bootstrap with relation None, unscoped bootstrap, incoming Allowance
  paths and later attachments to the same key;
- actual FreshUse antecedent/source/use map and scoped root/input/scope renames
  (`candidate_scheme.rs:4859–4883,4947–4995`), preserving independent use IDs;
- exact Replay heads/prior heads, dependency novelty, retained recipe, task
  transport, processing relation and each subsequent consumer cut;
- permitted history, partial failure and rollback/resumption, which are not
  implied by R70's successful stable local envelope.

R267-r6's reviewed exact Function-slot `k=C(k)` result remains applicable only
to that actual selected-slot case. The present forward indexing explains how
such a slot belongs to an occurrence/Parent's full local selected family. It
does not show that a later Function consumer necessarily descended from an exact
Function slot: a direct-row ancestor, alias, merge or FreshUse may intervene.
R70's raw-prefix fact therefore remains reusable, while R71 still requires
INC268. No new parent edge is discharged.

R267-r5 VD267 is reused only for retained Value relations. It gives P_t(r)=K(r)
there, including the reached Value Function parent, without supplying any path.
R265's TEMP265/Z265 definitions remain unchanged; Effect temporal simulation,
actual opposite-input ancestry and later Effect callback/residual cuts remain
OPEN. ENTRY-WF, drain/eventual Diagnostics, Q262-EPISODE, other R71 history and
rollback obligations, diagnostic adequacy, successful-helper coverage, full
soundness, A/B, F1/FK1 and foreign continuations remain OPEN.

Mutual TODO `R268-SOURCE-NEED-INCIDENCE-1` to Luna: obtain one independently
justified source-required candidate and its complete slot-family/ordered-input
tuple, or construct the source-wide required-lineage interpretation at the
unchanged proof interface, then prove INC268 over the actual owners. The exact
falsifier is an accepted-source reached consumer requiring that named lineage
after every competing path has been accounted for and shown absent. Neither a
failed diagnostic authentication nor an unequal ContextId suffices. Any new
dependency, observer or code lease needs a new Luna grant.

`NO_SAFE_CODE_SLICE`: Work::Bound/raw-prefix transfer and source qualification /
Replay/Function-port owners show a missing proof join, no demonstrated violation
of an approved clause. No production edit, instrument, test or repair follows.

## 6. Pins, provenance, resource and cessation

Read authority: R267-r6 contract
`000e0d4d4297026ab8b4c634b7d7e36f186070d04236f852d9f6ae189e7277c9`
and R255 manifest
`f6138d36052934093328e34c01102fc9155ea9d8a0ccfd19182af6e7e2d946ef`;
only their exact operational/direct inputs and the fourteen listed Rust/HIR
bodies were eligible. Initial sha256sum gate matched all extracted R267-r6/R268
direct pins and all 36 R255 entries before source-body reads. Final gate and
artifact hashes are recorded in the frozen handoff and terminal receipt.
Bulk operational output was truncated; exhaustive comprehension of truncated
text is not claimed. Exact subsequent reads supplied active authority, process,
role and proof obligations used here. Historical links supplied no extra reads.

Reused under actual premises: R70 by `/root/r70_ordinary_extrusion_proof` with
complementary `/root/r70_extrusion_countertrace`; R71 by
`/root/r71_raw_canonical_proof`; R265 by
`/root/sol_r265_consumer_lineage_51dd6af`; VD267 by
`/root/sol_r267_consumer_lineage_r5`; INPUT267/SLOT267 by
`/root/sol_r267_source_input_join`, within their reviewed bounded claims. Their
frozen pins/authorship remain in R267-r6. No R261/R262 theorem is assumed.
R255 theory, R230 and all excluded/quarantined R263/R264/R266 paths remained
unread. No historical source-shaped example is promoted to accepted reachability.

Runtime identity matched before Luna GO; session supplied by Luna:
`01a1873a-a93b-7dc3-a8ce-028a7b543a80`. Requested registered prover, Sol/high;
observed model/effort UNKNOWN. Maximum 900 seconds, no reset/extension; full
reservation charged, exact launch-to-stop active seconds UNKNOWN. Observed
clock cuts 11:40:30, 11:42:01 and 11:43:56 UTC on 2026-11-02.

Only this theory and the one leased R268 inbox were written. No descendants,
Git, Lean, tests, builds, probes, Cargo, source/expectation edits, scratch/cache,
generated outputs or external contact. Luna's material-obstruction freeze
instruction ended further proof work. After the final pin/hash gate this writer
stops all reads and writes; independent review/adjudication belong to Luna.
