# Restoration products: local coverage and the unresolved rescue invariant

Date: 2026-10-10
Status: frozen, unreviewed research-only conditional derivation and exact
induction obstruction. R remains OPEN. No admitted-state counterexample,
source counterexample, universal rescue theorem, or production authority.
Assigned baseline: `1a3e694e8`, branch `research/simple-sub-intrusion`.
Producer: `/root/restore_product_rescue_proof`, bounded constructive evidence
leaf; no custom prover execution or independent review claimed.
Exclusive write lease: this note only.
Requested and observed model/effort: not exposed to this leaf.

## Claim, quantified states, and authority

The target is the later restoration half of R: for every valid admitted finite
candidate state and successful transactional scheme use u, every ordered
fiber obligation required by u must be emitted by restoration or discharged
by a later actual replay and the applicable diagnostic consumer. The stronger
source target additionally quantifies over actual parser/HIR construction and
normal action/provider schedules. This investigation does not prove either.

An admitted-state theorem cannot quantify merely over well-indexed vectors.
Its domain must be the inductive closure of the owning allocation, term/view
construction, admission, extrusion, capture/freshening, intrusion and route
rollback operations. Conditions such as idle worklist, representative forest
well-formedness and nonempty literal fibers are necessary local conditions;
they do not establish that a supplied graph belongs to that closure.

The operation equations below apply to successful calls on valid internal
states. They retain row and view identities, attachment occurrences and member
ordinals, exact RelationIds, directed context construction, and recorded
parent/copy provenance. No endpoint/spelling/family equality substitutes for
an ordered fiber witness. Original annotation scopes and provider order are
fixed by the use being quantified, not selected by this note.

Authority: the contextual attachment/admission design §§3.1–5, especially
ordered opposite replay, capture/freshening, qualifying parent/copy intrusion,
and whole-route rollback. Its two certified circuit classes do not authorize
arbitrary mixed admission or establish restoration completeness. Read inputs:
the positive-tail composition, selective-SCC proof, and selective-SCC source
witness notes. The source witness records 38 restores and 19 products for its
particular complete action schedule, with no qualifying merge; that finite
inventory does not establish the target quantifier.

## Exact restore and fiber-product equations

Write c_s(e) for endpoint canonicalization in state s. Only row endpoints are
renamed; Allowance/Support view IDs remain stable. A Function term is not
rebuilt merely because one of its port rows changes representative.

For owner o and selected bound side p, let D_s(o,p) and E_s(o,p) be the current
direct-row and exact-nonvariable **opposite** vectors. Their concatenation is
Q_s(o,p) = D_s(o,p) ++ E_s(o,p). Duplicated physical entries remain duplicated.
Write F_s(K) for the newest-first linked list of RelationIds under the literal
BoundKey K; attach deduplicates an identical RelationId within one key.

`candidate_restore_bound` first inserts the physical bound and attaches its
origin, then stores:

```text
o0 = c_s(owner)
b0 = c_s(bound)
N  = |Q_s(o0,p)|
```

N, o0 and b0 are local saved values. For each n = 0,...,N-1 it resolves o0
again, reads the current vectors at that integer, and canonicalizes that item:

```text
on = c_sn(o0)
an = c_sn(Q_sn(on,p)[n])
I  = BoundKey(on,p,b0)
J  = BoundKey(on,opposite(p),an)
(L,U) = (I,J) when p is Positive; (J,I) when p is Negative
```

The task uses (b0,an) or (an,b0) in that same orientation. The saved b0 is
not explicitly canonicalized again in the construction of I. Thus when b0
is a row whose representative changes after a callback, canonicalizing the
task elsewhere does not by itself make this literal fiber key current. For
the particular negative Allowance route, b0 is a stable view ID, so that
saved-row-item case does not apply.

At the start of `candidate_context_restore_replay`, let H_L and H_U be the
two literal fiber heads. Its first rectangle enumerates exactly

```text
F_sn(L) × F_sn(U)
```

in newest-first lower order, then newest-first upper order for each lower.
For each ordered pair (l,r) it retains

```text
context = IDENTITY if both input contexts are IDENTITY
          Replay(lower_context,upper_context) otherwise
dependency = Replay(child,l,r,L,U)
```

Distinct parent pairs may intern the same child relation; the dependency
certificate still distinguishes the ordered pairs. `incoming_use=true`
sets both old heads to None and bypasses dependency suppression. The second
rectangle consequently has no lower entries. The whole relation callback
list is constructed before its first callback. Each callback then constrains
one listed relation using u's occurrence and cause, drains the worklist,
settles dirty SCC intrusion, completes diagnostics, and returns before the
next callback. The next index therefore observes a later state.

This proves complete **literal-head snapshot enumeration**, not coverage of
the initial physical frontier, fibers attached during later drains, or final
canonical keys.

Code correspondence: `candidate_extrusion.rs:599–641,549–594`,
`candidate_context.rs:1951–2033,1529–1563`, and
`lib.rs:11328–11339,11799–11846,12083–12110`.

## Two useful bounded coverage lemmas

### Fixed-frontier restoration

Assume throughout one restore that the canonical owner, the canonical saved
item, both relevant bound keys and fibers, and the first N entries of Q are
unchanged. Then every initial physical opposite position is read once by its
index, and every ordered pair in its two literal fibers is listed and passed
to a constrain callback. Proof: integer induction on n with the exact product
equation above. Physical duplicates may repeat a pair; they do not invalidate
coverage. This does not assume that callback effects themselves are sound or
that all use diagnostics are reachable from a later final root.

### Ordinary replay certificate coverage

For fixed literal keys, successful ordinary replay retains certificates for
their current product. If the previously recorded heads represent older
lists L_old,U_old, and the current lists extend them by prefixes L_new,U_new,
the two rectangles are exactly:

```text
(L_new × (U_new ++ U_old)) union (L_old × U_new).
```

The old/old rectangle has certificates from prior successful replay. A novel
dependency is retained and enqueued; an identical existing dependency may
suppress enqueueing. Recorded heads are updated only after rectangle
construction. Initially heads are None. The append-only fiber lists and
rollback of both fibers and recorded heads justify induction over successful
replay calls for that literal key pair. This is certificate coverage; it does
not prove current-generation execution or incoming-use diagnostic discharge
when an old dependency suppresses a callback.

When a successful owner merge has transferred both sides, canonicalized
fibers and installed its representative, it synchronously loops over every
current positive physical entry and calls ordinary replay against every
current negative entry. No constrain callback/drain interleaves those loops.
Thus the same certificate lemma applies to all current products on that
merged owner at that merge snapshot. This is a substantial possible rescuer.
It does not cover an arbitrary third owner, fibers attached after that
snapshot, or the incoming-use reporting requirement.

Code: `candidate_intrusion.rs:549–603`,
`candidate_context.rs:1978–2029,2035–2055`,
`candidate_extrusion.rs:644–690`. These lemmas add explicit hypotheses and do
not claim new independent theorem closure.

## All changed-index cases and the missing induction step

The needed invariant concerns **old obligations**, not only newly inserted
bounds. For a restore/use obligation omega = (l,r,L,U), the proof needs to
show after each callback mutation that omega is already discharged for u,
is owned by a real queued comparison, or is guaranteed to be selected by an
actual remaining restoration/replay with the same ordered witness lineage.
Endpoint coincidence or a possible future comparison is insufficient.

The owning operations expose these distinct cases:

| Mutation between indices | Consequence for the saved N loop | Established rescuer / remaining obligation |
| --- | --- | --- |
| Append an exact opposite entry with unchanged owner | Existing opposite positions stay fixed; the new entry can lie beyond N | Ordinary admission of that new bound replays its opposites; direct physical insertion/transport needs separate coverage |
| Append a direct opposite entry | All old exact entries move right by one | Admission replays the new direct entry, but has no general loop over displaced old exact entries |
| Append several direct entries | An old exact position can shift by several places before its turn | Same missing old-obligation implication; increasing total bound count does not repair the fixed N |
| Merge the restoring owner as copy into a parent | The parent has its own old direct/exact prefixes followed by appended source entries; current indices address a different concatenation | Full merged-owner ordinary replay gives product certificates at its snapshot; use-time diagnostics and later fiber growth remain separate |
| Merge another copy into the current restoring owner | Incoming direct entries shift that owner's old exact suffix; incoming exact entries extend it | The same full merged-owner certificate replay exists |
| Change a direct item's representative without owner merge | The physical position persists, but its canonical item and literal key change | Canonicalize-bounds transports third-owner fibers; a universal corresponding third-owner replay was not found |
| Change the saved bound row's representative without owner merge | b0 remains historical in I even though owner/item reads are current | Equality transport creates current-key fibers; task normalization alone does not read those fibers under I |
| Attach an additional lower or upper fiber after a product list is frozen | The physical position can remain unchanged while the required ordered product grows | Ordinary admission can replay fresh fibers; transport/attach alone does not publish a callback |
| Revisit a physical duplicate instead of a displaced entry | A callback can repeat an already listed product while an old entry is never selected | Incoming mode deliberately permits repeats; repetition gives no other-key coverage |

Within a successful route, physical vectors append; they do not shrink.
Owner merge appends the copy's storage to its parent and keeps original
storage intact. Every representative transition follows an actual parent/copy
record and same-SCC qualification; arbitrary union is not permitted. The
vectors are partitioned into direct and exact lanes, so append-only storage
does not imply append-only order of their concatenation.

The exact missing constructor invariant can be stated as follows:

```text
For every admitted pre-use state s and successful use u,
for every callback-produced mutation m before completion of u,
for every previously required omega whose remaining selection is lost by m,
m's actual consumer path or the remaining actual use schedule discharges
omega with its ordered fibers/context and u's checking/reporting obligation.
```

The narrow unresolved induction premises are (a) displacement coverage for
old exact entries on direct append, (b) third-owner/key/fiber transport
coverage without owner replay, and (c) incoming-cause diagnostic accessibility
for suppressed ordinary dependencies. They must be proved from the admission
and capture constructors, or falsified by a retained admitted execution. The
ordinary insert-and-replay rule alone implies none of these three premises.

## Rejected local Function trace: why it is not a counterexample

There is an elementary local-loop schedule illustrating case (a): restore a
negative Function U on Value owner O with no direct lowers and exact lowers
[A,B]. Save N=2. Suppose the first comparison A <: U emits Function result
comparison X <: O with L(X)<L(O), inserting direct lower X on O. The flattened
sequence becomes [X,A,B]. Index 1 repeats A; the initial B position is never
visited. The new X <: U comparison may finish on X without touching B.
Taking singleton fibers makes the locally omitted pair explicit:

```text
omega = (relation(O,+,B), relation(O,-,U)).
```

Actual Function comparison does emit preserved result Value endpoints, and
actual Value admission at these levels inserts X as O's direct lower and
replays X. These are real transition rules, but **the assumed prefix is not
an established admitted capture state**.

If X was already older in the original graph, the earlier saturated A/U
comparison normally installed X on original O before capture. Capture visits
direct lowers before exact Function lowers, so X is present before the
fresh U restore and the proposed first insertion is not new. If X and O are
generic local rows, freshening allocates both at the same use level; at equal
levels X <: O stores an upper on X, rather than a lower on O. A nongeneric
exception or intervening merge requires its own constructor proof. No such
exception was manufactured or established here.

Consequently the schedule is a countermodel to the unrestricted inference
“new-bound replay rescues every displaced old bound,” with an explicitly
supplied mutation assumption. It is neither a valid admitted-state
counterexample nor an ordinary-source witness. It has no established missing
Value error, Effect error, retained occurrence/cause, or transactional retry.
It is not offered as evidence that the compiler has a defect.

Code: `lib.rs:12021–12082`, `candidate_extrusion.rs:692–724`,
`candidate_scheme.rs:189–215,440–487,841–853`.

## Subsequent restoration, final link, diagnostics and rollback

Capture emits a graph Bound for each literal fiber and deduplicates the exact
(kind,side,lower-node,upper-node,relation) tuple. Thus multiple fibers can
generate multiple later restores with separately saved counts. For Value
rows capture orders direct lowers, direct uppers, exact lowers, exact uppers;
Effect capture additionally visits incoming Allowance incidence first.
Freshening selects the row map before reconstruction and restores graph.bounds
in its recorded order. Each transported bound precedes its restore. These
facts supply real possible later rescuers, but do not guarantee that an
arbitrary missing omega has a later bound of the required key/lineage.

All graph restores finish before the final local Value link. That link uses
the fresh root and the actual lookup destination. It owns ordinary propagation
and diagnosis for that pair. It does not contain a separate loop over every
captured bound product. The module-use route likewise freshens before its
route publication. Source and provider order can determine what each frontier
contains; no schedule commutation or provider-order independence is proved.

Value ordinary bound replay records its diagnostic parent-to-child edge before
contextual suppression. Function comparison records argument/result Value
children. These edges can make previously retained Value failures reportable
even without a new contextual callback. Effect reporting traverses initial
and current canonical pairs through retained relation children; Derived,
FunctionPort and both Replay parents contribute edges. FreshUse Transport
alone creates no diagnostic edge from the template to the fresh use.
An Effect-initiated drain also reports its mixed Value diagnostic deltas.
None of these consumers reconstructs a missing ordered Replay dependency
solely from the existence of endpoint bounds. A full rescue proof therefore
needs checking coverage **and** actual diagnostic reachability for u's cause.

The local use wraps capture, freshening, restoration, final Value link and
route publication in `with_route_transaction`. Context rollback restores
relations, dependencies, literal fibers, recorded heads, origins, use count,
edge lists and discharge state; row/route rollback restores vector lengths,
levels, metadata, representative state, route records and errors. These
static correspondences prevent treating a failed prefix as a retained
witness. They do not constitute a complete rollback/retry theorem for every
consumer. In particular a rescue argument may not rely on fibers or memo
heads from a failed attempt: a successful retry must establish its own
restored-state coverage.

Code: `candidate_scheme.rs:411–532,998–1032,1053–1070,1111–1144`,
`candidate_extrusion.rs:666–675`, `candidate_context.rs:1449–1479,1070–1143`,
`candidate_effect.rs:524–580`, and
`lib.rs:9102–9135,9280–9410,12083–12099`.

## Result, limits and resource use

Result class: exact unresolved invariant plus local conditional/certificate
lemmas. The literal snapshot and full merged-owner certificate facts narrow
the rescue question. An exhaustive admitted-state rescue proof was not
constructed; no constructor-valid counterexample was constructed. R stays
open. No source reachability claim follows from the rejected local schedule.

The proof-obligation economy boundary remains unchanged: restoration checking
and required incoming diagnostics are compiler correctness/natural inference
obligations. Universal arbitrary graph characterizations are stronger research
claims. This note proposes no semantic restriction, new carrier, certificate
mechanism, invariant adoption, or production code change.

Checks were static owning-source and rule/design/note reads using `cat`, `rg`,
`sed`, `wc`, and dependency `sha256sum`; no test, build, executable model,
benchmark, Git command, external contact or delegation. Zero executable
samples, zero heavyweight processes, zero performance measurements. Sequential
lightweight shell reads only; CPU/RAM and aggregate wall time unmeasured.
Some initial aggregate outputs truncated; subsequent narrow reads supplied
the code used in the derivation. No broad suite or compiler source change.

One next action: adjudicate the missing mutation-coverage invariant against an
actual successful restore callback trace on the shared Allowance owner, or
assign its constructive admission-preservation proof. Another static finite
graph with a supplied mutation does not establish the admitted-state domain.

## Frozen dependency hashes and commit packet

The assigned commit/branch are supplied by the primary; this leaf performed
no Git inspection. Inspected direct dependencies:

```text
3fd1c7234c38013343e1c2e72bfed06c4eecdf7173e27d7581e11d6df84f0b3a  crates/yu-solver/src/candidate_extrusion.rs
3b219b51ed8aba6ffc85675fd1d500b901a6f63b31325a85a586d688eee3515a  crates/yu-solver/src/candidate_context.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
582bfb741315534dacf7290bb5618452bb55d9949a8aac691d8d01b93720de11  crates/yu-solver/src/candidate_scheme.rs
2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e  crates/yu-solver/src/candidate_effect.rs
9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1  crates/yu-solver/src/lib.rs
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  notes/design/2026-10-10-contextual-attachment-admission-design.md
6e8a41bc27e0570c916cf49fa4e4a916b6bb6059ad8b0c32627a2d33a0cfbf93  notes/progress/2026-10-10-positive-tail-source-composition-proof.md
3376b6d6b05d90653b91d47a66c5ae522b3b2014bccaca3dfa40e5940cd1d7b2  notes/progress/2026-10-10-source-hir-selective-scc-proof.md
17936a4926135bf04bedb52a2640073227ee17f8f971ba549095b227e56b8e81  notes/progress/2026-10-10-source-hir-selective-scc-witness.md
```

Exact checkpoint path: this note. Baseline: `1a3e694e8`. No dependency edited
by this leaf; primary must compare these hashes to the assigned commit and
checkpoint HEAD. Status: frozen unreviewed research-only obstruction, R OPEN;
no independent review or theorem closure. Verification already run: static
operation/call-site derivation and dependency hashes. No executable artifacts.
Proposed message: `research: isolate restoration product rescue invariant`.
Shared deltas left to primary/curator: retain R OPEN, record the three missing
mutation/diagnostic induction premises and rejected Function-prefix shortcut;
do not record the local schedule as an admitted-state/source counterexample.
`tasks/current.md`, theory maps and design/index changes intentionally remain
primary-owned and were not edited.

Final dependency recheck: all ten listed hashes matched the inspected bytes.
No dependency drift was observed during this assignment. Writes stop at this
handoff; the primary owns any later correction or independent review.
