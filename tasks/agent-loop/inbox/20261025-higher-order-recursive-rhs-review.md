# Independent recursive RHS review — revision 1

Verdict: CLEAN for fixed outcome B of HANDLER-RECURSIVE-RHS-THEORY-20261025/r1.
No blocking defect found in the frozen accepted-HigherOrder source allocation
theorem, its substitution suppliers, immutable extension or guard projection.
This is independent review of that exact research scope, not full-paper,
operational canonical-observation, native correspondence or production closure.

Reviewer: /root/higher_order_rec_rhs_review_astra_r1.
Session: HANDLER-RECURSIVE-RHS-THEORY-20261025/root-r1.
Requested model/effort: gpt-6-astra / medium. Observed: UNKNOWN / UNKNOWN.
Actual acknowledgement: 2026-10-25 07:22:29 UTC.
Grant: 450 seconds; conservative predispatch interval starts 07:22:02 UTC and
ends 07:29:32 UTC. Sole write lease is this report. No descendants or coauthors.
Baseline: 03eb4b672c29f92c7bed0e2b6e4a1fbb53741c82.
Contract SHA-256: a921540d9539741dcc9dbacb9bd45f0dc086ecb97cdb03dc360dbbda1fd267eb.

## Frozen target and authorship

- HigherOrderGraphSyntax.lean: 2dca03ee408f7f35545c02847d03fae47ab1887c2761c82e8b59cc9ad6001886
- HigherOrderRecAllocation.lean: 30a6e1855fb8bb4950ad2bdfad238e000554563cb0d1d4b1ec311e3c0cf4f0dd
- notes/theory/2026-10-25-higher-order-recursive-rhs-theory.md: 08020fdf17139162ba49ece7336967b7f6b757ef0cff35201a1deeb5970866fc
- Original author inbox: 282c3bd3d2e00826c9c4cf1202e7b8bdc45afe8f65b0a2da17eb0e65c04eedf5
- Combined verification JSONL: 56bc0c6ce4478b23a22010601a13e32e3a03025c9a17b28bd74b7a291ed77c58
- Primary query: 683a5d5c27b7fcd3024f47fc0b6f542e940c6ef6b7c6dcda0e50aeb4feece45a
- Primary runner: 65abbae372131b10fe1b336b682e5864564aaf4b67f4a36379c2d8f3858a83ad

All target hashes match. All 96 contract dependency pins match. Original author
/root/higher_order_rec_rhs_astra_r1 stopped before primary takeover. Primary is
a coauthor of the recorded mechanical elaboration repairs; this reviewer is
independent of both authors and edited none of the reviewed artifacts. The
original author's older hashes remain an explicitly historical freeze.

## Proof and scope audit

Compared every Value/Comp/Adapter constructor and typing rule with frozen
HigherOrderSyntax.lean. The new grammar preserves all accepted types, literal
payloads, lambda mode/receipt/annotations, operation instance data, paths and
view metadata. Graph references, recursive names and ordinary locals occupy
separate namespaces. Structural embedding retains actual nested bodies and
adapters, with typing proved for every original derivation.

Manually traced mutual renaming, substitution and name closing. Lambda body
lifting preserves its parameter, while its result consumer stays in the outer
scope and introduces its own Adapter.mk input binder. Bind, union branches and
request continuation lift at their respective binders. Reference/name closing
does not shift ordinary locals. This covers repeated and mixed binders, rather
than only the worked examples.

HigherOrderRecAllocation.lean:21–80 supplies the real prefix convention:
recursive indices below n become recvar; outer index n+i becomes local i.
splitNames_typed derives this from sourceContext lookup. At lines 84–157,
CapturesTyped requires independently typed closed OLD-graph captures. These
cannot mention fresh names. closeNames maps all recursive names to Sum.inr
simultaneously; capture substitution subsequently closes the outer environment.

The decisive source_rec_allocation at line 313 starts with actual original
HigherOrder.ValueTyped RHS derivations in that common recursive environment.
It derives hf via sourceCloseValue_typed, then applies allocate_typed. Thus the
helper's fresh-node premise is genuinely discharged in the final theorem, not
renamed or assumed. The body uses the same closing operation. The named form
also permits existing graph references directly. The finite variant derives the
old guard from finite acyclicity. No fresh typing or numeric rank oracle remains.

Allocation keeps every old node structurally renamed through Sum.inl and every
old type unchanged; Sum.inr names are disjoint and injective. closeNames traverses
old code and adapters too, so no hidden fresh reference is introduced beneath
an old constructor. WellTyped checks the actual higher-order values under the
joint assignment, independently of the guard.

The frontier at line 169 follows references through both/top/view/wrap and stops
at actual literals, injections, lambda or delay. projectNode_next and
projection_edge identify exactly its successor; frontier_closeNames,
projectNode_map and project_allocation connect this to actual renaming and
allocation. fresh_edge identifies only fresh-internal edges. The reused finite
construction computes ranks from FreshNoCycle, and its freshGraph deliberately
treats old targets as local endpoints. allocation_guard_iff also proves the
criterion necessary given the old certificate. Old-to-fresh edges cannot arise.
No restricted NodeTyped or canonical theorem is used for higher-order values.

The source mutual-lambda examples genuinely call the opposite recursive name,
share an old capture in body and consumer, and preserve the delayed parameter
under a second binder. The request example preserves its higher-order response
under a local bind while closing payload and recursive references correctly.
The old alias example admits a fresh-to-old edge. Source x=x is typed at any
type but rejected by the guard. The query additionally rejects a wrapper-only
self-cycle and checks double lifting and constructor barriers.

## Receipt audit, without rerunning checks

Read the runner, frozen query and preserved JSONL. There are 17 calls totaling
25.46509404799508 seconds. Failed/intermediate rows remain present. Final rows
13–17 record success, no timeout and no warnings; their input hashes before and
after agree and all recorded final input/output hashes match current bytes.
Final graph module and query source_text fields match the actual frozen source.
The 46 reused module chains from the pinned prior receipts have successful last
rows and matching current input/output hashes; excluded historical failures are
not silently relabeled successful.

The final query contains 281 matching #check/#print-axioms pairs (273 module
declarations plus eight query declarations), eight anonymous examples, and 281
corresponding axiom results. Their union is exactly {propext, Quot.sound}.
All 36 named declarations in GraphSyntax and 93 in RecAllocation appear in the
query. No missing target or additional axiom was found. These are inspections of
primary-produced evidence, not a new reviewer Lean run or self-certification.

Reviewer Lean/build/tests/checkers/Git: NOT_RUN. Read-only source, receipt and
SHA-256 inspection only. An initial read-only inspection command used unavailable
python and exited 127; it was repeated with python3. No Lean command was launched.

## Original parent application and remaining obligations

Inspected paper lines 180–196, 258–267 and 980–993. The candidate supplies the
missing simultaneous RHS-to-node typing construction for all accepted
HigherOrder forms, preserving the original full-paper GVG-REC-RHS-1 quantifiers
as OPEN outside that explicit subdomain. Guard token unit carries no claim that
the actual higher-order value is unit.

B-OBSERVE-1 remains OPEN: both/top/wrap may change the underlying value's type,
so canonical observation must retain evidence and adapter context. A future
eliminator-directed observation theorem is still required. B-PAPER-1 /
GVG-FORMS-1 remain OPEN for actual mu, type-changing roll/unroll, polymorphism
and omitted paper forms. HO-HANDLER-GRAPH-COMPOSITION-1 remains OPEN: these
independent extensions do not establish a combined language theorem.

Inspected actual RuntimeProgram::from_hir_with_roots ownership walk and
LocalBinding construction; Machine::begin_local; Frame::Local publication;
Instruction::Name uninitialized reads; lookup and initializer_environment.
The native code creates None cells and initializes/publishes sequentially with
binder and dispatch state. It is not the immutable simultaneous allocator.
B-NATIVE-1 / ENV-GRAPH-1 remain with primary source/proof intake for the actual
cell/capture/publication realization relation. No source generation, inference
constraint, propagation, intrusion, generalization, native current-value or
production consequence follows. NO_SAFE_CODE_SLICE under this review lease.

## Freeze and STOP

Review complete; no requested repairs. Primary owns acceptance and integration.
Report freeze and writer STOP: 2026-10-25T07:24:04.890811+00:00.
Elapsed 95.891 seconds from actual acknowledgement; conservative elapsed 122.891 seconds
from predispatch bound, within 450 seconds. No background processes, active
commands, descendants or unresolved descendant leases remain. No source edits,
scratch files, Git, native runs or external contact. Only this report was written.
Report SHA-256 is returned separately to avoid circular self-hashing.
