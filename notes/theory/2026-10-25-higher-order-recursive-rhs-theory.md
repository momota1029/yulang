# Higher-order recursive RHS allocation

Status: candidate constructive mathematics, author checks NOT_RUN; fresh independent
review and primary adjudication pending. No compiler or production authority.
Assignment: HANDLER-RECURSIVE-RHS-THEORY-20261025/r1, lane B.
Author: /root/higher_order_rec_rhs_astra_r1, requested gpt-6-astra/medium;
observed model and effort UNKNOWN. No coauthors or descendants at author freeze.
Baseline: 03eb4b672c29f92c7bed0e2b6e4a1fbb53741c82.
Contract SHA-256: a921540d9539741dcc9dbacb9bd45f0dc086ecb97cdb03dc360dbbda1fd267eb.

## Original parent and application

GVG-REC-RHS-1 is the missing supplier in the immutable graph-extension claim at
docs/yulang-operational-type-safety-ja.tex:980–993, under the recursive-value
source convention and guard requirement at 180–196 and graph interpretation at
258–267. Every RHS derivation in the common recursive environment must produce
a typed closed fresh node by simultaneous substitution. The old graph's
values/types must be preserved, all recursive names must be fresh together,
and the body must use the same substitution.

The earlier restricted graph theorem accepted fresh-node typing as a premise.
It could not represent arbitrary accepted HigherOrder code, types, local binders,
result consumers, adapters or request response binders. This candidate supplies
that missing derivation for the entire accepted HigherOrder grammar.
The theorem source_rec_allocation starts from actual HigherOrder.ValueTyped RHS
derivations, independently typed outer captures, old graph typing/guard, the
actual fresh transparent-cycle criterion and the source body derivation.
It derives all fresh-node typings, allocated graph typing, its guard, and closed
body typing. It takes neither a fresh-node typing oracle nor local numeric ranks.
The finite_source_rec_allocation theorem also computes the old guard from old
finite acyclicity, eliminating numeric ranks entirely.

This applies the substitution lemmas back to the parent allocation step.
The candidate's own elaboration/review remains pending. The full paper parent
retains its original quantifiers and remains OPEN for omitted paper forms,
higher-order eliminator observation and source/native correspondence.

## Exact syntax, types and binders

HigherOrderGraphSyntax.lean defines new mutually inductive Value/Comp/Adapter
sorts parameterized by old graph names R and recursive names S. Constructors
ref r, recvar s and var i distinguish graph references, simultaneous recursive
binders and ordinary de Bruijn locals. Every accepted HigherOrder constructor is
present, recursively including code beneath lambda, delay, bind, unionCase,
scope, expose, request and both adapter positions of wrap.

The existing HigherOrder.Ty is retained exactly, including callable underneath
thunk/union/intersection and operation type arguments. The eight literal payload
domains, mode, all three lambda annotations, receipt, path correspondences,
occurrences, ordered operation type arguments and payload/response types are
retained unchanged. No opaque code label replaces a body. PathCorrespondence
retains its preexisting Prop-valued PathRule metadata; no new typing proof is
placed in syntax.

The new ValueTyped/CompTyped/AdapterTyped judgments use separate assignments
xi:R→Ty, nu:S→Ty and the ordinary local Context. A graph is R→Value R Empty.
WellTyped checks every actual closed higher-order node against xi; it does not
reuse GuardedValueGraph.NodeTyped. Graph guard is a separate conjunct in the
allocation theorem.

The mutual embedValue/Comp/Adapter functions structurally embed all accepted
syntax. Their typing theorems quantify over every original derivation and
arbitrary graph/recursive assignments. Local renaming/substitution and all three
preservation proofs cover every constructor. At a lambda, only its parameter
body lifts; its result consumer belongs to the outer environment. The consumer's
own Adapter.mk body lifts exactly once. Bind/unionCase/request each lift at their
own binder. No metadata is substituted.

## Source convention and actual RHS closing

The sourceContext nu env function represents Γ,x̄:Ā with n recursive names at
indices [0,n), and outer index i at n+i. New ordinary binders push index zero.
The source_recursive_lookup and source_outer_lookup theorems give exact lookup
equations. This is an explicit convention for the paper/accepted research
source calculus; it is not a claim about Rust runtime environment layout.

The splitNames n function maps a recursive-prefix index to recvar and an outer
index to var. The splitValue/Comp/Adapter functions first embed the actual
accepted source tree and then apply the binder-preserving local substitution.
The splitNames_typed theorem proves the lookup supplier from sourceContext;
the three split typing theorems consume it. The split_bound_zero and
split_bound_recursive equations expose behavior under a binder; repeated lifting
covers nested lambda/adapter/request/bind scopes.

The closeNamesValue/Comp/Adapter functions map all old references through Sum.inl
and all recursive names through Sum.inr simultaneously, leaving ordinary locals
alone. Their mutual typing theorem reads unchanged old types and the common
fresh assignment. CapturesTyped xi env capture independently requires each used
outer slot to contain an already closed old-graph value typed under xi.
No capture is typed by assuming a fresh graph reference exists.
The closedCapture function structurally renames these old values; closeValue,
closeComp and closeAdapter substitute them into the remaining local slots.
Their closing theorems derive closed-node/body/adapter typing.

The sourceCloseValue_typed and sourceCloseComp_typed theorems compose these
concrete operations starting at the source derivation. The sourceFresh function
uses the same construction for every RHS, with all names available together.
The named_rec_allocation theorem additionally handles explicit-name RHS syntax,
including old graph references directly in code; it supplements the actual
source-prefix supplier rather than replacing it.

## Immutable graph and exact finite guard projection

Allocation's domain is Sum R (Fin n). Old nodes are structurally renamed through
Sum.inl; fresh node s is stored at Sum.inr s. The allocation_old_node equation
preserves the entire old value/code/metadata under that renaming;
allocation_old_type preserves its exact type. The fresh_no_collision and
fresh_names_distinct theorems prove actual disjointness and fresh-name
injectivity. The old_no_fresh_edge theorem excludes old-to-fresh transparent
edges. The structural map also traverses references beneath old code/adapters.

The frontier function follows only the immediate transparent inspection chain.
References produce its successor. Both/top evidence, views and callable adapter
wrappers continue through their underlying value; none turns an alias cycle
into genuine data/lambda/delay. Literals, injections, lambda and delay terminate
inspection. References inside their fields/code remain represented and may form
guarded cycles. Free local heads are excluded by closed graph typing.

The nextValue function removes the impossible Empty recursive name.
The projectNode function maps an actual successor to GuardedValueGraph.Node.alias
and no successor to terminal token Node.unit. That unit is only an untyped guard
token: it is neither an encoding of the higher-order value nor a higher-order
type/canonical form.

The frontier_closeNames theorem connects real name constructors to successors.
The projectNode_next and projection_edge equations equate every projected
transparent edge with nextValue; fresh_edge gives exact fresh-internal edge
equivalence. The projectNode_map and project_allocation equations prove that
projection commutes with actual structural old-node renaming and allocation.

The allocationGuard definition invokes the accepted finite decision through
this equation. Local ranks are computed from FreshNoCycle; fresh-to-old edges
are permitted. The allocation_guard_iff theorem also proves necessity under the
old certificate, so the criterion is not a stronger sufficient restriction.
No restricted NodeTyped, transparent_type, reference_canonical or
no_bottom_reference theorem is applied to higher-order nodes.

## Distinguishing constructions

- The mutualRhs example consists of two actual computation-entry source lambdas.
  Each calls the opposite recursive name using its original delayed argument.
  Both read the same outer capture in body and designated result consumer.
  The mutualRhs_typed theorem proves source typing; mutualFresh_equation exposes
  allocated code, fresh targets, shared old reference and both local binders.
  The mutual_allocation theorem applies the general source theorem.
- The responseRhs example is delayed request code whose continuation reads its
  recursive node and returns the original higher-order response through a local
  bind. The response_closed equation retains operation metadata, closes payload
  capture to an old reference and recursion to a fresh reference, and retains
  response index one under that bind. Typing is derived from the source RHS.
- The oldAliasRhs example is an outer capture reference. Its allocation theorem
  admits the fresh-to-old transparent edge without an assumed local rank.
- The aliasRhs example is source x=x, typable at an arbitrary type. Its actual
  closing is a fresh self-alias; alias_cycle_rejected and
  alias_allocation_unguarded reject its guard.

These are candidate theorem instances, not executed checks or native traces.

## Source/native evidence and unchanged owners

Read-only source inspection supplies a boundary, not correspondence:

- runtime/program.rs, RuntimeProgram::from_hir_with_roots, ownership walk at
  605–646 and LocalBinding construction at 748–764, detects selected local self
  references on the lexical initializer stack and stores a recursive flag.
- runtime/machine.rs, Machine::begin_local at 2500–2545, allocates a None cell,
  extends the environment before evaluation for recursive locals, and schedules
  the initializer. Frame::Local at 1498–1560 publishes its resulting value.
- Instruction::Name at 839–861 detects recursively demanded globals or rejects
  an uninitialized local. Machine::lookup at 2585 onward traverses binder cells;
  initializer_environment preserves/extends dispatch state.

These producers/consumers are not the immutable simultaneous constructor proved
here. Their sequential initialization, mutable current-value cells, error states,
binder identities and owner/dispatch behavior need an ENV-GRAPH-1 realization
relation. A source prefix index theorem does not establish that relation.
NO_SAFE_CODE_SLICE: this theory-only packet authorizes no runtime change; the
inspected producer/consumer owners have no production write lease.

No Simple-sub generation, accumulation, propagation, levels, extrusion,
qualifying intrusion or generalization is changed. No withdrawn bypass is
restored. F1/FK1, foreign-continuation, provider, residual and witness quantifiers
remain independent of this allocation result.

## Reuse, remaining premises and mutual TODOs

The accepted HigherOrder substitution proof pattern is adapted with explicit new
graph/recursive leaf cases, not assumed for extended syntax. FiniteGuardDecision
is reused exactly for its guard domain. Its accepted finite completeness result
supersedes the older graph note's historical open rank-synthesis premise.
Restricted Term/Node typing and canonical proofs are rejected as suppliers for
arbitrary HigherOrder code/types.

B-CHECK-1, primary: elaborate the frozen modules, inspect theorem signatures and
transitive axioms, then appoint a fresh nonauthor reviewer. Falsifier: a missing
accepted constructor, wrong lift, remaining fresh-node/rank oracle, forbidden
axiom or elaboration failure.

B-OBSERVE-1, next graph proof allocation: supply eliminator-directed higher-order
observation retaining wrapper/evidence context. Both/top and wrap can change the
type of an underlying transparent value; identical-type transport through the
guard projection is invalid. Falsifier: a well-typed guarded node whose claimed
canonical form loses union/intersection/top/callable evidence. OPEN.

B-PAPER-1, full-paper syntax/theory allocation: supply actual μ types and
type-changing roll/unroll/evidence, polymorphism and other omitted paper forms.
Falsifier: an accepted paper RHS without a structural typing-preserving
translation, or type-changing evidence mishandled as identity. Original paper
quantifiers remain intact.

B-NATIVE-1 / ENV-GRAPH-1, Luna/source intake: define readback/lifecycle invariants
for the inspected from_hir_with_roots, begin_local, Frame::Local, Instruction::Name
and lookup paths. A future minimal provisional instrument could record allocated
cell/binder identity, publication and the environment captured by an RHS,
retaining uninitialized reads explicitly. Falsifier: capture reads an
uninitialized/currently different cell, sequential initialization is falsely
treated as simultaneous, or a shared native value receives inconsistent types.
This is a proposed evidence TODO, not permission to edit/run the runtime.

## Freeze and resources

All 96 frozen contract dependency pins were read-only SHA-256 compared and
matched. Direct dependencies include:

- HigherOrderSyntax: ea727d33692bdcbe6b40245b960d01225b556b5334ffab649eea2699930d5972
- HigherOrderSubstitution: 19910452c45b20761ec06dc7e15f94c94b95014ff00f3f5296af005b9adf6f30
- GuardedValueGraph: 4d2c3b17d0ab8d12606c875638426167ce596492167cecf042eb222436229f55
- FiniteGuardDecision: a9924ab2c8d96a173c886ddfbb2580a7719fbf08064d9f85d0644784778de9fa
- Paper: a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b
- machine.rs: b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e
- program.rs: 6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907

Author Lean/build/tests/checkers/axiom inspection: NOT_RUN, as required.
Hash comparison and manual source/proof inspection are not independent review.
Intended new axiom closure is a subset of propext/Quot.sound; no sorry, new axiom,
Classical.choice or native_decide is introduced. Primary owns actual checking
and independent review.

Only the two leased Lean files, this note and the assigned inbox were created.
No scratch paths, other-worker writes, compiler/config changes, Git, network,
descendants or background processes. Fixed grant: 1200 seconds from actual
acknowledgement; conservative lower bound 07:07:26.019051 UTC.
The inbox records author freeze time, artifact hashes and STOP.

## Primary coauthorship and candidate freeze

Primary acknowledged the author's actual STOP and took over the two source files
and this note at 07:16:30.933241 UTC. Primary coauthorship repairs: ordinary comment
before mutual; explicit closeNamesValue unfolding for the reference cases;
modern dependent-if equations and explicit sourceContext/splitNames unfolding
in splitNames_typed. These preserve all constructors and theorem premises.
The author inbox remains byte-frozen at its original handoff hashes.

Primary has elaborated both modules and queried every named public declaration.
The combined query covers 273 module declarations plus eight primary query
constructions, with eight additional anonymous boundary examples. All successful
query results have transitive axiom closure contained in {propext, Quot.sound}.
The query exercises empty value-arm failure, concrete instance inequality, nested
response restoration, ordered trials, double binder lifting, transparent wrapper
cycle rejection, guarded constructors and alias-cycle rejection. Earlier failed
elaboration/query receipts remain preserved. Final source/note-bound rebuild and
fresh nonauthor review are required before acceptance; their exact receipts and
adjudication belong to the sprint outcome.

Current module SHA-256:

- `HigherOrderGraphSyntax.lean`: `2dca03ee408f7f35545c02847d03fae47ab1887c2761c82e8b59cc9ad6001886`
- `HigherOrderRecAllocation.lean`: `30a6e1855fb8bb4950ad2bdfad238e000554563cb0d1d4b1ec311e3c0cf4f0dd`

The two new grammar extensions separately embed the accepted higher-order core.
Their combined handler/graph language is not proved by either independent lane
(HO-HANDLER-GRAPH-COMPOSITION-1 remains OPEN). Original full-paper and native
correspondence parents remain OPEN.
