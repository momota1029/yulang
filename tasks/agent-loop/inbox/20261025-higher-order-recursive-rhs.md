# Frozen assignment handoff: HIGHER-ORDER-REC-RHS / revision 1

Sprint: HANDLER-RECURSIVE-RHS-THEORY-20261025/r1.
Contract: tasks/agent-loop/sprints/handler-recursive-rhs-theory-20261025-r1.md
Contract SHA-256: a921540d9539741dcc9dbacb9bd45f0dc086ecb97cdb03dc360dbbda1fd267eb.
Assignment ID: HIGHER-ORDER-REC-RHS-20261025-B; handoff revision: 1.
Baseline: 03eb4b672c29f92c7bed0e2b6e4a1fbb53741c82.
Outcome class: candidate constructive mathematics, pending primary checks and
fresh independent review. No reviewed-theorem, compiler or production promotion.

## Runtime and authorship

Actual worker: /root/higher_order_rec_rhs_astra_r1, lane B leaf author.
Requested model/effort: gpt-6-astra / medium.
Observed model/effort: UNKNOWN / UNKNOWN.
Session: HANDLER-RECURSIVE-RHS-THEORY-20261025/root-r1.
Primary launch acknowledgement precedes 07:08:14.918560 UTC;
conservative authorization lower bound 07:07:26.019051 UTC.
All authors at this freeze: this worker only. No descendants, coauthors,
nested CLI, external contact or background processes.

Freeze and writer STOP: 2026-10-25T07:16:03.091297+00:00.
Fixed grant: 1200 wall seconds, no extension or reset.
Elapsed lies between 468.173 and 517.072 seconds using the supplied
acknowledgement interval. Conservative remaining grant: 682.928 seconds;
this STOP does not authorize further author work or automatic budget reuse.

## Parent application and exact result

Original parent GVG-REC-RHS-1; paper180–196,258–267,980–993.
Two new modules construct the full accepted HigherOrder Value/Comp/Adapter
grammar with separate graph references, recursive names and ordinary locals.
All accepted constructors, types, metadata and code binders are retained.
Structural embedding and mutual renaming/substitution typing proofs are supplied.

The sourceContext convention places all n recursive names at [0,n), with outer
Γ shifted by n. Typed prefix splitting preserves each ordinary binder, including
the lambda consumer's outer scope, adapter input and request response.
Simultaneous name closing maps all recursion names to fresh Sum.inr references.
Outer captures are independently typed closed values under the OLD graph and
are substituted separately. The sourceCloseValue_typed supplier derives each
fresh node's typing from an actual HigherOrder source RHS derivation.

The source_rec_allocation theorem applies those suppliers to immutable
simultaneous allocation and the actual closed body. No fresh-node typing or
local rank remains an independent input. The finite_source_rec_allocation
variant also derives the old rank from finite old acyclicity.
The named_rec_allocation variant handles already explicit source names and old
graph references, without replacing the source-prefix theorem.

The new graph WellTyped judgment types actual higher-order values.
The exact projectNode_next, projection_edge, fresh_edge, projectNode_map and
project_allocation equations connect all transparent edges to the accepted
FiniteGuardDecision construction. Its unit terminal token carries no value
encoding or typing claim. AllocationGuard computes local ranks from FreshNoCycle;
allocation_guard_iff proves the criterion necessary under the old guard.
Old values/code/metadata and types are preserved by structural Sum.inl renaming;
fresh names are injective/disjoint. Old-to-fresh transparent edges are impossible.

Concrete candidate instances cover actual mutual recursive lambda calls, shared
old captures in bodies and consumers, preserved request response binders,
fresh-to-old alias acceptance and actual source-typed self-alias rejection.

## Evidence boundaries and reuse

Accepted HigherOrder substitution proof structure is adapted with new ref/recvar
cases. Accepted FiniteGuardDecision is reused only for guard certification.
Restricted GuardedValueGraph Term/Ty/NodeTyped/canonical proofs are not used to
type arbitrary higher-order code. The historical open finite-rank premise is
superseded by the accepted finite decision, not revived.

Read-only native audit: RuntimeProgram::from_hir_with_roots owns the recursive
flag from its source ownership walk and LocalBinding construction; Machine::
begin_local allocates a None cell and schedules initialization; Frame::Local
publishes; Instruction::Name/lookup read or reject uninitialized cells.
This sequential mutable lifecycle is not the immutable simultaneous construction.
No native layout, initialization, readback or execution correspondence follows.
Source generation/constraints/propagation/intrusion/generalization and F1/FK1,
provider/residual/witness/foreign-continuation obligations remain unchanged.

Higher-order canonical observation remains OPEN: both/top/wrap can change the
underlying value's type and require eliminator-directed evidence, so the untyped
projection cannot supply canonical typing. Actual μ/roll/unroll, type-changing
evidence, polymorphism and other omitted paper forms remain OPEN under the
original quantifiers. Full paper/native parents are not declared closed.

## Frozen artifacts and dependencies

- notes/theory/lean/YulangClosure/HigherOrderGraphSyntax.lean
  SHA-256 1f9c2a39a255c7947827d59fa6e1e7142080ba6ceeb791dac7451e117baeb09e
- notes/theory/lean/YulangClosure/HigherOrderRecAllocation.lean
  SHA-256 2d2ac09220e74093d4871f7bb4fc329226413c0eaf561f4dedcc14f38e649b99
- notes/theory/2026-10-25-higher-order-recursive-rhs-theory.md
  SHA-256 f78d328082f77f11d5f85a588fc3a9174240cc8150434f05fe577eb6783aba4f

This handoff is the fourth and only other new path:
tasks/agent-loop/inbox/20261025-higher-order-recursive-rhs.md.
Its own SHA-256 is returned separately to avoid a circular self-hash.
No scratch paths or other writes.

All 96 pinned contract dependencies matched read-only SHA-256 comparison.
Direct dependency hashes and inspected source owners are listed in the note;
the immutable contract contains the complete pin inventory. No imports from the
other new lane and no dependency enlargement.

## Checks, next step and mutual TODOs

Lean/build/tests/checkers/axiom inspection: NOT_RUN by author, as required.
Manual proof/source inspection and read-only hashing are not independent review.
Intended strict axiom closure: subset of propext/Quot.sound; no admitted proof,
new axiom, Classical.choice or native_decide. Primary must verify the candidate.

B-CHECK-1 — primary: elaborate the two modules, inspect source_rec_allocation,
finite_source_rec_allocation, embedding/substitution signatures and axiom closure;
then obtain fresh nonauthor review. Falsifier: failed elaboration, omitted
constructor, capture, forbidden axiom, or hidden fresh-node/rank premise.
B-OBSERVE-1 — next graph proof allocation: eliminator-directed higher-order
observation preserving wrapper evidence. Falsifier: canonical form loses required
type-changing wrapper evidence.
B-PAPER-1 — full-paper theory owner: actual μ/type-changing evidence and omitted
forms. Falsifier: a paper RHS has no structural typing-preserving translation.
B-NATIVE-1 / ENV-GRAPH-1 — Luna/source intake: exact cell/binder/publication/
capture realization through the named native owners. Minimal future provisional
instrument could record those identities and uninitialized states. Falsifier:
wrong/currently changed cell read, sequential-to-simultaneous mismatch or
inconsistent typing of a shared value. NO_SAFE_CODE_SLICE in this packet.

Writer state: STOPPED. All four leased paths are frozen at this revision.
No descendants/processes or unresolved descendant leases. No Git.
Next action belongs to primary checking/review intake; no running worker is
claimed while waiting. Author cannot independently certify this result.
