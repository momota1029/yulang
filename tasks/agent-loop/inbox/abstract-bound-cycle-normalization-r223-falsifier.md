# R223 independent falsification — revision 1, frozen

Assignment: `R223-BOUND-CYCLE-FALSIFIER`; worker
`/root/r223_bound_cycle_falsifier`; session `R222`. The primary's compact
record uses the alias `/root/r223_falsifier`; runtime NEW_TASK identifies this
worker. Sole author, no descendants. Requested/effective model and effort are
UNKNOWN here. Exact lease and only changed path: this report.

Baseline: `b6e886c3b74b820eef7c996f8026d551f01b6f47`; observed integration HEAD
`4e3b42f9c921cfd1b1d195ba8c7100a2c11c6b51`. Frozen inputs rehashed:

| Input | SHA-256 |
| --- | --- |
| R223 contract revision 3 | `df9393be7ea3432ca8cf28af13610fdded5430b20b6fdf0f49668e2b83edf980` |
| R223 Lean revision 2 | `65335f3b8c6834e1e1cd34429a8fd7330162648a62d532c3a45f44305b255aee` |
| R223 proof handoff revision 2 | `82a30aaea95f67830f8459932c8240064831cacaba94d17188d192d27f4abcc0` |
| AbstractSimpleSubCore.lean | `023635d283f9a00e906ec965a6eaa5595eab21f2b93f353a1d5ea0ede0bffb6c` |
| BirthLevelSCC.lean | `2c76b82d4dc85a4bf4c122731ba014b07df4c863ad679e9a795a57e6546243f0` |
| SimpleSubConstraintSyntax.lean | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| SimpleSubGeneralizationSoundness.lean | `3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246` |
| SimpleSubScopedPublication.lean | `d64e9bffca5d513985237a9ff78dcf3d9e43baae1594edbc93dff4b5410d428f` |
| Contracts.lean | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |

Objective/method: independently inspect the existing definitions and derive
small countermodels to tempting stronger claims. This report does not construct
or independently kernel-check a Lean theorem. Governing sources read: root
AGENTS and pre-sprint proof-closure/authority clauses; research-lab and its
preserved rules; design-authority; git-concurrency; goal-driven-sprints; R223
required theorem contract and stop boundary; top-level inference principles;
actual pinned Term/Sub, CoreState, generalization and owner-local Published
definitions. No language interpretation is changed.

## Result and surviving mathematical scope

No counterexample was found to the strict statements of the submitted SCC,
solution-transport or all-Term structural theorems. The independent derivation
is as follows:

1. Each graph edge is one complete same-kind variable/variable clause, so a
   store solution supplies Sub along every edge and its transitive paths.
   Mutual reach therefore supplies both Sub directions. Finite closure's
   intermediate scope is explicit; exact ordinary SCC equivalence additionally
   requires StoreBounded n store and in-scope endpoints. With n=1 and the
   out-of-scope two-cycle 0↔1, global SCC equality would fail, as expected;
   the theorem does not assert it without those premises.
2. The minimum is a variable coordinate in the same finite connected class,
   not a choice of a distinguished semantic type. Later coordinates remain
   fixed. Idempotence and the exact-SCC theorem have appropriate scope.
3. Every removed clause is syntactically var r <: var r, satisfied by Sub.refl
   under every valuation. Every other clause is mapped in list order, including
   duplicates and structural self-bounds. Pullback is the actual substitution
   composition, not an assumed solver-success law.
4. For an original solution ρ, mutually Sub values on SCC members transport
   through every Term constructor. Function uses the reverse direction at
   argument and argument-effect ports and the forward direction at result
   effect and result ports. Record labels/optional bits, tuple order and variant
   tags/payloads are unchanged. σ=ρ is a constructive normalized valuation.
   No bound on client t or substitution values is needed for this statement.
5. physicalRows visits both sides of every physical row; representative lookup
   is one step, not an established canonicalization history. Class-level bounds
   are valid for the explicit padded numeric scope; an exact fiber minimum
   requires the stated in-scope/fixed premise. Arbitrary CoreState records do
   not establish valid/idempotent representatives or actual allocation/capture
   coherence. The module labels those native bridges open. Numeric anchor
   transport is not a theorem about nonGeneric capture.

The all-Term result above has the premise that ρ solves the complete original
store. It does not assert unrestricted freshened all-Term factorization from
owner-local Published satisfaction. That distinction is essential below.

## Checked fixture: owner locality is material

The submitted stopped-layout witness is correctly minimized to two rows and
one use. Let x=0 have level 0 and upper [y], and y=1 have level 1 and upper [x].
For boundary 0 and root y, capture stops x and copies y. With n=2/use=0, the
published clauses are exactly x<:y, y<:x and copy(y)=3<:x. Additional uses repeat
the last form. Setting ρ(x)=ρ(y)=a∪b and ρ(3)=a satisfies these clauses.
After quotienting x,y to captured class 0, queries t=x and t=y would require
one σ(0) equivalent to both a∪b and a. That implies Sub(a∪b,a), refuted by
the submitted Boolean observation with observesOne(a)=false,
observesOne(b)=true. Each Sub constructor preserves this observation; the
constant-false observation on structural constructors is legitimate for this
countermodel. This is not an interpretation of free variables as rigid atoms.

The low owner's high dependency violates BoundLevelsClosed. Thus the witness
does not refute an accepted source state. In the submitted closed layout both
directions are owned by y, as lower [x] and upper [x]; x stores nothing. Exactly
the same extracted clauses/quotient/levels now publish both copy(y)<:x and
x<:copy(y). The actual Published constructors supply the two directions needed
for each use's equivalence. The submitted closed-layout factorization theorem
is a concrete valid discriminator, not a universal publication result.

## New discriminator A: numeric closure alone still fails

This is an explicit model derivation, not a new checked Lean declaration.
Use the same owners x.upper=[y], y.upper=[x], n=2, boundary 0, root y and one
use 0, but set levels(x)=levels(y)=1 and nonGeneric(x)=true,
nonGeneric(y)=false. All other rows are absent; representatives are identity.
After merging the SCC, use class level 1 and nonGeneric(class 0)=true, the
ordinary OR of its two members.

BoundLevelsClosed holds: both dependencies require only 1≤1. Before capture,
captureGuard is false at x and true at y. After capture it is false at class 0.
Use allocation equal to those respective capture flags. The published clauses
are therefore exactly the stopped-layout clauses above. The same valuation
ρ(x)=ρ(y)=a∪b, ρ(3)=a satisfies Published. For all-Term factorization t=x and
t=y again force σ(0) equivalent to a∪b and a, an impossibility.

NonGenericClosed fails at owner x: its nonGeneric flag is true but dependency
y's flag is false. StoppedClosed consequently fails too. This independently
extends the existing numeric_closure_does_not_imply_guard_closure warning to
the exact joint-factorization conclusion. It refutes the proposed universal
implication "BoundLevelsClosed plus SCC/minimum/OR metadata suffices". It
does not refute the submitted closed-layout theorem, whose nonGeneric flags
are all false. It is not a source-qualified counterexample: no actual lawful
capture/publication history with these flags has been established.

## New discriminator B: unrestricted freshened clients need coverage

Even both closure properties do not supply a universal freshened all-Term
theorem when publication cannot reach the queried SCC. The smallest model uses
two rows x=0,y=1, equal level 1, all nonGeneric flags false, upper bounds [y]
and [x], boundary 0, n=2, use list [0], and roots=[]. Both closure properties
hold. Published contains the two base clauses and no copy clause: Reach has
no root, so no row is reached. q(0)=q(1)=0, class level is 1, and both old and
new class guards are active. Old fresh indices are 2 and 3; the new class's
fresh index is 2.

Set ρ(x)=ρ(y)=a∪b, ρ(2)=a, ρ(3)=b, with a=atom 0 and b=atom 1. This is one
valuation solving every Published clause. It refutes this exact stronger shape:

```text
PublishedSatisfied(before, ρ) →
  ∃σ, ∀k (t : Term k),
    Equivalent ((rename freshBefore t).subst ρ)
      ((rename freshAfter (rename q t)).subst σ).
```

At t=x and t=y the right sides are both σ(value,2), while the left sides are
a and b. Their two equivalences imply Sub(b,a), contradicted by the same
Boolean observation. Allowing arbitrary σ cannot repair this failure. A
single use already suffices; additional uses do not help.

If a nonempty root list is desired, add an isolated row z=0 and shift the SCC
to x=1,y=2 with n=3, roots=[z], all levels 1, no bounds at z. The SCC is still
unreached. Its old fresh indices are 4 and 5, and its shared new fresh index
is 4. The same contradiction applies. This variant is also only a model:
no accepted source/client publication has been established.

Therefore the next generic publication theorem needs evidence that every
queried fresh SCC class has sufficient published constraints, or a source-
justified query/reachability condition. Such a condition must come from the
actual consumer, not an ad hoc narrowing of Yulang's parent scope. Ownership,
capture closure, and query coverage are distinct obligations. BoundLevelsClosed
and NonGenericClosed can supply StoppedClosed, but do not alone supply root
reachability or a solution relation for arbitrary unqueried copies.

## Guarded-readout boundary

Variable/variable SCC normalization does not eliminate arbitrary unguarded
lattice recursion. A single allocated level-0 row with upper
union(var 0,atom 0) has no variable/variable edge, q(0)=0, and that structural
bound survives normalization. The corresponding one-demand R212 problem
passes term allocation; insertPendingUpper's level check also passes because
the only dependency is its same level-0 owner. This is a derivation from the
actual partial operation, not a checked complete accepted run.

Literal unifying negative coalescing retains the shape μn.(Top ∩ (n ∪ atom 0));
a direct lattice graph has a cycle through intersection/union nodes. The SCC
packet provides no simplification/recursive-syntax theorem making it Guarded.
This agrees with its explicit remaining Fig.12/readout bridge. No original
guarded-readout or parent soundness/principality/termination gate is closed.

## Evidence, limits and handoff

Read/hash/source inspections only: cat/sed/rg, sha256sum, read-only
git rev-parse/status, date. The targeted forbidden-token scan returned no
matches. No build, checker, tests, executable model/search, random seeds,
cache, scratch, extra files, descendants or Git mutations. No CPU/RSS claim;
lightweight sequential shell reads and this one report write, within 900s.
The new witnesses above are mathematical derivations with explicit predicates;
they are not executable or kernel receipts. There is no sampled search range
or omitted shard to report.

Oracle independence: the countermodels are grounded in the preexisting
Published/fresh/captureGuard/Sub definitions, not an oracle that assumes the
new normalization theorem. They necessarily share those pinned definitions;
they do not validate source generation, solver histories or compiler behavior.
The failure conditions are precisely missing NonGeneric closure or missing
query coverage, respectively. No third equivalent toy probe is proposed.

The primary reports the final target build and complete 65-declaration axiom
audit passed. This worker did not rerun or independently observe those
executions. The handoff preserves the earlier failed revision-1 build, including
the rejected elaborator sorryAx diagnostic, truncated diagnostics, the initial
memory-limit abort and subsequent repair. Those remain historical failure
evidence; final-source inspection does not erase them or certify that rejected
environment. Fresh referee review remains pending.

Recommended next action: at the actual publication owner, establish the
combined bound-level/nonGeneric/capture/representative invariants and the
consumer's query-coverage relation, then prove generic joint factorization or
produce a source-qualified counterexample. Preserve both new witnesses as
discriminators. Parent application remains none: roots 0/4, packages 0/5,
parent delta 0. Only the primary updates shared records or admits that packet.

Commit packet: exact path
`tasks/agent-loop/inbox/abstract-bound-cycle-normalization-r223-falsifier.md`;
baseline `b6e886c3b74b820eef7c996f8026d551f01b6f47`; no dependency bytes changed;
claim class bounded independent falsification/model derivations; fresh referee
review pending; checks limited to source inspection, exact hashes and token
scan; proposed message `research: record R223 capture and query-coverage falsifiers`.
Shared deltas intentionally left to Luna: actual runtime identity/alias,
frozen report hash, R223-OWNER-LEVEL-CAPTURE expanded to explicit nonGeneric
and query-coverage premises, unchanged parent status, review/integration state.

**WRITES_STOPPED** at submission. No outstanding writes or descendants.
