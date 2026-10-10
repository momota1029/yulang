# FunctionPort incidence as a lifecycle mutation

Status: frozen unreviewed source characterization and conditional derivation.
No implementation, certificate validity, ordinary-source reachability, or
lifecycle-gate closure is claimed.

Baseline: `c9e5b295c82ec9ac2263c71fb087f175b4d29afd` on
`research/simple-sub-intrusion`. Governing authority is
`notes/design/2026-10-10-contextual-attachment-admission-design.md` §§4–6.
The prior current-component inventory remains useful for the missing lifecycle
owners, but its earlier statement that all nonidentity Swap contexts are
unexecutable is stale: current `candidate_zero_word_filters` executes
payload-free Swap/WithoutLeftFilter fragments; payload-bearing nested filters
remain unavailable.

## Conditional source bridge

Let `p` and `c` be existing identity-context relations, let the exact
FunctionPort dependency `(p,c,Argument,Swap)` be absent, and assume a
successful admission with no intervening merge. `candidate_function_port_admit`
(`candidate_context.rs:1681–1736`) selects Swap but elides structural
`Swap(Identity)`, reuses the existing child relation, and stores the new
FunctionPort dependency. For the relation masks to grow, one endpoint must
also have been outside the previous retained-input closure. That stronger
condition was not established: ordinary Function dispatch already adds a
Derived dependency, which often closes both endpoints. The unconditional
mutation is new typed dependency/incidence evidence; it can also add
`InputGap::InertOperation` when no such operation was already present.

At this admission return, intrusion equality generation does not change. The
`Dependency::FunctionPort` append can therefore alter the retained recognizer
input without a relation ID, context ID, or equality-generation change. Its
exact dependency key deduplicates repeat admissions. Existing context
checkpoint undo removes a newly appended dependency/edge and preserves prior
records on route rollback. That undo does not yet own any future certificate,
withdrawn observation payload, deferral state, or member publication.

The custom `prover` role supplied the conditional derivation. Its session
JSONL records an actual `spawn_agent` call with `agent_type="prover"`,
`fork_turns="none"`, and child `/root/functionport_lifecycle_proof`. The
normal configured request was Sol/high; effective model and effort were not
observable. A separate researcher independently mapped the owning source
seams. These are producer findings, not independent proof review or source
execution.

## Implementation consequence and boundaries

Lifecycle invalidation cannot be keyed only to new relation/context IDs or
intrusion equality generation. New dependency incidence is an input mutation
even when endpoint relations are interned. Hooking allocation sites alone
would miss it. This finding supports the already selected lifecycle gate; it
does not establish a parsed-source history whose FunctionPort dependency is
the sole new closure edge, and does not demonstrate a current stale-result
bug. The existing `retained_input` remains unconditionally `Incomplete` and
has no production caller.

Pre-implementation conformance review found no major or blocking issue and
requested an exact regression for the pre-existing-relation identity
FunctionPort case. Performance review requires incremental typed
incidence/support indexes, indexed save-once undo, and accounting for
simultaneously live old/staged graphs and lifecycle scratch. Those requirements
rule out calling the current global `retained_input` fixed-point scanner on
every mutation. Static accounting and visit-count checks should establish cost;
no timing result is needed yet. No implementation or measurement has been
performed.

## Focused regression and warning ownership follow-up

The exact pre-existing-relation case now has a regression in
`candidate_context_tests.rs::function_port_identity_incidence_changes_without_new_relations_or_intrusion_generation`.
It observes dependency-only FunctionPort evidence without relation/context
allocation or intrusion generation change, then checks route rollback,
successful retry and duplicate-admission deduplication. Focused verification
passed 1/1 under a single Cargo job, one CPU, 1.5 GiB address-space limit and
120-second timeout; the build used reduced test debug info. A fresh
compiler-referee review found no blocking, major or minor findings. This test
exercises the producer but is not ordinary-source reachability or lifecycle
certificate closure.

The warning audit also marks the no-witness `candidate_context_transport`
convenience wrapper `cfg(test)`, since its callers are tests; production uses
the witness-bearing transport. `RetainedInput` fields, `CircuitEvidence.parents`
and `owned_bytes` remain unused production evidence for the future certificate
consumer. Removing them would weaken the approved provenance/accounting
contract, and adopting them now belongs to the next lifecycle implementation
gate. No blanket warning suppression was added.

Next implementation gate remains the full lifecycle foundation under §§4–6:
tracked input mutation, dependent-observation withdrawal, successful private
deferral with exact input retained, member/publication blocking, and route
rollback/retry. Keep production certificate minting, exact two-circuit
recognition, nonempty recursive-context admission, concrete negative formal
rows, public/default cutover, soundness/principality, and F5 retirement open.
