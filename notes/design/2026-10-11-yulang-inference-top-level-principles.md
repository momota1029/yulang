# Yulang Type-Inference Development: Top-Level Principles

Status: Authoritative
Scope: design, proof, implementation, error handling, and evaluation of
Yulang's Simple-sub type inference and its replacement of F5
Approved-by: user, explicit decision in this conversation, 2026-10-11
Reviewed-by: spec_auditor and compiler_referee, no findings, 2026-10-11
Supersedes: any inference-workflow requirement that treats exhaustive search,
proof-hostile implementation, exact diagnostic identity, complete internal
failure restoration, capacity restoration, or allocation-free rollback as a
general correctness or quality requirement

## Purpose

The purpose is to implement a correct, efficient, and natural Simple-sub type
inference algorithm. Simple-sub constraint generation, accumulation,
propagation, levels, extrusion, intrusion, and generalization form the
algorithm. Proof, implementation, and evaluation serve that algorithm.

## 1. Prefer the mathematical structure

Construct inference from its mathematical operations: generate and accumulate
constraints, propagate them, perform level-aware extrusion and intrusion, and
generalize at the selected boundaries. Prove the required soundness,
principality, termination, and normal inference progress.

Do not add special rules that solve individual constraints at generation time.
Do not turn inference into speculative search over possible typings. A proof
obligation does not authorize changing ordinary inference into a less natural
algorithm.

### 1.1 Source constraints and intrusion: direct clarification, 2026-10-14

Authority: the user's direct explanation in the continuing completion
conversation. This records the selected inference operation; it does not
assert a newly proved theorem. The earlier review attribution applies to the
October 11 text; review of this clarification is recorded separately below.

1. Construct types and constraints for source expressions. The user's example
   `if true { 1 } else { "str" }` has inferred type `int | str`: both branches
   contribute. A formal initially has a type variable such as `'a`; using it
   as a function adds `'a <: ('b ['c] -> ['d] 'e)`. This construction needs
   neither prior execution of the condition nor constant folding. Unknown
   types remain variables constrained by their uses.
2. Perform ordinary level-based Simple-sub extrusion as constraints are added
   and propagated. At each copying occurrence, retain the parent and child
   value-variable identities associated with the actual type-variable copies.
   The existing [occurrence qualification](2026-10-12-intrusion-value-type-association.md)
   specifies the origin/receiver Values and the produced polar parent/copy
   pairs. Resolved identities implement the user's value-variable names.
3. Compute SCCs of the selected value-reference graph. When the two Values
   associated with that extrusion occurrence are in the same SCC, undo that
   extrusion by equating its actual type parent/copy pairs. SCC membership of
   type-bound endpoints is not this criterion. Retain the added constraints
   and propagate the equality through their actual consumers.

These steps describe constraint construction and solving, not a requirement
to determine every variable's final type before generating constraints. They
do not add a new scheduling, storage or transport convention to the approved
occurrence rule. Existing preservation obligations concern this algorithm;
evaluation or constant folding is not a prerequisite to infer the example.

The user also explicitly requires reuse of the existing hygiene proofs. Apply
the established results and their actual hypotheses through the
[existing proof integration](2026-10-10-annotation-effect-hygiene-integration.md#3-existing-results-retained-and-reused).
Work on missing constructor/consumer correspondence at its implementation
owner. Do not restart a proved hygiene result or treat a stronger unfinished
characterization as evidence that no reusable proof exists.

Clarification review: independent `spec_auditor`, no findings, 2026-10-14;
transcription and applicability only, not algorithm or proof certification.

## 2. Actively reduce computational cost

Avoid naive exhaustive search, needless recomputation, excessive state
duplication, and proliferation of auxiliary data structures. State the
invariant that justifies each optimization and give its work and space bounds.
Prove correctness of the optimization. Do not complicate the inference
algorithm merely to make a proof shorter.

## 3. Derive implementation from proof

Establish the algorithm's central invariants before implementation. Derive data
structures and processing steps that preserve those invariants naturally.
Do not first build a brute-force implementation and then search for convenient
local lemmas about its behavior. The implementation must correspond to the
proved algorithm, not define a second algorithm that the proof attempts to
explain afterward.

## 4. Require only necessary abnormal-path safety

When a type error occurs, continue inference and diagnostics where feasible and
detect appropriate errors. Exact diagnostic text, order, or identity and full
internal-state restoration are not general requirements. It is acceptable to
stop safely when resources are irrecoverably exhausted.

Abnormal handling must never accept an incorrect typing or publish an
inconsistent result. Continue only the work whose state remains meaningful;
otherwise terminate the affected private attempt without exposing its partial
result. Diagnostic recovery may be best-effort and need not reconstruct the
entire pre-error state.

## 5. Do not make rollback a goal

Rollback is one possible implementation technique when it is needed to
preserve a proved semantic invariant. It is not a goal in itself. Do not impose
complete abnormal-path recovery, restoration of prior capacities, or
allocation-free rollback as inference-correctness requirements without a proof
that the semantic invariant requires them.

The same principle applies to retry: retrying must not search for another
typing. Reusing a failed internal state is allowed only when the relevant
invariants are proved; otherwise discard or stop the private attempt safely.

## Evaluation

Evaluate the work by inference correctness, completeness for the supported
natural source behavior, and computational efficiency. Do not use code size,
test count, lemma count, or rollback completeness as success criteria.

## Authority and integration

This document records the user's explicit top-level decision. It does not
approve unrelated source restrictions, API changes, or weakened successful
inference behavior.

It supersedes the unconditional abnormal-route restoration and supported-retry
requirements in the private candidate suspension contract §§6–7, and the
corresponding whole-route rollback requirements in contextual attachment /
admission, wherever they make full restoration a general correctness gate.
Those requirements remain only where an owning proof shows that a particular
rollback is necessary to preserve a semantic invariant. This document does
not select a replacement storage mechanism.

Successful suspension remains part of normal inference progress: accepted
constraints and the owned continuation must be retained, dependent results
must not be reused while invalid, and inconsistent or partial results must
not be published. This principle does not waive soundness, principality,
termination, source correspondence, complete Call, effect hygiene, or F5
replacement gates.
