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
