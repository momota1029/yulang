# Ordinary-state scalar registry bridge (cycle118)

Status: Draft. Scope: I-16 P1/P2/P3. Fields reduced: `B4Bridges.frontierLocal`,
`evidenceNode`, and the visible-impl part of `canonicalLocalOrder`.
The general-source obligations remain twelve of twelve open.

## Scope and data

A registry is an arbitrary finite list of source entries (role, declaration
identity, int/str scalar). Each generates a real `Roles.Impl` with one scalar
receiver and an empty where list. No checked registry, successful solver model,
materialized receiver, selected candidate, or dictionary is supplied by callers.
The real ordinary solver first checks an arbitrary `State n`; explicit paired
atoms then materialize the receiver, and the existing dictionary elaborator
returns the actual declaration and its empty child list.

The independent `Candidate` judgment relates source membership, role equality,
and scalar equality. `Ready` states zero, unique, or two distinct candidates.
`Known` uses paired atoms in the original ordinary state, not an executor result.
`Classify` combines independent knownness and candidates and retains pending
when no supported scalar evidence exists. `run_exact` quantifies over all
registries, roles, receiver slots, states, and returned outcomes. Consistency
and independent classification occur on the right of its iff, not as inputs.

## All-model semantics and order

For every returned selected dictionary, `run_all_models` proves actual source
visibility, role agreement, scalar-head equivalence, declaration identity and
all children (empty) for every Common assignment satisfying the input state.
This is not merely the solver's chosen assignment. Visible-set equality preserves
the entire executable result and exact dictionary payload, hence permutation
and duplicate enumeration do too.

## Limits and fidelity

No-supported-evidence pending is an adapter boundary, not complete language
knownness: bool/unit and structural forms are not materialized. Inconsistency
returns unavailable (`none`), not a new language rejection rule. Finite nullary
scalar heads do not trigger K2. No where children, associated equations, method
body semantics, general interval propagation, or source B4 instance are claimed.
The two old B4 target obstructions recorded in cycle112 remain unresolved.

Before this definition, `work/dots-audit` role-boundary claims were checked:
ROLE-MORE-001 confirms zero/single/distinct duplicate ambiguity; ROLE-MORE-002
rejects priority by specificity. The existing same-declaration duplicate-list
law is reused, not a new semantic decision. Source authority is spec 6.2/6.3.
No fresh Yulang2 binary run was performed.
