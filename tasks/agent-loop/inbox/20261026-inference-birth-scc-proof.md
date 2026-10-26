# Birth-level SCC qualification: constructive proof receipt

Date: 2026-10-26. Producer: execution_frontier, generic fallback for the
`lean_prover` packet. Supplied baseline:
`0f6346a2de0a8bff863f41d487eb4b29cf8fb5f3`.

Status: **constructed and checker-accepted in the stated graph scope**.
Independent review, native correspondence and original inference soundness
are separate obligations. Source and handoff writes are stopped after this
receipt. No Git, compiler, existing Lean file, root import, configuration or
scheduling record was changed. No children were dispatched.

## Frozen output and authority

- New module: `notes/theory/lean/YulangClosure/BirthLevelSCC.lean`.
- SHA256: `2c76b82d4dc85a4bf4c122731ba014b07df4c863ad679e9a795a57e6546243f0`.
- Only Lean dependency: existing `YulangClosure.Contracts`.
- Scratch and isolated build ownership:
  `/workspace/scratch/f98087c7ac1a/inference-birth/`.

| Input | SHA256 |
| --- | --- |
| `notes/design/2026-10-24-birth-level-scc-intrusion.md`, §§2–4 | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |
| `notes/theory/2026-10-24-birth-level-scc-intrusion.md`, §§2–3 | `67c2a44b7a4009a96424dc329ed4385fffdbc6d6661bf4155408cfbd62de3bfa` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/lakefile.toml` | `834b73ad29dd92c372a948c35d7c6c0f3744eade289a3afbab2ab7375a0d6c01` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |

The authoritative rule uses immutable semantic Value birth and **all vertices**
of each path in its birth-induced graph. Original cross-level references remain
in Ref. A single Value qualifies against itself. Birth does not identify a
lexical telescope, generalization boundary, mutable row level or source strategy.

## Exact claims and source application

All names below have prefix `YulangClosure.BirthLevelSCC`.

1. `finiteReach_iff` proves the executable finite closure returns true exactly
   for ordinary finite reachability. Inputs are an arbitrary Boolean adjacency,
   decidable vertex equality and a finite list containing every vertex. Repeated
   list elements are allowed. `finiteReach` is a Warshall specification algorithm;
   it is **not** a formalization or performance claim about native Kosaraju.
2. `finite_qualifies_iff` applies that closure directly to the unchanged
   `Contracts.Qualifies`, for every actual `ExtrusionOccurrence V T I`. The id,
   origin, receiver and complete signed pair list are unchanged. Eligibility
   computes reachability both ways after retaining precisely same-birth edges.
3. `projection_filter_iff` derives that helper projection and level filtering
   commute, from the local planning invariant below. `compression_iff` derives
   ordinary reachability correspondence by splitting each finite path at its
   semantic vertices. `filtered_compression_iff` composes them for all paths.
4. `finite_helper_qualifies_iff` is the strongest application theorem. For every
   finite helper representation and every unchanged occurrence, executable
   eligibility of its semantic endpoints in the filtered implementation graph
   is equivalent to `Contracts.Qualifies` of the original projected semantic Ref.

The last theorem has these substantive inputs, with no assumed path theorem:

```text
vertices : List (Sum V H)
covers : forall node, node in vertices
edge : Sum V H -> Sum V H -> Bool
birth : V -> Nat
helperLevel : H -> Nat
PlanningInvariant (edge = true) birth helperLevel
event : ExtrusionOccurrence V T I
```

`planningLevel (inl v) = birth v` and
`planningLevel (inr h) = helperLevel h`. Helpers are not semantic Values and
are not assigned births. The sole local edge invariant is:

```text
forall source helper,
  edge source (inr helper) ->
  planningLevel source = helperLevel helper
```

Thus semantic→helper and helper→helper edges preserve planning level.
Helper→semantic and semantic→semantic edges may cross levels and remain in
the original graph. `projectedRef edge u v` is a **nonempty** path from semantic
u to semantic v whose internal vertices are helpers only. The theorem proves
that filtering the implementation edges and then projecting retains exactly
the same incidences as projecting first and filtering semantic endpoint births.
Zero-edge reachability is handled separately, retaining singleton eligibility.

No whole-path preservation premise or qualification oracle is supplied as a
local law. The local invariant is an explicit native obligation, communicated
to `inference_frontier` before its implementation. Native source planning must
establish immutable semantic births, actual helper planning levels, and this
edge invariant. Its semantic-incidence interpretation must match projected Ref.
The native SCC procedure must compute SCCs of that same filtered graph in both
passes. These are the first remaining source/native premises; this module does
not certify any Rust edit or replace implementation review.

## Counterexamples and singleton behavior

- `endpoint_filter_counterexample` and `endpoint_filter_not_qualified`:
  semantic vertices L/R have birth1, X has birth2, and edges are L→X, X→R,
  R→L. L/R lie in one global SCC and have equal births, but they are not mutually
  reachable in the birth1 induced graph. This rejects a global SCC calculation
  followed only by endpoint birth equality. It is a finite graph counterexample;
  no complete Yulang source for this three-vertex shape is claimed.
- `cross_birth_cycle_rejected` and `cross_birth_not_qualified`: O/G have births
  1/2 and reciprocal edges. Both global directions remain present while neither
  cross-birth event qualifies. This is the graph shape of the inspected nested
  source fixture below.
- `eligible_refl`: a semantic endpoint is always eligible against itself,
  including without a self-edge. No special exclusion of singleton SCCs occurs.

## Narrow independent specification review of the existing nested fixture

At the primary's request, inspected the unchanged source string
`my loop x = { my helper y = loop y; helper x }` in
`crates/yu-solver/src/candidate_intrusion_tests.rs:310` and
`crates/yu-solver/tests/candidate_intrusion_observation.rs:31`.
Both existing fixtures expose two actual reciprocal, distinct origin/receiver
owners; the old assertions expected global-SCC qualification and resulting
parent/copy equality.

**ACCEPT the proposed specification correction:** both events must be
nonqualified. The Oct24 design §2 explicitly identifies the nested births 1/2.
The inspected actual planner independently corroborates them:
`candidate_source.rs:1204` starts the definition at level1; Lambda `:1339`
visits its body at the same level; StatementBlock/Block `:1347–1370` schedule
the nested initializer at level+1; Initializer `:1526` visits that initializer
at the supplied child level. Names preserve the existing resolved Value.

Keep the fixture source, ordinary successful inference expectation, actual
parent/pair/group provenance and retained cross-level references. Remove the
expectation that this qualification rule must merge their actual pairs. Do
**not** replace it with a blanket assertion `copy != parent`: design §4 allows
independent lawful constraints to derive equality. This was source/spec review,
not an implementation review; no Rust source/test was written or executed here.

## Original inference obligations remain open

This result repairs a concrete qualification conformance gap and supplies the
previously missing helper-filter justification. It does not establish original
`SourceProblem.InferenceSoundness`, `NativeCorrespondence`, source-scoped
coverage, principality, generalization or combined inference termination.
The old global rule adds extra equalities and therefore restricts models **if**
all accumulated constraints are faithfully retained. Overqualification alone
is not evidence of accepting an ill-typed program; its direct threat is to
coverage/ordinary inference. The constructive original-source derivation and
all-clause preservation remain separate obligations. Birth equality does not
discharge the Oct24 BL-JOINT telescope/shared-witness requirements.

## Actual verification and retained evidence

Fresh isolated project at `inference-birth/project`, with **no copied cache**.
The actual current Contracts and the new module were compiled. All five copied
project inputs were byte-compared with the repository after auditing.

Toolchain executable:
`/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.
Actual versions: Lake `5.0.0-src+eb6cafb`; Lean `4.35.0`, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, x86_64 Linux Release.
Each Lean process used `-j1 -M1024`; no Lean processes overlapped.

- `check-01.log`: version checks and successful Contracts build; initial module
  check failed at three proof/elaboration details (an induction continuation,
  injection into a Boolean disjunction, and reserved binder name `local`).
- `check-02.log`: repaired module build exit0, no warnings. The mathematical
  statements were unchanged; the three proof details were repaired directly.
- `audit-named.log`: bundled `check_lean.py`, `--project` isolated project,
  `--module YulangClosure.BirthLevelSCC`, all 32 names in `theorems.txt`,
  pinned `--lake`, total `--timeout 90`; exit0. Actual full types and complete
  individual axiom results are retained.
- `project/AuditBirthLevelSCC.lean` and `audit-all.log`: independent inventory
  audit of **every one of the 57 originating-module theorem constants**, including
  generated/private helpers; actual type and axiom output; required named roots
  present; no project axioms; exit0. Exactly 57 unique ordered begin/end pairs.
- Complete axiom distribution: 37 constants have no axioms; 19 use only
  `propext`; one generated theorem uses only `Quot.sound`. No `Classical.choice`,
  `sorryAx`, custom axioms or other dependencies occur.
- `source-scan.txt`: no hole/bypass keyword matches in the new module and
  Contracts. `input-hashes.json` records all hashes above.
- `elapsed.txt`: four measured check/audit subprocess batches total
  **7.316104 seconds**. There were five proof-checking Lean processes and two
  Lean version invocations, within the 12-call/250-second bound. Python bytecode
  writing was disabled throughout. No shared helper bytecode was generated.

The 32 named declarations are grouped as: Reach composition/monotonicity;
LevelPath endpoints and conversion (4); finite closure (6); filtered edge and
eligibility equivalences (5); helper incidence and compression (9); and the
two finite graph inventories/counterexample pairs (6). The exact authoritative
inventory is `inference-birth/theorems.txt`; complete originating-module evidence
is `inference-birth/audit-all.log`.

Root owns independent review, integration imports, Git and any production
claims. **Source and handoff writes stopped.**
