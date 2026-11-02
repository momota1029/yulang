# Sprint R242 — original literal input dependence

Status: ADMITTED for a bounded Sol-owned diagnostic proof attempt.
Parent: unchanged `SourceProblem.InferenceSoundness`,
`notes/theory/lean/YulangClosure/Contracts.lean:128–130`.
Authority is unchanged: the adopted L1 and canonical literal generation
equations, plus the existing original interpretation and consumers.
R241 remains BLOCKED with parent delta zero; its reviewed artifacts are frozen.

## Fixed outcome

Test whether the actual original literal consumers are determined by adopted
literal generation and a fixed decoded assignment when independent `Inputs`
fields vary. In particular, derive an input-dependence result for
`Inputs.ground` and isolate the separate `traceForm` premise used by the
existing pure-Return consumer. This is a diagnostic statement about the
current parameterized formalization. It does not claim a source-qualified
counterexample to `InferenceSoundness`, select alternative source semantics,
or authorize a new semantic model.

Preserve all eight literal constructors and payloads, the same source
occurrence/root/event/scope/shared witness, decoded assignment and frame
prefix. Keep `Sorts`, source generation, declarations, `valueForm`, readout,
environment, and every non-target `Inputs` field fixed in each comparison.
Attempt the exact original `foldedLiteralKernel`/`Build` consumer. Separately
show which generator/decoder equations are definitionally independent of
`ground` and `traceForm`, and account for `return_observation_iff` and the
existing Return consumer without supplying their missing trace equation.

Success is a checked parameter-dependence theorem applied to the actual
consumer, with complete theorem types and axiom audits. A conditional
characterization or mere record-field observation is insufficient unless it
establishes that varying only the named field changes the consumer result for
the same fixed decoded assignment and original coordinates. Any assumptions
about the other fixed facts must be explicit. This diagnostic does not close
the unchanged parent.

Do not assume `LiteralAtom`, `GroundLaw`, a readout law, an original carrier
map or a Return trace law. Do not choose semantic carriers, modify the
consumer, fabricate a `SourceProblem` instance, narrow source forms, or
reinterpret the diagnostic as an approved source meaning. If the exact
variation cannot be constructed from the current definitions, return the
precise constructor/field obstruction and continue any independent
noninterference result.

## Sol assignment and exact leases

Registered `prover`; requested Sol/high; no descendants. Exact outputs:

- `notes/theory/lean/YulangClosure/OriginalLiteralInputDependenceR242.lean`
- `tasks/agent-loop/inbox/original-literal-input-dependence-r242.md`

Frozen direct dependencies: R241 artifact and handoff; L1 adoption; canonical
generation adoption; `OriginalSourceInterpretation.lean`,
`OriginalSourceEnvironment.lean`, `OriginalReturnWorld.lean`, and the unchanged
parent contract. Record and verify dependency hashes in the handoff. No Rust,
compiler, test, question, central-state or quarantined path is leased.

## Stages, gates and resources

1. Derive the exact `Inputs.ground` dependence from
   `folded_literal_build_exact`, or produce a same-state pair differing only
   in `ground` that changes the original Build result under explicit fixed
   premises.
2. Separate `traceForm` dependence for the original pure-Return consumer from
   generator/decode noninterference; apply existing consumer theorems where
   possible and state the precise remaining equation.
3. Apply each checked result to the unchanged parent obligation, reporting
   delta zero unless an actual parent premise is discharged. Freeze the artifact
   and one handoff with hashes, full types/axioms, check results and resources.

Sol may run at most one pinned Lean check, using the existing cache only. After
handoff, assign a fresh independent review; only then may Luna run one targeted
pinned check on the frozen bytes and complete axiom audit. No tests, Cargo,
cache growth, Astra, descendants or Rust writes. Sol active-work cap: 1,800
seconds. Preserve all prior R240/R241 resource receipts. Luna owns review,
state synchronization and all Git.

Stop at a genuine definition boundary, completed applied result, budget bound,
or user STOP. Record actual runtime/model only when observed; otherwise use
UNKNOWN. UNKNOWN and quarantined workers/paths remain untouched.
