# LEAN-CORE-CONTROL-BRIDGE-20261025/r6 outcome

## Status

**Accepted bounded Lean bridge; complete Yulang semantics/type-inference goal
remains OPEN.** Luna adjudicated the frozen candidate after both pinned Lean
checks passed and the fresh independent compiler referee returned CLEAN. This
closes only the stated Original-to-Control bridge declarations. It does not
close full source semantics, source/native correspondence, source-scoped
coverage, principality, termination, or the original inference A/B obligations.

## Before and after

R5 successfully checked `ControlComposition` but failed elaboration in
`CoreControlBridge` at four dependent-index `Prefix` inductions and one
typing-preservation induction-hypothesis application. No semantic
counterexample was established. R6 introduced variable-start-index helper
proofs carrying an explicit equality to the embedded source state, a generic
Original prefix typing-preservation theorem, and a derived stationary-prefix
lemma for no-step exits. The unchanged public statements now elaborate and
check.

Accepted declarations retain their original quantifiers and domains:

- `finite_coverage` and `machine_finite_coverage` classify arbitrary finite
  traces into an Original prefix followed by the explicit boundary exit and an
  arbitrary foreign Control/root-machine prefix;
- `exit_empty_prefix` proves the terminal empty-suffix exit is stationary;
- `finite_typed_transfer` transfers the existing closed Original typing
  premise along any source prefix;
- `finite_closed_safety` establishes typing, Bad exclusion, and progress or a
  terminal exit for the exact closed embedded source fragment.

The four Control transitions remain `originalEnter`, `originalReturnBind`
using actual `Original.substComp (Original.single value)`,
`originalPrincipal`, and explicit `originalExit`. The literal old suffix and
all metadata/body/source/world/trace-length quantifiers remain intact. R6
changed proof terms only; it changed no source or Control transition and no
production compiler semantics.

## Pinned checks and axiom receipt

Toolchain: Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

From `notes/theory/lean`, Luna ran these serialized commands:

```sh
timeout 60s lake env lean -j1 -M1024 -o .lake/build/lib/lean/YulangClosure/CoreControlBridge.olean YulangClosure/CoreControlBridge.lean
timeout 60s lake env lean -j1 -M1024 -o .lake/build/lib/lean/YulangClosure.olean YulangClosure.lean
```

Both exited 0. Measured command times were 0.473s and 0.091s respectively.
The root output reported:

```text
YulangClosure.CoreControlBridge.successor_coverage: no axioms
YulangClosure.CoreControlBridge.machine_finite_coverage: [propext]
YulangClosure.CoreControlBridge.finite_closed_safety: [propext]
```

The dependency-component scan covered `Contracts`, `CoreSyntax`,
`CoreSubstitution`, `CoreExecution`, `CoreComposition`, `ControlSyntax`,
`ControlTyping`, `ControlComposition`, `CoreControlBridge`, and the root module.
Only comments in `ControlComposition.lean` matched the words `admit` or
`axiom`; no proof holes, project axioms, unsafe declarations, or
`native_decide` uses were found. This scan supplements kernel checking; it is
not the review.

`python3 tools/agent_sprint.py check` passed for the compact scheduling state.
It is static workflow evidence only. No tests, Cargo, or native probes ran.

## Independent review and provenance

Fresh read-only reviewer `/root/r6_bridge_referee` returned CLEAN with no
blocking, major, or minor findings. The reviewer independently matched the
bridge/root hashes, checked generalized induction and statement specialization,
source/exit/foreign trace arithmetic, exact source transitions and substitution,
typing/progress domains, root axiom query sites, and the dependency hole/escape
scan. It ran no edits, tests, Lean process, Git commands, or descendants.
Requested route was `compiler_referee`, gpt-6.1-sol/medium; observed session,
model, and effort remain UNKNOWN. Actual elapsed review time is UNKNOWN; the
120-second grant is charged in full. Reviewer STOPPED.

Constructive producer `/root/lean_prefix_generalization` returned a frozen
revision-1 handoff and STOPPED after 171.0 seconds. Requested route was
`prover`, Sol/high; observed model and effort remain UNKNOWN. Its full
240-second grant is charged. It ran no Lean checks, tests, or descendants.

## Frozen artifacts and dependencies

| Artifact | SHA-256 |
|---|---|
| `notes/theory/lean/YulangClosure/CoreControlBridge.lean` | `30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a` |
| `notes/theory/lean/YulangClosure/ControlSyntax.lean` | `801f5ff354d0546aaca6fbd353cf261d3e49c915f78687d76167eab7b9aa8bc9` |
| `notes/theory/lean/YulangClosure/ControlTyping.lean` | `67e0d5d8840090ad7adf06b33c65725dc0901488c16f9dcc235c5c0372ae0135` |
| `notes/theory/lean/YulangClosure/ControlComposition.lean` | `9a48a5f2ef15eb947478757e0fa74457579183ccdbab90f2518886590e33fc40` |
| `notes/theory/lean/YulangClosure.lean` | `04a209f4aa4a9e8c2848aee11eb16befb6fe4e0b566d4683dd0705f96ccf3b2f` |
| `tasks/agent-loop/inbox/20261025-lean-core-control-induction.md` | `bf7d4bc530bb8e2d86ad9f3a93ed74642ef3b23488ece013753feee8e6bd1cd7` |
| r6 contract | `a362c015ba0cf47df2ce0038dd8c756dbc98f50d2d8737e9dafe9077e35db486` |

The frozen direct/transitive dependency hashes, including the toolchain, are
also recorded in the r6 contract and were rechecked before review. Producer and
reviewer STOP receipts are recorded in this outcome and `current.json`.

## Resources, remaining parents, and Git

The prior 3,600-second r3-r5 cap remains fully accounted; its 40-second review
reserve and 6.8-second remainder were untouched. R6 added 600 seconds without
resetting earlier grants: prover 240, primary checks 120, conditional same-
prover repair 120, and fresh review 120. Prover, checks, and review grants
(480 seconds total) are charged; the conditional repair grant remains unused.
Actual primary Lean commands totaled 0.564s. No resource is carried into a new
sprint automatically.

The bridge is accepted as a checked and reviewed bounded theorem component.
Full Yulang semantics/type inference, source/native correspondence, all other
source constructors, source initialization, Call/wrap/Resume, raw-constructor
coverage, principality, termination, and original A/B remain OPEN. No
production authority follows from this theorem.

At initial outcome freeze, the r6 artifacts are ready for Luna's explicit-path
milestone commit and ordinary non-forced push; the final commit/push receipt is
recorded by the primary in `current.json` after outbound-range and remote-head
inspection.
