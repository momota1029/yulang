# FORCE-PROJECTION-DESIGN-20261025/r3 — source-derived projection

Status: **FROZEN by Luna**. Baseline: `9b945b0bb175e8e0919d388dc720babbdf0c2464`.
Parent: complete Lean proofs of Yulang semantics and type inference. This
bounded architecture gate designs the concrete source-to-Lean projection
needed by Force execution; it grants no Lean/code or production authority.

## Accepted premise and scope

The r2 source-interface gap is accepted after fresh CLEAN review. The
operational paper fixes Force semantics; the r2 outcome records the reviewed
gap and its limits. Construct a concrete `pi` and transition equations for the
represented source domain, or identify the smallest equation that cannot be
derived from the pinned source. Do not narrow the source domain, introduce
observable behavior, or assume arbitrary metadata callbacks.

## Pinned inputs

The operational paper is semantic authority. The typed-boundary document is a
Draft and may locate obligations only. The r9 Lean files are candidates, not
accepted proof dependencies.

| Input | SHA-256 |
|---|---|
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` (Draft only) | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| r2 outcome | `520cf5cb0c716271b9a10872df0c376684d11b8c92df018e01c91f8dbe92e672` |
| r2 review input | `735000fc73892400d596514d9f1ef91aa4468e6fd73a08f997fa6fb8750081fc` |
| r2 independent review | receipt from `/root/force_source_spec_review_r2`, CLEAN within scope |
| `YulangClosure/CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `YulangClosure/ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `YulangClosure/ControlTyping.lean` | `e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f` |
| `YulangClosure/ControlComposition.lean` | `9a48a5f2ef15eb947478757e0fa74457579183ccdbab90f2518886590e33fc40` |
| `YulangClosure/CoreControlBridge.lean` | `30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a` |
| `YulangClosure/CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `YulangClosure/CoreSubstitution.lean` | `fc73d6d60d28f2abb54049a5715751d27df47ad93dbeb8f52966cf98a747bd2f` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |

If a pin changes, stop and return the path and new digest to Luna.

## Assignment, output and budget

- One read-only `architect`, requested Sol/medium, maximum 300 seconds, no
  descendants. The role returns its design in its final response and writes no
  files.
- Luna captures the returned equations and field mapping at the sole output
  path `tasks/agent-loop/inbox/20261025-force-projection-design-r3.md`. Clearly
  label Luna's transcription/decisions; do not attribute file authorship to
  the architect.
- After Luna freezes and hashes that input, one fresh read-only `spec_auditor`,
  requested Sol/low, maximum 300 seconds, checks source support and exact
  projection coverage. It returns findings in its final response and writes
  no files.
- Total worker cap 600 seconds, sequential, no carry. Charge a full grant if
  elapsed time is UNKNOWN. Astra 0; at most one author assignment at a time.
- No Lean/Lake, build, tests, Cargo/native commands, compiler edits, Git, or
  scratch files in r3. Luna owns contract, current state, adjudication and Git.

## Required construction

Specify typed objects and equations for a source configuration and its
represented configuration, including:

1. Static Force syntax label versus fresh dynamic View occurrence; current
   owner and ambient context; wrapped forced value; retained body graph and
   captured typed packets.
2. Distinct `force.effect` entry and `force.result` transport, each licensed by
   the source derivation and retaining explicit path correspondence evidence.
3. View entry, normal saved-ambient restoration and returned-value transport.
   Do not use set subtraction or arbitrary `Metadata` callbacks as the source
   equation.
4. Event observation at the actual emission context, including active outer
   Views beyond handlers. Req capture preserves the literal typed suffix and
   crossed inner Views; re-entry uses the current resumer ambient and fresh,
   coherently renamed occurrences.
5. Separate Fail and malformed-Force Bad propagation, without normal result
   transport or invented failure-world cleanup.
6. Complete suffix View data, packet provenance and source body/capture
   lineage. Control-name substitution must act coherently on bound captured
   occurrences while fixing free ambient names.
7. A commuting diagram with exact producer/consumer fields and every required
   Lean representation change. State which equations follow from the paper,
   which are definitions of the representation, and any remaining premise.

Falsify the design with nested returned thunks, shared View witnesses,
outer-View observation across handlers, repeated resume under different
ambient contexts, Fail, malformed Force Bad and child Bad. Equal endpoint
types, IDs without typed paths, an arbitrary world relation, a transition that
assumes Call typing, or a target-defined “source” relation do not close the
gate.

If a source equation does not determine a Lean record layout, Luna may choose
a representation only when its equations prove correspondence to the fixed
source machine. If an observable source rule remains underdetermined, stop at
the exact equation; do not make that choice.

## Successor propositions (not issued in r3)

On an accepted and frozen representation, a new grant may split:

- **F — `force_plan_formation`** in `ForceFormation.lean`: construct the force
  plan, retained body/capture lineage and both port correspondences from the
  represented source derivation; do not assume them.
- **P — `force_context_projection`** in `ForceProjection.lean`: map every
  represented Force entry, normal Ret, Req capture/re-entry, Fail and Bad
  transition while preserving current context and literal suffix; its final
  source-to-execution theorem consumes F.

Only after this representation is frozen and checked may Luna consider
separate raw-relation grants for S `call_step_erasure` and C
`call_raw_successor_coverage`. A new contract must define their raw relation
independently of Call typing. Call A/B, native correspondence and the full
semantics/type-inference parent remain OPEN.
