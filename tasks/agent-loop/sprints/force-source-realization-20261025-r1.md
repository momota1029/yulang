# FORCE-SOURCE-REALIZATION-20261025/r1 — source-derived Force interface

Status: **FROZEN by Luna**. Baseline: `5ef9f200096d47d864f21bc5b78a245b5804574c`.
This bounded source/architecture sprint identifies and independently checks the
Lean interface for the accepted Force rules. It grants no compiler, Lean-code,
semantic-change, or production authority.

## Parent and outcome

The unchanged parent is complete Lean proofs of Yulang semantics and type
inference. The preceding reviewed source characterization is
`tasks/agent-loop/sprints/force-view-source-owner-20261025-r1-outcome.md`.
The goal of this sprint is one exact source-to-interface derivation for Force
of a nested or captured View-wrapped thunk, or the exact missing equation and
its owner. It must connect the paper's typed-syntax decorator and concrete
context machine to the current Lean representation without treating generic
metadata callbacks as source semantics.

## Frozen inputs

| Input | SHA-256 |
|---|---|
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` (Draft; obligations only) | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| reviewed source-owner handoff | `90506b6c8cf98487690550b95255e37806a79ab527646d1bf12192dfb82dfc1c` |
| r9 Force/View gap packet | `8d7ad0d788d559d5efa3e7b75953221d8a7bd9586ffe09ac1f705fe6a3862406` |
| `YulangClosure/CoreSyntax.lean` (unchecked r9 candidate) | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `YulangClosure/ControlSyntax.lean` (unchecked r9 candidate) | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `YulangClosure/ControlTyping.lean` | `e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f` |
| `YulangClosure/ControlComposition.lean` | `9a48a5f2ef15eb947478757e0fa74457579183ccdbab90f2518886590e33fc40` |
| `YulangClosure/CoreControlBridge.lean` | `30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a` |
| `YulangClosure/CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `YulangClosure/CoreSubstitution.lean` | `fc73d6d60d28f2abb54049a5715751d27df47ad93dbeb8f52966cf98a747bd2f` |
| `lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |

The operational paper is the semantic authority. The draft can locate an
unrealized obligation but cannot license a constructor or behavior. The r9
Lean files are unchecked candidates, not accepted proof dependencies. If any
pinned input changes, stop and return the path and new digest to Luna.

## Exact assignment and output lease

- One `architect`, requested Sol/medium, maximum 300 seconds; read-only except
  the sole output lease below. No descendants.
- Sole output: `tasks/agent-loop/inbox/20261025-force-source-interface-proposal.md`.
- Then one fresh `spec_auditor`, requested Sol/low, maximum 300 seconds, on the
  frozen proposal. Read-only, no descendants or output file.
- Total worker cap: 600 seconds; author and reviewer run sequentially. Astra 0.
- No code edits, Lean/Lake, builds, tests, Cargo/native commands, Git, or scratch
  files. Luna alone owns adjudication, contract revisions, current state and Git.

## Required source equations and falsifier

Trace a resolved typed Force of a wrapped/captured thunk from its source
derivation and retained Delay body/capture packet into the actual Lean
execution context. State each supplied field, each derived field, and every
remaining assumption. The proposal must give concrete types and equations for:

1. Stable Force syntax label versus the fresh dynamic View occurrence, current
   owner/context, forced wrapped value, retained body graph and captures.
2. The distinct `force.effect` position and `force.result` typed transport,
   including how each correspondence is licensed by the source derivation.
3. View entry and normal leave/restoration from the source context machine,
   not arbitrary `Metadata` callbacks or set subtraction.
4. Req observation/capture/re-entry under current resumer context, preserving
   active outer Views and the literal typed suffix.
5. Separate source Fail and malformed-Force Bad propagation. Do not infer a
   cleanup/world operation absent from the accepted source.
6. A commuting producer/consumer diagram identifying exact existing Lean
   fields that realize source contexts and exact fields that must change.

The independent falsifier is a required source transition for which the
proposed record cannot provide the distinct port, body/capture lineage,
dynamic occurrence, current context, or saved-context behavior without a
fabricated mapping. Equal endpoint types, `PathRule.adapterMap`, an arbitrary
world relation, or a transition constructor that assumes Call typing do not
close this obligation.

If accepted source equations do not determine the projection into the chosen
Lean context representation, return the smallest missing equation and its
owner. Do not choose new observable behavior, weaken the represented source
domain, or move the problem into an assumed premise. The spec auditor checks
all equations against the frozen sources and the complete Ret/Req/Fail/Bad
trace. Luna accepts or rejects the interface before any implementation grant.

## Success, non-goals, and successor gate

Success is a frozen source-derived interface proposal that passes fresh spec
review and Luna adjudication, or an exact source-input obstruction that names
the missing source owner/equation. Neither outcome is a Lean theorem.

No S/C, Call A/B, Force implementation, semantic approval, or production
promotion is authorized by this sprint. On an accepted interface, Luna will
freeze a separate implementation/proof contract with disjoint output leases:
an implementation handoff, `ForceFormation.lean` for
`force_plan_formation`, and `ForceProjection.lean` for
`force_context_projection`. The two proposition agents may work in parallel
only after the implementation freezes and Luna checks its dependency chain.
The projection theorem's final source-to-execution application consumes the
frozen formation result. S `call_step_erasure` and C
`call_raw_successor_coverage` remain gated until that Force representation is
frozen and checked; their raw relation must be defined independently.

The exact reviewed source-characterization gate and the whole Yulang
semantics/type-inference parent remain OPEN until their respective proof and
source/native correspondence obligations close.
