# R28 revision 1 closeout: caller module initialization

R28 rev1 froze and independently reviewed a caller-side `CallerModuleInit`
candidate, then tested it against the unchanged original guard at the same
tuple. The specification review was CLEAN only for an unadopted proposal; the
compiler review found blockers for any derivation or implementation.

The proof lane attempted the original `j0/a0` application and stopped at the
first missing independent inputs: authentic predecessor `P` and actual same-
event `Init0`. It also found no exhaustive existing guard introduction or
same-event old-dependent extension. The source-owner audit inspected the HIR,
playground candidate and runtime owners. `RuntimeProgram::start` creates a real
`ModuleRun`, but accepts neither `P` nor the original dependent evidence and
does not activate every resolved declaration root. Opaque caller-evidence
transport and HIR retention do not change that.

The compiler review additionally found that direct visibility does not prove
the original dynamic authority/incidence judgment: original `Inc_C` needs an
exact typed `Path` plus activity of the referenced member, owner and receiver.
The existing source module has no supplier for those facts. The old-field
restriction diagram and original semantic `a0` also remain unconstructed.
The separate fixed-`c` Operation `DeclContribution`/license gap remains open.

Therefore the selected public path has **NO_SAFE_CODE_SLICE**. No payload
transport or guard-shaped receipt is added. Parent
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN/closure0, with
original conditions **0 -> 0**. No source restriction, semantic adoption,
production authority, `JointWF`, `OriginalInitial`, phase closure, whole Call,
F1/FK1, soundness or principality follows.

Frozen evidence:

- R28 source candidate
  `notes/design/2026-10-18-caller-module-init-research-definition.md`, SHA
  `06a924b9ea0b7f987b15b4c4f4509203f3e04c8d03536678794d3e43b2b4c49d`.
- Conditional proof
  `notes/theory/2026-10-18-caller-module-init-guard-preservation.md`, SHA
  `50a24c63948efe0c964f45e72c2819b496e5c79461b4d2494124fc97ada12686`;
  handoff SHA
  `1e3a3642d401e7bc2ec8590867a5acc726eaad9f5a541d0c4d8a96ab12b8739b`.
- Independent spec review: CLEAN only as a non-adopted proposal; two blocking
  design gaps were recorded.
- Independent compiler review: findings block original guard derivation and
  implementation; the candidate honestly retains all gaps.
- Read-only event-owner audit: `Init0` absent from the inspected source/native
  route; source roots and dynamic activity are distinct.
- Dispatcher closeout: no safe code slice; proceed, if useful, by drafting a
  concrete research-only source transition with its old-dependency restriction
  proof, then independent review and explicit adoption boundary.

The user authorized one attempt at the recommended caller-initializer route.
This permits developing a specific reversible *semantic proposal*, not silently
adopting a new initial event or authority policy. R28 revision 2 is limited to
making that exact proposal reviewable. Any compiler implementation remains
WAITING until the transition and evidence policy are reviewed and approved.
