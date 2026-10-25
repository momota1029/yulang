# FORCE-RESULT-SOURCE-EQUATIONS-20261025/r4 — derive the Force bridge

Status: **FROZEN by Luna**. Baseline: `9b945b0bb175e8e0919d388dc720babbdf0c2464`.
Parent: complete Lean proofs of Yulang semantics and type inference. This
bounded source-equation sprint discharges the two reviewed blockers before any
representation or Lean implementation authority.

## Frozen authorities and inputs

The operational paper is semantic authority. The typed-boundary file is a
Draft and cannot supply a missing equation. The r3 proposal is a candidate,
not a proved interface. The current r9 Lean files are unchecked research
candidates.

| Input | SHA-256 |
|---|---|
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` (Draft only) | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| reviewed Force source-owner handoff | `90506b6c8cf98487690550b95255e37806a79ab527646d1bf12192dfb82dfc1c` |
| r2 accepted gap outcome | `520cf5cb0c716271b9a10872df0c376684d11b8c92df018e01c91f8dbe92e672` |
| blocked r3 contract | `b9d7453a0ea6e782cbfd7f6a78e88bbb7a723546bc130a8b8990fdc6c1a56b29` |
| blocked r3 capture | `a255b7c7e84ba608b0fa42372455560c90e9bc59428865f452e351f11e18de77` |
| `YulangClosure/CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `YulangClosure/ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `YulangClosure/ControlTyping.lean` | `e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f` |
| `YulangClosure/ControlComposition.lean` | `9a48a5f2ef15eb947478757e0fa74457579183ccdbab90f2518886590e33fc40` |
| `YulangClosure/CoreControlBridge.lean` | `30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a` |
| `YulangClosure/CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `YulangClosure/CoreSubstitution.lean` | `fc73d6d60d28f2abb54049a5715751d27df47ad93dbeb8f52966cf98a747bd2f` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |

If a pin changes, stop and return the path and new digest to Luna.

## Exact assignments and output leases

Run two independent read-only source-research packets in parallel, then one
fresh independent spec audit after both writers STOP and freeze their outputs.
No descendants.

### F — Force-result Flow derivation

- One Sol/high `researcher`, maximum 600 seconds.
- Sole output: `tasks/agent-loop/inbox/20261025-force-result-flow-derivation.md`.
- Derive the complete Force-result Flow construction from accepted source
  rules, or demonstrate the exact underdetermination. Identify every incoming
  occurrence, fresh output occurrence, typed template domain/image, and row
  connecting the actual body-return packet, the forced thunk's `force.result`
  subtree, and latent descendants. Give an authoritative derivation for each
  row. “Separate result transport” and the Draft's two-input image are not
  themselves a proof.
- If derivation fails, distinguish missing evidence from genuine
  underdetermination. A useful discriminator is two candidate row systems
  satisfying every cited accepted rule but producing different `Path` or
  `Eligible` observations on the same source-admitted configuration. Without
  that, report a missing equation and owner, not semantic ambiguity.

### P — Source-indexed projection inputs

- One separate Sol/high `researcher`, maximum 600 seconds.
- Sole output: `tasks/agent-loop/inbox/20261025-force-source-input-equations.md`.
- Define how source input owns and supplies the retained derivation,
  decoration/template and packet lineage. Give constructor equations for raw
  resolution, saved-View extension, boundary/segment cut and complete suffix
  extraction. Preserve every counted administrative reference/type/view step.
  Do not collapse resolution to an unproved lookup. Parameterize the disputed
  Force-result transport from F rather than choosing its rows.
- Keep the raw relation defined independently of Call typing. Preserve literal
  suffix contents, malformed and child Bad, current-resumer ambient, and
  scoped bound/free substitution. Separate representational policy (record
  layout, index/fresh-name encoding, context zipper) from source correspondence.

### Fresh review

- After both outputs freeze, one fresh Sol/low `spec_auditor`, maximum 300
  seconds, reads both exact hashes, this contract and all pinned authorities.
- It checks each row/equation against the paper, the underdetermination test,
  cross-packet dependency consistency, and that no draft-only behavior or
  Call-typed premise is smuggled in. It returns findings in its final response
  and writes no file.

## Resources, stop conditions and gate

Fresh envelope: 1,800 seconds total — F 600, P 600 (parallel, disjoint paths),
review 300 (sequential), Luna adjudication 300. No carry from earlier sprints.
Astra 0; at most two new authors concurrently. Charge full grants when elapsed
time is UNKNOWN. No code, Lean/Lake, build, tests, Cargo/native commands,
compiler edits, Git or scratch files. Luna owns current, adjudication, contract
and Git.

Success is the fresh review validating source-derived equations, or validating
that a precise equation is absent and that a genuine observable semantic
choice is required. If only the representation construction is missing, Luna
can freeze a new representation contract from the fixed equations. If source
allows distinct observable Force-result rows, stop at that exact choice for
the existing semantic authority process; do not choose one here.

This sprint grants no representation adoption, Lean implementation, F/P Lean
theorems, S/C, Call A/B, production promotion or parent closure. The next
potential proposition wave remains `force_plan_formation` and
`force_context_projection`, after a reviewed interface, implementation freeze
and dependency-order Lean check. Separate raw S/C grants remain later.
