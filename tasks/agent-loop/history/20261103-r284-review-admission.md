# R284 independent review admission

Admit one fresh read-only Sol Lean review of the frozen R284 candidate and
counterexample under
`tasks/agent-loop/sprints/extrusion-capture-validity-r284-review.md`.
R284 producer `/root/sol_r284_capture_validity` returned STOP / WRITES_STOPPED,
NO_DESCENDANTS, no processes; its complete proof grant is charged. Frozen
outputs:

- Module `notes/theory/lean/YulangClosure/OriginalExtrusionCaptureValidityR284.lean`,
  SHA-256 `6842d0af28691e18ea6c50f250ff08f14205c5cb45ced3d0c58e07178e30f49c`.
- Handoff `tasks/agent-loop/inbox/extrusion-capture-validity-r284.md`,
  SHA-256 `8f4d100930853d61b6d7f883f14955b67c3b79ffb170c76e87aec88d5e4b3407`.
- Producer outcome `tasks/agent-loop/history/20261103-r284-proof-outcome.md`,
  SHA-256 `2327572bb38cf840b6e027b6345e8f77aa8cbda148f399c554d360217438d0fb`.

## Frozen pins and Luna preflight

Review contract
`tasks/agent-loop/sprints/extrusion-capture-validity-r284-review.md`,
SHA-256 `e99d2cade6ee8214879a678c5b762ccfe910fe397fc33e99281244f20e4f3dfc`.
The explicit 26-input manifest is
`tasks/agent-loop/sprints/extrusion-capture-validity-r284-review-inputs.json`,
SHA-256 `8407c07a92ec751aee9214c7b0c6b868eca7e50a0767fa9b451d2c620cd132d4`.
Luna's `python3` preflight hashed every exact repository-relative entry; all
26 matched. The manifest includes the 11-module workspace cone, project
configs, R283/R284 outputs, unchanged R70 parent contract/handoff, approved
principles and the exact checker script. No body was rendered by that preflight.

## Live roster and cache handoff

Luna synchronized the live roster after producer STOP: only `/root` is active;
R284 producer, R283 producer/reviewers and all earlier children are
completed/STOPPED. There are no other RUNNING/WAITING children or descendants.
The `.lake/build` lease was HELD only by the R284 producer, which has stopped
with no process. R283's cache lease was already transferred to R284 after its
producer STOP. Luna now transfers only `.lake/build` ownership from the stopped
R284 producer to this reviewer. R284 module and handoff remain FROZEN under
their producer. No UNKNOWN/quarantined path is touched; no capacity override.

## Reviewer and limits

Fresh identity `/root/sol_r284_capture_validity_review`, registered
`lean_prover`, requested Sol/high, maximum 900s, no descendants. The reviewer
must use the contract-only WAITING/GO and first-operation 26-path hash gate,
then inspect model source first and candidate/handoff second. It owns the
exclusive `.lake/build` lease for the focused independent kernel check and
per-theorem audit; no artifact write lease. It must challenge the exact
`CaptureComplete` quantifiers, `viewTailGap` counterexample, all 18 theorem
types/axioms, initialization application, and omitted cases. No broad build or
tests, Rust/source/Cargo/probes/external bodies, source edits, Git or semantic
changes.

The 900s review allocation is within R284's existing 3,600s envelope (2,400s
producer, 900s reviewer, 300s Luna); no new grant or carryover. Parent/A/B
remains 0->0, original R70 and source/native correspondence remain OPEN, and
`NO_SAFE_CODE_SLICE` remains. Luna owns the receipt, adjudication and any later
sprint selection.
