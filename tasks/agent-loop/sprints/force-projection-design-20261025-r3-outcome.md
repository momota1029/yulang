# FORCE-PROJECTION-DESIGN-20261025/r3 outcome

Status: **BLOCKED_SOURCE_PROJECTION_DESIGN**. Parent: complete Lean proofs of
Yulang semantics and type inference — **OPEN**.

## Frozen evidence and review

- Contract:
  `tasks/agent-loop/sprints/force-projection-design-20261025-r3.md`, SHA-256
  `b9d7453a0ea6e782cbfd7f6a78e88bbb7a723546bc130a8b8990fdc6c1a56b29`.
- Luna's capture of the read-only architect final:
  `tasks/agent-loop/inbox/20261025-force-projection-design-r3.md`, SHA-256
  `a255b7c7e84ba608b0fa42372455560c90e9bc59428865f452e351f11e18de77`.
- Fresh `spec_auditor` `/root/force_projection_spec_review_r3` returned
  **BLOCKING** for accepting the candidate as an executable projection. It
  reports all fifteen checked digests match; the r3 contract pins and capture
  were also checked locally. The reviewer wrote no files and ran no tools.
- Architect and auditor were each granted 300 seconds. Exact elapsed time is
  UNKNOWN for both, so both full grants are charged. Both stopped; no
  descendants. The architect's design is a proposal, not a theorem.
- The worker ran no Lean/Lake, build, tests, Cargo/native commands or Git. A
  primary `git add` later failed because `.git` is read-only; no index or
  commit changed. No code or semantics changed.

## Adjudicated findings

The review accepts these as **source obligations**, not as proved Lean
realizations: distinct static/dynamic Force identity and effect/result ports;
saved-ambient union/restoration; observation over the executing context at
emission; immutable observations during bubbling; shallow capture boundaries;
current-resumer ambient on re-entry; scoped bound-name renaming; and distinct
Fail/Bad propagation without normal result transport.

Two requirements remain BLOCKING:

1. **Force-result Flow rows.** The operational paper requires fresh-output
   typed transport, retained result information, and distinct `force.effect`
   and `force.result`. Its generic Flow rules do not explicitly determine the
   combined input rows from both the actual body-return packet and the thunk's
   `force.result` profile subtree. The candidate `transportResult` leaves
   these rows unspecified. The Draft's multi-input formula and prefix-removal
   example are non-authoritative.
2. **Executable `pi`.** The candidate gives a construction recipe, not full
   inputs/equations. It does not associate `SourceDecoration` with the source
   input, define boundary/suffix extraction, or give constructor equations for
   raw `resolveH` and saved-View extension. It must preserve counted
   administrative transitions and work for malformed/child Bad without a
   Force typing derivation.

The classification is a missing source-to-representation derivation; no
implementation defect or semantic change is established. If two distinct
observable row systems both satisfy accepted rules, route that exact choice to
the semantic authority. Do not infer it from a record layout or the Draft.

## Next step

Run parallel focused source-equation assignments: F derives the exact
Force-result Flow construction or its smallest underdetermination; P derives
source-indexed projection inputs, resolution, context cut and suffix equations
while parameterizing F's unresolved result rule. A fresh reviewer then checks
the whole frozen bundle. Keep representation adoption, Lean implementation,
`force_plan_formation`, `force_context_projection`, Call S/C, Call A/B and the
full parent OPEN.
