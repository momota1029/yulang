# R185 representation-design handoff

Assignment: `source-history-and-option-b-representation-20261021-r185`,
contract revision 1, SHA-256
`d1323554eaf8809e6f65c27df2592fea49ffeb3b557f4070beb050e9cef7b997`.

Parent goal: proof-backed inference/evaluator and broad unchanged Yulang2 Web
sample support. R183 parent theorem and `R183-FRONTIER-COVERAGE-1` remain OPEN.
R183 proof note SHA-256
`0fe3afdc4ddfd1d3b8979bf34497e395bef06836a199cb6735a39eb84c43a28d`; R184 map
was reviewed with a MAJOR exact-path finding. R147 rev2 Option B is provisional
under the R183-recorded user-direction interpretation.

## R184 finding applied

R184 reviewer `/root/r184_owner_map_final_review` identified an actionable
major omission. This design names `tools/inference-playground/src/runtime/receiving.rs`
as the missing runtime continuation/view owner and distinguishes it from the
already pinned `tools/inference-playground/src/lib.rs::execute`, which owns
selected-definition scheduling and scalar/runtime-value formatting. The
candidate graph output helper `src/render.rs` is a third, separate owner.

## Result

The complete current-to-required constructor/consumer map is in
`notes/design/2026-10-21-r185-option-b-representation.md`.

- No sequence or general record expression constructor exists in the pinned
  HIR/type/runtime representations.
- A future sequence must preserve item identity/order, branch result, each
  item's effect, and next-item state across receiving-view continuation/replay.
- A future record must preserve source fields/spread occurrences and define
  type/runtime construction, access, merge and output. R147's broad shape intent
  does not settle duplicate fields, override order, missing lookup or rendering;
  do not invent those rules.
- Existing `if` no-else semantics produce Unit; preserve them.
- Required future Web regression is the unchanged fixture with
  `countdown_result -> 8`, retaining every current smoke expectation.

## Missing evidence and next step

This design does not establish exhaustive ownership across all source/solver
consumers, and does not close R183's theorem. Any source owner outside the
45-blob manifest requires a sequential manifest revision. Record semantics
must be cited from approved text or sent for a narrow decision before code.
The exact implementation path needs its own complete contract, CLEAN review and
Luna activation. No code authority follows from this handoff.

The concurrent R185 proof lane independently surfaced a precise source-history
dependency request: pin `crates/yu-solver/src/shadow_apply.rs::admit_candidate_fact`
for actual Apply construction/admission and
`crates/yu-solver/src/candidate_call.rs` for the reported Formal/Name/native
carrier supplier. Both are outside the 45-blob R185 rev1 manifest; neither was
read under this lane. Treat the latter owner description as a candidate until
its committed definition is reviewed under a sequential manifest revision.

The proof note froze at SHA-256
`8e102bfa1badaba2578eaef3cf6e76100d52bdb9b312b22e2368dbc570c47161`; it
excludes one completed qualifying negative-extrusion selective-lowering
attack, but does not establish universal frontier coverage or close the parent.

Outcome: design candidate only; no compiler writes, tests, builds, probes,
sample execution or Yulang2 external worktree inspection. Luna owns both design
outputs; R185 producer proof remains a separate lane. No independent review of
this design has yet run.
