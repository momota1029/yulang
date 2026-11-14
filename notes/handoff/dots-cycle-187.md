# Cycle187 — current head extension with independent projection constraints

Start observed 2026-11-14T10:30:38Z, automation slot10:27:19Z. Conservative
publication/report deadline11:22UTC; user55-minute cap overrides older runtime
instructions. Fresh integration720ef126fee791d11774947b989a108ac98960d8,
standing-orders/inbox through I32 read. ACTIVE, no STOP. Prior186 final
cf362e7b71ccfdf65b2973588aa2f866d7e44b7b heartbeat completed and report present;
no prior build/writer. Retained local prior branch had different Git history:
failed merges were aborted, then cycle187 started from exact published tree.
No prior work was overwritten. The current integration is already its ancestor.

## Closed mechanism

**The historical-plan requirement is removed.** For an arbitrary checked,
reachable WF/V6 state and current candidate Frame, simultaneous current Models,
actual candidate HeadModels and centered inspection ProjectionModels have a
conservative extension satisfying the entire HeadEquations. Current Models,
actual HeadModels, centered projections and actual merge equations are retained.
The finite preserved set is old fullSources plus declared candidate capture
endpoints, not the entire assignment. Input site registration remains required;
the candidate plan need not have been installed before.

Main theorem: `GeneralNominalHeadBranchFrame187.head_models_extension`.
This is a model-construction helper for soundness, not completed general
soundness/completeness/principality. Prepared only supplies an existential branch
witness; simultaneous validity with current Models and centered projections is
still a genuine residual. Candidate new outputs, full Plan.Holds, generated
children and EvidenceNode remain open. Existing effect/live output preservation
is not equivalent to proving the new candidate's outputs.

Intermediate exact result: under recorded merges and a matching historical
plan, head extension exists iff every declared input's historical binder value
fits all current raw same-name capture intervals. This replaces the opaque
merged BoundsFit criterion with the actual raw interval criterion.

11 new proof modules, 47 public theorems. Their names, Japanese quantified
claims, side classification and 13-field definition inventory are in
`notes/design/2026-11-14-cycle187-claims-ja.md`. Complete public types and axioms
are in `lean/Audit/Cycle187FrameTypes.lean` and the reproduction log.

## Verification

`timeout 240s bash notes/verification/cycle187/reproduce.sh`: PASS, exit0.
Full command output: `notes/verification/cycle187/frame-reproduce.txt`.
- Focused `lake build --wfail` of HeadBranchFrame187 and HeadDeclaredBounds187:
  PASS,1036 jobs (cached dependencies included). No unscoped full build.
- All11 new sources: `lake env lean --trust=0 -DwarningAsError=true`: PASS.
- Public type/axiom checks: PASS.
- All-declaration executable whitelist gate (including private/generated and
  definitions): PASS; only propext/Classical.choice/Quot.sound allowed.
- Preservation: PASS5515 old paths byte-exact except heartbeat replacement and
  append-only root imports. No existing Lean module, README, Audit root, spec,
  standing orders, inbox or lakefile changed.
- `git diff --check`: PASS.
- Independent read-only review: PASS; clarified that uninstalled plan does not
  mean unregistered input, and that a common model is still needed. No hidden
  HeadEquations premise or completeness claim.
- Full `verify-lean.sh`, full build, CI certification and new Yulang2 runtime
  tests were NOT run. Usage budget unknown. Disk remained50GB free of63GB.

Dependency traversal reports are in `notes/verification/cycle187/*reach*`.
General WF Exact/SaturationTotal/OrderIndependent roots reach no new declaration.
This explicitly prevents counting a helper as a newly closed B4 field. Current
V6 has no B4SkeletonV6 structure, so no invented14-field denominator. New general
field closures0. Existing upstream multi-tag generatedChildren obstruction was
not repaired, changed, or advertised as a new discovery.

## Checkpoints and failures

- Heartbeat4e97c8ea2b6678d576ebd69a98d65bdccc5e1112 published after local CLI
  push failed with missing GitHub username. App publication with expected-head
  lease succeeded without creating a new approval request.
- Checkpoint281e037384eba28be2f0b7d1ad0cc3671dd601ee: generic projection-to-merged
  Fits and historical raw criterion; fresh fetch and whole-tree equality PASS.
- Checkpointda5b81e8eb8adf8671c884dfce72611391a5c707: first-time candidate
  extension,91 declaration gate; fresh fetch and whole-tree equality PASS.
- Development compile/serialization errors and repairs are recorded in
  `notes/verification/cycle187/development-errors.md`, rather than hidden.
  The complete final reproduction is green. No semantic choice was made.

## Yulang2 comparison

Fresh work/dots-audit x-oracle was read before new definitions. X13 interval/shared
input notes and C3-PARENT are historical observations, not new runtime tests or a
proof of arbitrary interval stability. No known Yulang2 disagreement was silently
imported. The work changes no language semantics, merely proves properties of
existing inspection/allocation/Frame definitions.

## Next three real bridges

1. Derive a common assignment satisfying current Models, candidate HeadModels
   and centered ProjectionModels from actual selected/stable conditions.
2. Add new candidate output equations and child materialization while retaining
   current constraints. Existing outputs are already inside the preserved footprint.
3. Compose child evidence into the actual parent Evidence judgment after the
   upstream generation boundary is repaired. Do not weaken the target to make it pass.

Final publication details and measured finish time are appended below. Writer
stops after final remote-tree verification. This is one completed proof mechanism,
not completion of the full recurring research task.

## Final verification and release preparation

Strict gate checked118 declarations. Reach traversal loads117 cycle-attributed
constants: general roots0/117, local mechanism roots85/117. The one-count difference
was investigated: the gate import order attributes the lazily generated upstream
`GeneralNominalRecursiveInspection.bindings.eq_1` to this load, whereas the reach
script's additional WFTransfer import does not. The exact gate-name list is saved;
47 new public theorem count is unaffected. Neither denominator is a field count.

All47 signatures and all11 source hashes are saved. Final review of the branch
frame confirms prior effects/live outputs remain protected, but future unused
reserved output keys and the new candidate's output equations are not claimed.
Latest integration re-fetch remained720ef126f, an ancestor of the publication.
Final verification finished2026-11-14T10:56:40Z,26.0 minutes after observed start.
The added model-construction and branch-preservation mechanisms are verified;
remaining work requires the separate common-model/output/child bridges above.
Final publish is restricted to work/dots-main with expected-head lease.
