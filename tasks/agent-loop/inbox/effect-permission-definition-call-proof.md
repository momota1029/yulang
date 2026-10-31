# Definition/Call bridge — proof handoff r1, frozen

Worker `/root/effect_permission_definition_call_proof`; contract SHA-256 `940a4b7737c5cbca80a0019ec5d2b8fd466bf55255e01669dc6b91adb236d3fe`; source baseline `bc2a0836ec`. Outcome: constructed-but-unchecked local constraint schema plus exact OPEN source/native bridge. No residual/no-loss theorem, source-qualified counterexample, independent review or production authority.

## Sources and authority boundary

Read root AGENTS, preserved operating map, sprint rules, compact state/README, assigned contract, Lean skill and both references, design-authority rule, Lean project pin/manifests/README, original parent §§1–3 and relevant §5 continuation, exact prior consumer handoffs/review, and only the five pinned Rust owners plus pinned `FormalPermissionAuthenticatedSiteExport.lean`. No new callee source was read. Original parent SHA-256: `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`.

Original A/B target in `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5 retains every supported original source program/history/extrusion occurrence, complete Call/effect hygiene/scopes and one shared source witness; it remains OPEN. Current birth-level correction and original H/annotation-permission corrections are located by the pinned prior proof handoff, not newly inspected under this source boundary. Its research manuscripts/receipts do not grant semantic authority. The module-level source typing authority is **not established by the available local HirLocalId rule**. Primary explicitly confirmed no broader source reads or execution; authority lookup beyond these pins needs its versioned amendment.

All SHA-256 pins independently matched: candidate_source `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`; candidate_effect `1715046b29b760fe70b3c2fb05665dad23e7f95ad05883c39d06d4da37b925ab`; candidate_scheme `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`; shadow_apply `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`; lib `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`; authenticated Lean export `d6fc3e11f26350f6cf03d7afc248500778e3bf4a8ee816582630aa5f5feeeb84`. Prior Rust/proof/review handoffs respectively `c873113f179634be7f9e29e90eea95f717bd50f4ceb314c239379e488ce8b1fe`, `7437b723ac103af620dd35dd348ec78fbd82c176eb9893b4acf0578da9b817db`, `505463444165018764e3b4680b58a624f43da7eeeccd2db6489d6ed4d5088691`.

## Typed source-owner trace and exact obstruction

| Constructor/owner | Supported direction and identity | Limit |
| --- | --- | --- |
| candidate_source:1785–1787 | ModuleDef target + original occurrence -> PendingDefinitionUse and Action::Module | Distinct from Local active_initializers/Action::Link at :1795–1800 |
| candidate_source:2490–2495; candidate_scheme:4184–4191 | Exact DefinitionUseId; active-use/parent/target roots checked; internal route_internal | No argument/result identification |
| lib:19179–19187; candidate_scheme:4193 onward | External incoming candidate route -> stored provider graph capture/fresh instantiation | Different route from internal open recursion |
| candidate_source:1869,1912–1924 | Apply retains callee/argument/result and distinct effect ports, source occurrence, checking/cause; Native initially None | Registration alone is not native Call/provenance acceptance |
| shadow_apply:4105–4176 | callee+ <= negative_function(argument+,argumentEffect+,invocationEffect-,result-); exact NativeInterface saved | Actual argument/result remain distinct; contribution propagation not concluded |
| shadow_apply:4227–4245 | calleeEffect+ <= applicationEffect-; invocationEffect+ <= applicationEffect- | Local constraint generation, not transitive no-loss |
| candidate_source:1995–2013; shadow_apply:4044–4054 | Positive tuple from actual argument element endpoints <= tuple result- | Builds the argument tuple |
| candidate_source:1459–1488; shadow_apply:4081–4104,4261 | Actual Call-result scrutinee+ <= negative tuple with actual pattern components; source/owner/slot checked | No direct Effect edge; wildcard gets a fresh negative row |
| candidate_effect:1394–1416 | Contribution retains effect, origin, allocation instance | Same family is insufficient identity |

**First unsupported parent premise:** authenticate the exact module-recursive `f pair = f pair` Definition use and complete source Call/provider derivation that connects the supplied callback's full contribution key to the Call-result component bound as `left`, then to `left 0`'s invocation. The inspected constructors distinguish argument and result and do not supply that identity edge. This is absence of derivation/evidence in this packet, not a theorem that no such source derivation exists or that divergence deletes effects. The next unread `candidate_call` owner is outside the pinned boundary; primary/source owner must amend and pin it before further inspection. Module-level semantic authority must also be identified by that owner.

After that premise, the solver owner must prove same-contribution transport through actual comparisons/tuple projections/fresh use/qualified copying, and the extraction owner must provide authentic computation-row membership/readout. No unconditional residual follows from publication/replay or Permission export. The exact fixture has no Catch/handler; no subtraction claim is made. Preserve original failure `consumer-returned-effect-forms=[]`, exit 101, as recorded by the pinned prior invocation, without reclassifying it as solver failure or a proved fixture defect. This packet did not execute or newly authenticate that invocation's raw receipts.

## Constructed Lean surface

Changed `notes/theory/lean/YulangClosure/FormalPermissionDefinitionCallBridge.lean`, SHA-256 **`cb582e65901d81429a0856e10b8b9223c736bcb148783393e1da270b5f597f4c`**. Imports only `Init`; no root import edit. Namespace `YulangClosure.FormalPermissionDefinitionCallBridge`.

Written statements below are source text, **not printed/checker-accepted types**:

- `effect_edge_target {Value Effect : Type} {call : ApplyPorts Value Effect} {lower upper : Effect} (edge : ApplyEffectEdge call lower upper) : upper = call.applicationEffect`.
- `effect_edge_source` with the same parameters/premise: `lower = call.calleeEffect ∨ lower = call.invocationEffect`.
- `substituted_target_rejected {Value Effect : Type} {call : ApplyPorts Value Effect} {lower foreign : Effect} (different : foreign ≠ call.applicationEffect) : ¬ ApplyEffectEdge call lower foreign`.

These are local two-constructor constraint projections, explicitly conditional on the schema and without any extracted native instance. They reject swapping a fixed recipe's join target. They do **not** furnish the required fixed-contribution provider/Call-result/projected-component substitution falsifier; that remains OPEN with the missing route.

`SameContributionExtraction` states, for a fixed complete `(effect, origin, allocationInstance)` key, graph owner and computation row: there exists an entry in an authentic Contribution-variant census with that owner and key, whose exact node is an Effect lower bound of that computation row. It is a **Prop definition with no instance or retention theorem**. `ContributionEntry` is partial readout of Contribution operands only. Support/Permission/Annotation/OperationInterface variants remain uninterpreted; no full extraction-completeness or smaller source-language closure is claimed. Source fixtures, accepted language cases and all parent quantifiers remain unchanged.

## Execution, evidence and resources

Actual static commands: focused `cat`, `sed`, `rg`, `ls`, `sha256sum`, and Python for a field-name edit; file creation via shell heredocs. Shell writes exited 0. Initial `ls` found both fresh leased outputs absent as expected; no construction failure was hidden. Forbidden-token search matched only prose mentioning an axiom audit; no `sorry`, `admit`, project axiom or checker bypass declaration was added.

Pin: `leanprover/lean4:v4.35.0`; lakefile `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`; manifest `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`; toolchain file `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`; no external packages in the read manifest.

Actual Lake/Lean versions: **NONE**. Lean/Lake/checker/Cargo invocations: **0**; execution seconds **0**; generated cache outputs **NONE**. Printed types: **NONE**. Full axiom audits for all three candidate theorem declarations: **NONE — NOT EXECUTED**. No invocation inventory/release was provided, so no execution was attempted. Static work wall/CPU/RSS was not independently instrumented; no numeric resource receipt is invented. Primary requested freeze at this finite boundary; no further work continues.

Changed paths: only the leased Lean file and this handoff. Scratch paths: **NONE**. No compiler, expected-output, dependency/configuration, question/status/index/Git writes; no children. Parent application stops at the source-provider-to-Call-result contribution premise; owner Luna's source/Rust/proof assignment. Kernel acceptance, native correspondence, independent review, and all parent/production gates remain OPEN.

**STOPPED / WRITES STOPPED.** No heavyweight process, descendant or cache writer exists from this leaf. Primary owns further checking, review, adjudication and integration.
