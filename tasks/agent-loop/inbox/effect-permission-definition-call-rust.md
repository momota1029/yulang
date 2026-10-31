# Rust source-route handoff — EFFECT-PERMISSION-DEFINITION-CALL-BRIDGE/r1

Handoff revision: 1  
Assignment: `/root/effect_permission_definition_call_rust`  
Contract: `tasks/agent-loop/sprints/effect-permission-definition-call-bridge-20261028-r1.md`  
Contract SHA-256: `940a4b7737c5cbca80a0019ec5d2b8fd466bf55255e01669dc6b91adb236d3fe`  
Parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1, 3, 5; original effect-hygiene consumer remains open.  
Role/model requested: Luna / `gpt-6-luna`, high. Observed model/effort: UNKNOWN.  
Worker state: STOPPED after this handoff; source audit only.

## Outcome and provenance gate

Outcome class: **source-native evidence of the supported owner path plus exact unsupported edge**. No implementation was produced. **`DELTA_AUTH_UNRESOLVED`; `NO_SAFE_CODE_SLICE`.**

The contract-pinned source inputs rehash exactly:

| Path | SHA-256 |
|---|---|
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `crates/yu-solver/src/candidate_effect.rs` | `1715046b29b760fe70b3c2fb05665dad23e7f95ad05883c39d06d4da37b925ab` |
| `crates/yu-solver/src/candidate_scheme.rs` | `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707` |
| `crates/yu-solver/src/shadow_apply.rs` | `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `notes/theory/lean/YulangClosure/FormalPermissionAuthenticatedSiteExport.lean` | `d6fc3e11f26350f6cf03d7afc248500778e3bf4a8ee816582630aa5f5feeeb84` |

The current `candidate_effect.rs` bytes are `1715046b…`; the required predecessor bytes are `6f20ac00deb2f5a84f57a0cf54cf9ceb64f2de5a90d15cc371240d9de68dfa3b`. The predecessor is not authenticated. Luna's admitted provenance search covered the relevant `/tmp` copies and all 66 Git revisions and found no exact predecessor. I preserved the current overlay and did not attempt a reverse patch or rollback. Because provenance is the first admission gate, no candidate-source edit or instrumentation is a safe slice, even though other pinned owners can be traced read-only.

## Typed owner route and exact gap

The following are construction and routing facts from the pinned source, not a theorem that a source contribution reaches the returned computation.

1. **Provider input and module Definition.** `candidate_source.rs::emit_candidate_source` validates a `SourceReceiver::Definition` against the matching definition/root and walks that local source. A `Name` resolved as `ModuleDef(target)` emits a `PendingDefinitionUse { parent, target, occurrence }` and an `Action::Module`. At execution, the action constructs the occurrence-keyed `DefinitionUseId` and chooses `route_candidate_open_use` for an active recursive use or `route_incoming` otherwise. `candidate_scheme.rs::route_candidate_graph` captures the target's live root; `instantiate_candidate_graph` freshens that graph and routes the fresh lower endpoint to the use's distinct `use_value_component`. This is the module-definition/use boundary. It is not an equality between a recursive call's result and its argument.

2. **Call callee, argument, result, and effects.** For each source `Apply`, `candidate_source.rs` retains a `CandidateRelation::Apply` with distinct `callee`, `argument`, `result`, `callee_effect`, `argument_effect`, and `result_effect` endpoints, and a corresponding `ApplySourceInput`. `shadow_apply.rs` turns it into a negative function demand with the argument value/effect and result value; in candidate-graph mode it allocates a separate invocation row and relates that row to the application result effect. The endpoints remain separately represented. The source constructor itself supplies no provider-to-result identity equation.

3. **Tuple result and case-pattern projection.** For the fixture's tuple case, `candidate_source.rs::Work::CaseArms` stores `CandidateRelation::TuplePattern { scrutinee, elements, ... }`; `shadow_apply.rs` validates the owned source pattern and constrains the positive scrutinee against a negative tuple whose binder positions are distinct component endpoints (wildcards use fresh negative values). A `CaseBinder` name resolves to its component endpoint. This types the projection from the *scrutinee*; it does not establish that the recursive module call's result tuple contains the provider callback supplied as its argument.

4. **Effect extraction.** `CandidateGraphNode::effect_operand` in `shadow_apply.rs` distinguishes `Contribution { effect, route, instance }`, `AnnotationMember` / `OperationInterfaceMember`, `PermissionView`, and `SupportView`; a raw effect-row endpoint has no such operand result. `CandidateGraphExport::formal_effect_permissions` follows a captured negative formal-permission path to an effect-row port and returns the declared permitted labels. The method documents that this is a structural observation, not certification that a source typing rule admitted the operand. `candidate_effect.rs::candidate_check_effect_operand` expands a `Support` into its allowed members and optional tail; it does not by itself identify an actual source contribution or handler subtraction. Thus exported permission/support metadata cannot fill the source/provider gap.

**First unsupported transition:** for the exact fixture, there is no source-owner derivation here that takes the provider callback inside the argument tuple, follows module-level `f`'s recursive `DefinitionUse`/`Call`, and identifies that same provider or same contribution at the tuple component bound to `left` and then at `answer`'s returned computation extraction. The constructions above preserve separate typed endpoints but do not prove the required fixed-identity composition. The consumer-residual Rust handoff and independent review agree that the local-self-recursion design does not settle this module-level route. A same-contribution extraction interpretation remains separately open. The fixture has no Catch/handler; this handoff makes **no subtraction claim**.

## Prior evidence reused or rejected

- Reused as the exact unresolved premise and prior implementation history: `tasks/agent-loop/history/effect-permission-consumer-residual-20261028-r1-outcome.md` (SHA `570f6df0b10886d248a4214a3671e8a23e143a7e6270e4d19cb43b457b1ba9d2`), its Rust handoff (`c873113f179634be7f9e29e90eea95f717bd50f4ceb314c239379e488ce8b1fe`), proof handoff (`7437b723ac103af620dd35dd348ec78fbd82c176eb9893b4acf0578da9b817db`), and independent review (`505463444165018764e3b4680b58a624f43da7eeeccd2db6489d6ed4d5088691`). The review rejects the earlier “fixture expectation defect” classification and retains only the missing provider/source and extraction bridge.
- Reused only for source navigation: prior authenticated-site-export proof/source handoffs and review, plus the pinned `FormalPermissionAuthenticatedSiteExport.lean`. Their conditional export/decoder evidence does not identify a contribution flowing from this fixture's argument through the module Definition/Call result, nor establish returned-computation extraction.
- Rejected as closure evidence: the earlier test-only empty returned-effect census and failed Cargo assertion. They are bounded observation only; they do not prove a missing source effect, a solver defect, or a false protected expectation. The previously recorded conditional Lean declarations do not supply the source-owner bridge or unconditional residual theorem.

## Parent application, checks, and boundary

Parent application: retain the Definition/Call, Apply, tuple-projection and extraction gates as OPEN. No contribution identity is transported across those edges by this handoff. The unresolved premise owner remains Luna/source and the corresponding proof lane. Exact next evidence: source-owned module-level recursive Definition/Call correspondence for this fixture, with the callback/contribution identity fixed through result projection, followed by an extraction interpretation for that same identity. No semantics, source domain, fixture, diagnostic, or expected output changed.

Checks: read-only SHA-256 verification of the six pinned source/proof inputs above and inspection of the pinned constructors/consumers. No Cargo, test, Lean or compiler command ran. No generated or scratch paths were created. No other repository path was written; this handoff is the sole new path. No Git operation occurred.

The handoff is frozen at revision 1. Writes stopped; no descendants or running build processes. No independent review or self-certification is claimed. Mathematical parent, source/native, principality, termination, effect hygiene and production gates remain OPEN.
