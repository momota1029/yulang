# Sprint R240 — Direct-Name source/use correspondence

Status: ACTIVE_PROOF_SOURCE_AUDIT; Luna sole primary. No child workers.
Baseline: `8998cb1c5` (`research/simple-sub-intrusion`), after R239 partial freeze.

## Parent and fixed outcome

Parent: `notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1, 6–7, SHA-256 `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`. Preserve its one shared assignment, original formals, arbitrary finite chain length, repeated calls, simultaneous entries and finite-prefix quantifiers.

R239 established restoration/admission/emission for each bound already present in a captured provider graph. Its frozen candidate is `notes/theory/2026-10-21-r239-parent-instance-admission.md`, SHA-256 `8ecb68feb9177a78af6f5cfb47faa161081ee13bf27376c490c52caf96a9769f`; R239 contract SHA-256 `d638d4c2445d575619cf4e56033ab7b1c01a972637cd5dc1f10e65419250e8cf`.

Establish the direct-Name provider base case's capture completeness and authentic use-to-Function correspondence. Starting at the source provider Lambda and one actual Module `DefinitionUse` or retained Local occurrence, identify the original `e_t`, `e_n`, `e_R`, provider graph root/frontier, actual compared Function, and per-use `mu_i`. Prove where each of the three required directed bounds enters the captured graph, or how it is preserved through an explicitly licensed shared anchor; then apply R239's conditional admission chain to the same authentic FreshUse map and actual Apply argument/output endpoints. Keep Module and Local routes distinct; include rollback/resumption only for selected routes that use them.

Success is either (a) a source-parametrized certificate for all three directed bounds, source/use identity, successful restoration/activation and actual comparison, or (b) the earliest exact failed graph/root/anchor/occurrence join and its falsifier. Apply any certificate to parent §6 immediately. This remains a base case; R71/R72 and the whole forwarding induction remain OPEN unless directly discharged. Do not assume R71/R72's canonical-child path is needed.

## Method and falsifiers

Use a graph-reachability/frontier proof over the actual `capture_candidate_graph_inner` and `Capture::expand_row` constructors. Classify every parent-required inequality as reached through a local row or preserved through a shared nonlocal anchor. Trace source planner ordering and completed source drains into provider root and graph capture; then follow one authentic retained `FreshUse`, its maps, R239 exact admission/emission, and actual Function port dispatch/Apply endpoints.

Falsify a proposed certificate if a required inequality lies outside the reached graph with no licensed shared-anchor realization, capture precedes its source admission, the compared Function belongs to a different use/map, rollback prevents publication, or the actual argument/RE/output endpoints do not match that map. RelationId, BoundKey, endpoint equality, and diagnostic unresolved flags alone prove no source/use correspondence.

## Lanes, leases, limits

Serial Luna proof/source lane; no children or Astra. No code edits, tests, builds or samples. Implementation remains `NO_SAFE_CODE_SLICE`; an executable observer would require a later versioned proposal with discriminating inputs and falsifier. No semantic changes or production authority.

Exact write leases:
- `tasks/agent-loop/sprints/simple-sub-source-instance-correspondence-20261021-r240.md`
- `notes/theory/2026-10-21-r240-source-instance-correspondence.md`
- `tasks/agent-loop/current.json`

Resource cap: 900 seconds, serial; no R239 carryover. Freeze on a decisive source/use join, exact missing supplier, authority/dependency/lease change, substantive result, or budget boundary. Fresh independent review is required for any claim promoted beyond candidate. Validate and integrate only coherent leased paths.

## Direct dependency pins

```text
8ecb68feb9177a78af6f5cfb47faa161081ee13bf27376c490c52caf96a9769f  notes/theory/2026-10-21-r239-parent-instance-admission.md
d638d4c2445d575619cf4e56033ab7b1c01a972637cd5dc1f10e65419250e8cf  tasks/agent-loop/sprints/simple-sub-parent-instance-admission-20261021-r239.md
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md (§§1,6–7)
5185481127cb619d66d49025c0a20ee7d829bc1e7a46072a05adecf4d22aa891  crates/yu-solver/src/candidate_extrusion.rs
90665143f127394316b950d039fc498d460ac680df20b2387911a2fbdcaaeee1  crates/yu-solver/src/candidate_context.rs
45324aaec3825b1bf5cb15811ce309b8ff2dc020d5882383c0ed33d9d0b779f8  crates/yu-solver/src/candidate_effect.rs
135b72655d948d5035b21eaddce9fbeb0260c49bc3093e4bf2df73b03d88c4a1  crates/yu-solver/src/candidate_scheme.rs
90ed01915688b9c13c95593ddce296e7e3702a623e23dd4b9255d718b380a599  crates/yu-solver/src/candidate_source.rs
50ad99c3afabb12816e9ec17fe50372bac758964699519d9ce6f1fc1f6649599  crates/yu-solver/src/shadow_apply.rs
285a39449360b050d7689f9e52f400b821e651ec9ce300bd14a1a3d9a9ab8b64  crates/yu-solver/src/lib.rs
```
