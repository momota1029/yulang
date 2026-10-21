# R240 — Direct-Name source/use correspondence

Status: partial capture/frontier result; unreviewed. Parent and R71/R72 remain OPEN.

## Fixed parent

The parent is `notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1, 6–7 (SHA-256 `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`). R239 showed a conditional FreshUse restoration/admission/emission route for each bound already in a captured graph. Its candidate SHA-256 is `8ecb68feb9177a78af6f5cfb47faa161081ee13bf27376c490c52caf96a9769f`.

## Source/use ordering

For a Module provider, there are two routes. After all member roots' candidate source actions complete, SCC processing captures and publishes each member graph; later incoming DefinitionUses route against their exact target roots. Their route records supply the use occurrence and `use_value_component`, and `instantiate_candidate_graph` links the fresh provider root to that receiving component. For these later incoming uses, capture follows the root actions.

Internal same-SCC Module uses take a live-root route, not a graph-capture route. SCC setup activates member roots and internal uses, then executes source action schedules. An active `Action::Module` calls `route_candidate_open_use`, which reaches `route_internal` and `route_internal_inner`; the latter constrains the live target-root value row against the use value row via `route`. It does not call `route_candidate_graph`, instantiate a graph, or create a FreshUse map. Thus the proposed stale captured graph does not exist on this path. The graph route through `route_candidate_graph` is used by `route_incoming_inner` for incoming uses. This distinction corrects the earlier stale-capture inference in this note; early internal routing alone establishes no source counterexample.

For a Local provider, `Action::Install` or `Action::LocalAnnotation` enters `PublishLocal`, installs the candidate local term, and only then advances the source action cursor. A later `Action::Local` identifies its slot and exact occurrence and captures that local scheme. A recursive local initializer name is a different route: while the initializer is active, the planner emits `Action::Link`, not `Action::Local`/FreshUse. Module and Local routes therefore remain distinct.

## Capture/frontier dichotomy

`Capture::expand_node` opens every encountered Function shape and interns its four children. `Capture::expand_row` exhaustively visits the retained direct row bounds and exact nonvariable bounds of a local row. `Capture::bound` enumerates the exact raw-key relation bucket, stores a `Graph::Bound` per relation, and snapshots that bound/relation's current evidence. Consequently, a parent-required inequality whose endpoints are reached through local rows enters the graph when its source bound is admitted before capture.

`Capture::row` classifies a row local exactly when it is above the capture boundary and not marked nongeneric. `expand_row` stops at a nonlocal row. `prepare_candidate_fresh_use` maps local generic rows above the boundary to fresh rows and leaves other rows at their current representative. Such a stopped row is a shared anchor: its existing source bound remains on the same row instead of being copied. This gives a constructor-level dichotomy for reached rows: local paths are traversed into captured bounds; nonlocal paths remain shared identities. It does not license replacing a missing source bound by an endpoint-equal row.

Combined with R239, this is conditional capture/admission evidence for the three direct-Name inequalities once their actual source constraints are attached at the reached provider ports before the relevant incoming graph capture. The source planner associates FormalNameEffect with the registered formal and Name occurrence, emits both equality directions, and Lambda slot 4 emits the body-to-RE direction. Ordinary Local publication precedes a later Local use; recursive initializer self-uses are `Action::Link`. Internal same-SCC Module use instead constrains a live shared root. The remaining issue is whether later source constraints/bounds on that target root propagate through an already admitted root-to-use-row route, and whether the resulting Function demand's AE/RE components match the actual Apply argument/output. No source-qualified counterexample was constructed.

## First unresolved join

The graph-to-`use_value_component` comparison is not yet the parent’s actual Apply comparison. This audit does not prove that the Function AE child reached by typed Function dispatch is the call’s actual argument effect `e_A`, or that its RE child is the call’s actual output demand `e_C`; nor does it join the next provider’s own map. The candidate Apply observation expressly leaves `ApplicationTypingRule`, `WholeArgumentProviderCompatibility`, `SourceTypingAndAdmission`, and `GeneralizationAndFreshUseCorrespondence` unresolved. These are evidence limits, not a finding that source typing is unsound.

Therefore the exact remaining premises are (1) incremental propagation from later provider-root constraints/bounds through an already admitted internal live-root route; and (2) an authenticated square from that source DefinitionUse/Local occurrence, through the live or captured provider route as appropriate, to the actual Apply AE/RE comparison and the next per-use map. Do not assign an incoming-use FreshUse map to the internal shared-root route. RelationIds, checking events, the graph root, or the DefinitionUse value link alone do not complete that square. R71/R72 remain OPEN; no evidence yet makes their canonical-child route necessary.

The frozen contract is `tasks/agent-loop/sprints/simple-sub-source-instance-correspondence-20261021-r240.md`, SHA-256 `2e4b0b7154047f1cedae6748d983d42b0896e503ba138aacf9100c2c94c96e99`. No implementation change, test, build, sample run, semantic change, or production claim is included.
