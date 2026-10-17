# Read lease amendment — NPAIR source correspondence

Sprint: `npair-source-admission-correspondence-20261018`, revision 1. This amendment keeps the fixed source-to-action outcome and adds only exact direct owners found while tracing the already leased `module.rs` and solver graph-plan call.

Primary read leases:

| Path | SHA-256 | Reason |
| --- | --- | --- |
| `crates/yu-hir/src/module/local_source.rs` | `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5` | HIR LocalSource construction and occurrence/parameter identity retention. |
| `crates/yu-hir/src/module/source_annotation.rs` | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` | Concrete and symbolic row parsing and retained annotation owner/position. |
| `crates/yu-hir/src/source_identity.rs` | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` | `HirSourceIdentity` storage for parse roots, definitions, occurrences and parameters. |
| `crates/yu-solver/src/candidate_value_graph.rs` | `8738c1b1699228b1a4dfd30af7e03d0afb100ca6124d23037c645246d888dc50` | Exact candidate value/owner graph input; it does not define the delegated graph-plan executor. |
| `crates/yu-solver/src/candidate_context.rs` | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` | Checked context owner; it does not define the delegated graph-plan executor or route wrapper. |
| `crates/yu-solver/src/candidate_scheme.rs` | `abe1eb6d6176c035d237c3f51f7ccfe99dea5224df20de285465c510c6c2a494` | Defines `execute_candidate_graph_plan` and `route_candidate_graph`; source-root schedules execute before graph capture and publication. |

The two HIR owner paths, then their directly referenced source-identity owner, were added as exact read-only paths before access. The candidate value graph and context owners were checked in the dispatcher-selected order; the existing owner map then supplied `candidate_scheme.rs` as the exact executor. Its source-root schedules run before the SCC graphs are captured and staged. No writes, builds or Astra allocation were added by this amendment. A further exact owner may be added only after its need is concretely located.
