# R347 source-census supplement — K0 Value-Lambda rows

Status: **frozen primary-owned supplement 1 for R347 contract revision 2**. This supplements, but does not replace or mutate, the frozen contract and census below. It is source evidence and an owner map, not a proof of projected solution equality, a test result, or a compiler defect.

## Exact dependencies and reason for this supplement

- R347 rev2 contract: `tasks/agent-loop/sprints/r347-k0-end-state-adequacy-20261023-r2.md`, SHA-256 `3ff5884ffefb9dca31f5433b68af56f3c6f172feab2284c1c80235dbfbe7ac5b`.
- R347 rev2 source census: `notes/theory/2026-10-23-r347-k0-end-state-source-census-r2.md`, SHA-256 `f40856702e43bcf4b990e980bee841292b792c372c7ba99dea1c6ea10b87eb7f`.
- R341 retention proof: `notes/theory/2026-10-23-r341-k0-source-constraint-retention.md`, SHA-256 `f8607d11c417734c1a7fb5aafe1af7ca78a587c5f5e7189c8cf3dcbc2064343f`.
- R341 source-retention census: `notes/theory/2026-10-23-r341-k0-source-retention-census.md`, SHA-256 `729c224785d42ee3577351e6a001668fe97a17fb2323aa532f52bbc8a1be0eeb`.
- Newest governing whole-language semantics: `docs/yulang-whole-language-semantics-ja (1).tex`, SHA-256 `28dc9b7fcb818e99a9513054d5847274ccce0d816a8c4a9644b802f0aa3fbd65`.

R341 already enumerates the K0 Value-Lambda formulas and identifies its two entry/return Effect rows as coordinates used by the actual Lambda recipe. Rev2 added the direct recipe/admission owners, but its new source trace did not spell out this Lambda row path and the obligation R347 inherits for projection/lifting. This supplement fills that census detail without changing `C_s`, the source domain, theorem, source pins, lanes, exact leases, or budget. If exact source inspection shows that these formulas are absent from the frozen R341 `C_s`, that is a mathematical scope failure and must be reported; do not amend `C_s` to fit the implementation.

## Pinned source path

The authentic K0 constructor is the annotation-free, single-binder Value-Lambda of R336/R341. Its source recipe path is:

1. `candidate_source.rs:2050–2070` visits `LocalSourceForm::Lambda`, records a `LambdaRecipe` containing the source occurrence, formal registration, parameter position, body Value/Effect endpoints, Lambda root component and source-action insertion point, then schedules `Action::Lambda` after collected source facts. For a Value-role formal the collector counts three facts: slot 2's Function-to-root Value inequality and Effect slots 3 and 4.
2. The source action dispatcher at `candidate_source.rs:2439` clones the retained recipe and calls `lib.rs::admit_lambda_fact` once. The enclosing ordered driver advances only after the action returns successfully. The actual one-pass source schedule and SCC/post-SCC order are already pinned in the rev2 contract and census.
3. `initialize_candidate_source_levels` at `candidate_source.rs:2250–2285` validates the formal-to-parameter recipe and installs its positive native Value root. It allocates a registered entry Effect row only for `FormalRole::Computation`; K0 Value-Lambda has role `Value`, so that setup path allocates no entry row.
4. In the contracted graph-enabled candidate run, `lib.rs::admit_lambda_fact` at `lib.rs:11557–11700` obtains the formal's negative Value port, the body result's positive Value port, and the body Effect row. It allocates two distinct fresh Effect coordinates at the formal's level: `entry` and `returned`. The Function term uses negative `entry` and positive `returned` ports. It records and admits the following occurrence-indexed formulas:

| Source occurrence slot | Formula | Relevant actual native coordinates |
| --- | --- | --- |
| `2` | `Function(formal, entry, returned, body-result) ≤ Lambda-root` | formal Value row; `entry` and `returned` Effect rows; body result Value row; Lambda-root Value row |
| `3` | `entry ≤ returned` | the same fresh `entry` and `returned` Effect rows |
| `4` | `body-effect ≤ returned` | body Effect component row and the same fresh `returned` row |

The signed ports are intentional: the Function reads the negative entry and positive return views, while direct Effect occurrences read positive lower and negative upper views. The proof must preserve their shared row identities and all three formulas; it cannot replace these rows by empty/bottom or infer purity from an uninstantiated callback.

`candidate_graph_enabled()` at `lib.rs:13520–13528` gates this allocation path. The proof must discharge that the authentic R347 ordinary candidate execution is in this graph-enabled mode. The non-graph fallback `(empty-effect, body-effect)` is not evidence for the graph-enabled formulas and must not be conflated with them.

## Projection and bounded exclusions

R341 retention proof §7 gives the construction map `ι`: Lambda entry and return Effects map to the two rows allocated by that occurrence and read by the exact negative-entry and positive-return Function ports. It includes both rows in `D_s = FV(C_s)` because they occur inside the source Function term and direct Effect inequalities. The R347 extension therefore preserves an arbitrary `C_s` assignment on both rows through its kind-preserving map `μ`; it must then show that the final native state satisfies every corresponding `H₀(S)` clause. Do not use allocator order or raw `u32` equality as the map. These are active constrained source-support rows, not unused native complements.

The following neighboring code branches are outside the frozen K0 source domain and do not add rows/formulas to `C_s` for this packet:

- effect-annotated Computation formals, including a registered entry row from `initialize_candidate_source_levels`;
- `FormalNameEffect` and `FormalEntry` source actions for those Computation formals;
- record-pattern default Effect occurrences in wide slots;
- any other structured parameter, annotation, or non-K0 Lambda form excluded by R336/R341.

If any such branch is reachable from the exact R347 `ValidK0` source domain, return its constructor and source path as a domain-boundary finding. Do not fold it into the Value-Lambda proof or silently widen the theorem.

No tests, builds, Cargo commands, or executable probes were run. This supplement records static source inspection only and supplies no closure of R347's lifting theorem.
