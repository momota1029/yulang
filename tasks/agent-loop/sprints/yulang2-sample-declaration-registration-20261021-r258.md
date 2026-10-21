# R258 — connect sample syntax to declaration registration

Status: primary-only read-only source result; no independent review.
Parent: Authoritative R149 Types/Console outcome. Parent Simple-sub/evaluator
A/B, R70/R71, source/native, soundness, principality and production remain OPEN.

## Exact input and source owners

Y2 baseline is commit `a58eefc31e22141574b6f20c6a5748151c6d79f1`. Reuse R257's
Web-to-WASM-to-root-source route and the exact Types/Console sample hashes.
Reuse R154's independently reviewed generic ModuleTable insertion/query
relation only within its fixed-table premise. New inspected Y2 owners:

| Path | Blob | Role |
|---|---|---|
| `crates/infer/src/syntax.rs` | `5d511c71322d6af4fdc18378fdc2dbf65c94f1fd` | Binding pattern/name/body accessors; pattern head and binding-name collection. |
| `crates/infer/src/lowering/expr_syntax.rs` | `3f12b017e52a9e85d00c6ed6ba52a1153e9f2137` | Binding argument-pattern and lowering body accessors. |
| `crates/parser/src/pat/parse.rs` | `b8161b6f6b0ea2e9a37545f664485be33ae6aa67` | Applies adjacent pattern atoms through `ApplyML`, and parses parenthesized patterns. |
| `crates/parser/src/pat/scan.rs` | `9e0688e7fc8b22a054d801342854e41b3b541dfe` | Classifies an adjacent identifier as an ML-application pattern argument. |
| `crates/infer/src/module_map/mod.rs` | `0e20fedcfef410b647b3fc90e70afa3fc0cb73e6` | R154-reviewed source root traversal, Binding registration, root-expression owner path. |
| `crates/infer/src/module_map/finish.rs` | `d7f12816d99d1e410daf2fc7323598082ba39a33` | R154-reviewed registration completion and ModuleTable insertion callers. |
| `crates/infer/src/module_table/mod.rs` | `1b54bd6c9335fbaa1f8b56de9b5014f3d0d17558` | R154-reviewed generic value insertion and identity/order storage. |
| `crates/infer/src/module_table/query.rs` | `0fccad0f84d53e5271bfec126703ad460f92d394` | R154-reviewed declaration vectors and projections. |

No other source owners, tests, builds, or executions are in scope.

## Bounded source result

`parse_binding_stmt` constructs a `Binding` with `BindingHeader` and
`BindingBody`; adjacent pattern atoms are nested under `ApplyML`. For the
Types source, the `our id x = x` header therefore contains an ML-application
pattern. `binding_value_names` recognizes `ApplyML` and returns the pattern
head, so its module value name is `id`; `binding_arg_patterns` extracts the
argument pattern `x`. For simple headers `answer`, `name`, and `pair`, the
name collector returns the respective single identifier. `binding_body_expr`
selects a child expression/block from `BindingBody`.

The source module-map root traversal visits direct CST children in order.
Each `Binding` goes through `register_binding_values`: for every extracted
name it allocates a `DefId`, constructs a `Def::Let`, calls
`insert_value_with_span`, and appends that DefId to the block's child list.
Each direct `Expr` follows a separate root-expression path. Therefore, on the
successful parse/root-traversal path, Types contributes binding names in source
order `id`, `answer`, `name`, `pair` plus its final `pair.say` root expression;
Console contributes two root expressions, in source order. This connects the
unchanged source forms to the generic R154 registration mechanism.

## Limits and remaining premises

The result is conditional on the pinned sample strings successfully producing
the described CST and the root module-map route consuming it. It does not
establish successful body lowering, Evaluation Value/Computation for any
sample definition, the absolute ModuleOrder values after implicit imports,
the complete imported-library declaration census, composed root order, cycle
behavior, successful specialization, or sample-specific Request reachability.
Fresh DefId numeric values are runtime allocations; this static result
identifies declaration names and allocation sites, not observed IDs.

R154's generic registration relation does not by itself prove this sample
instantiation. R152 constructor facts remain conditional at their stated
premises. R149 and the parent theorem/production gates remain OPEN. No code
changes, tests, builds, executions, or expected-output edits were made.
