# R258 — Y2 sample declaration registration bridge

Status: primary-only source result; not independently reviewed.

The pinned parser represents a binding as `BindingHeader` plus
`BindingBody`; an adjacent identifier pattern such as `id x` uses `ApplyML`.
The Y2 `binding_value_names` helper consequently selects `id` as the module
value name, while `binding_arg_patterns` extracts `x`. Simple sample headers
produce `answer`, `name`, and `pair` directly.

The root module-map traversal preserves direct CST child order. Each Binding
allocates a `DefId` and registers it through `insert_value_with_span`; each
root Expr follows a distinct expression-owner path. Conditional on successful
parse and root traversal, Types has the four named bindings in source order
followed by the `pair.say` expression root; Console has its two expression
roots in source order.

This joins the sample syntax to declaration allocation and the R154 generic
registration relation. It does not prove runtime Evaluation classification,
absolute ModuleOrder, the complete library census/root composition,
specialization, or Request reachability. Exact source blobs and qualifications
are in `tasks/agent-loop/sprints/yulang2-sample-declaration-registration-20261021-r258.md`.
