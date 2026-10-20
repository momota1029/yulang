# R166 selected-definition completion simulation

Status: frozen revision 1; bounded source/diff simulation, pending fresh independent review.

## Scope and exact change

Contract: `tasks/agent-loop/sprints/native-consumer-lineage-and-runtime-completion-20261020-r166.md`, SHA-256 `8f6515154a1f89038a5b7c4850c68c8e74967d8daab9972c932188fe9cfd8512`.
Baseline commit: `dbdf179986ac80608347dfc72c95d90b5ab9dfb7`.
Before hash of `tools/inference-playground/src/runtime/machine.rs`: `4fb918732047f61184bc8f89b829bde68a8d1e6649a24d02640ec14500ae0acd`.
After hash: `875213902660c06ffa393c8fef001c4e67d229486fed6ef8773c6abd9a3b23f1`.

The only code edit extracts the terminal selected-definition branch of `Machine::begin_root` into private `Machine::complete_selected_definition(next_ordinal)`. The caller passes the same exhausted schedule ordinal. The helper retains the same selected-cell test, completion result, initialization marker, `Frame::Root` fields and initializer `Code`/environment. No other code or files under the runtime source were changed by this lane.

## Transition correspondence

Let `S` be the complete machine state immediately after `begin_root`'s existing loop finds no root at ordinal `n`, with `current_owner == ModuleRun`. The old terminal transition is a deterministic function `T(S,n)` with two exhaustive cases over the selected cell:

1. `cells[selected] = Some(value)` sets `state = Stopped(Completed(value.value))`; it does not mutate the frame stack, initialization markers, caches, executions, owners, continuations or source data.
2. `cells[selected] = None` inserts `selected` into `initializing_globals`, pushes `Frame::Root { next: n, cell: selected }`, and sets `state = Evaluate { code: definitions[selected].body, environment: 0 }`.

After extraction, schedule traversal invokes `complete_selected_definition(n)` and performs precisely that same branch body. The helper performs no other reads or writes. Thus, for each valid `S,n`, the post-state in both cases is fieldwise identical. The call boundary itself does not persist in `Machine`; there is no intervening suspension, callback, allocation, or effectful operation between the exhausted-loop return and the helper transition.

All nonterminal schedule behavior is byte-unchanged: root lookup and ordinal increment, cached scheduled-definition skip, initialization marking, root/expression frame construction, selected code, environment and early return. The ownership guard remains before the loop and helper call. Consequently a mismatched owner still produces the same unavailable state without invoking selected completion.

The argument is source-level simulation of the extracted branch, not a checked proof artifact and not execution evidence. It covers schedule exhaustion with an already materialized selected cell and fallback evaluation. It does not establish schedule completeness, initialization order for a whole module, a module completion target, any new source classification, or Yulang2 sample compatibility.

## Review boundary and checks

Exact leased code file only: `tools/inference-playground/src/runtime/machine.rs`. `program.rs` is unchanged and its pinned SHA-256 remains `28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d`. The static diff has one extracted branch and no other machine transitions. No tests, builds, probes, compiler/sample/runtime executions or Yulang2 activity occurred, as required by the contract.

The remaining module-execution obligation is to derive a complete initializer schedule from source-owned computation/publication classification, including the admitted Case gap and imported module identities, then design an honest module-level completion result. This refactor alone enables no new entrypoint and changes no observable behavior. Parent inference/evaluator/sample gates remain OPEN.

Writer: Luna primary; no coauthors. Independent source/diff review pending. No commit/push by a worker; primary owns integration.
