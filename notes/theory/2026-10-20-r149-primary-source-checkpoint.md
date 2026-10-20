# R149 primary source checkpoint: root production to runtime consumption

Status: provisional source-owner evidence; independent review pending. This note
is a Luna-primary checkpoint under R149 rev9. It does not establish a complete
initializer census/order, role-selection correspondence, or any parent theorem.

## Scope and oracle

Goal remains proof-backed inference/evaluation for unchanged Yulang2 Web examples
as broadly as practical. The pinned Types and Console examples are the current
finite target, not the ceiling. Oracle: Yulang2 commit
`a58eefc31e22141574b6f20c6a5748151c6d79f1`; baseline Y3 commit
`b7b320d0516208ab4f6aeac14b795f99c6f92cce`, tree
`7c2f1f06f1f1f6719e5a88a8854a04f98a7774e7`.

I inspected immutable Git objects only; the dirty oracle worktree was not read.
The source-worker message is preserved as a provisional lead. Its `body/tail.rs`
locator does not exist at this commit, so I do not rely on that claim.

## Verified construction and consumer facts

- `crates/infer/src/module_map/mod.rs`
  (`0e20fedcfef410b647b3fc90e70afa3fc0cb73e6`), lines 1818–1824 sorts the
  `LoadedFileCst` collection by module-path depth and then module-path key.
  `by_depth()` at 1833–1835 returns that stored vector. The main body-lowering
  loop in `crates/infer/src/lowering/body/mod.rs`
  (`f33bdfb5525ddcee02eba9bcd8c181acd1f9ea99`), lines 726–753 constructs that
  collection and lowers each file in `by_depth()` order. This is a compilation /
  body-lowering order fact; it alone does not establish the complete runtime
  initializer schedule or how cycles affect evaluation.
- `crates/infer/src/lowering/body/methods.rs`
  (`086d42bc63f1c12414a42898671dda22c8ac1084`), lines 358–399 commits a
  provisional binding, derives `BindingFetch` from its evaluation, and appends
  `RuntimeRoot::ComputedDef(def)` only when `fetch.runs_computation()` and
  `publish_runtime_root` are both true. This is an actual root producer and
  disproves any rule that every loaded source file automatically becomes an
  initializer.
- `crates/infer/src/lowering/body/mod.rs`, lines 2525–2536 lowers a binding
  body and wraps a `nullfix` body in `thunk_computation` before finishing the
  binding. This does not classify all imported definitions or prove when each
  thunk is forced.
- `crates/specialize/src/lib_support/specializer.rs`
  (`4dfffee1d68b89ea311dd9218bd56d8ab75a42d5`), lines 55–70 transforms a
  `RuntimeRoot::ComputedDef(def)` into `Root::EvalInstance` via
  `ensure_def_instance`. This bridges root identity into the runtime program;
  it does not prove that no roots were omitted upstream.
- `crates/mono-runtime/src/runtime/engine.rs`
  (`d920a498c226383776ff265d5d8efddd06d06779`), lines 23–40 iterates
  `program.roots` in vector order, evaluates `EvalInstance`, resolves host
  requests, and omits those initializer values from returned expression results.
  Lines 67–92 return cached successful instance values and reject recursive
  re-entry; the cache is populated only after evaluation succeeds.

The five owner blob IDs above were independently checked with `git rev-parse`
against the pinned oracle commit. No build or test was run.

## What follows and what remains open

These owners establish a concrete pipeline from a conditionally emitted
computation root, through specialization, to serial runtime root consumption
and successful-value caching. They also show that loaded-file order and runtime
root order are distinct evidence questions. The example's exact initializer
set/order remains UNKNOWN: every imported computation must be classified, root
publication/filtering and module composition must be traced across the full
pinned closure, and cycles/forward demands must be matched to the runtime
consumer. The `(depth, module path)` collection order cannot substitute for that
trace.

The Add/Display side also remains open at the selector boundary. Rev5 pins the
40-file source-resolution closure and ten loader/schedule owners, and rev8's
compiler review independently checked those blobs. This checkpoint does not
establish the complete visible candidate inventory, role prerequisites,
selected implementation identities, or the source-to-Y3 selector carrier. The
required sample primitive leaves remain `int_add`, `int_to_string`, and
`string_concat`, but sufficiency for all required initializers is unproved.

Y3's `SemanticImports` remains opaque correspondence evidence; the playground
constructs a local schedule without authenticated imported-initializer
composition. Therefore there is still no safe compiler-code slice under the
current activation gate. Simple-sub/evaluator A/B, R70/R71, source/native
generality, soundness, principality, and production admission remain OPEN.

Falsifiers include any omitted initializer changing schedule/output, any omitted
candidate or prerequisite changing acceptance or selected identity, or a source
root whose runtime behavior is absent from the proposed Y3 carriers. This
checkpoint is useful owner evidence, not theorem closure or permission to narrow
the broader sample-compatibility goal.
