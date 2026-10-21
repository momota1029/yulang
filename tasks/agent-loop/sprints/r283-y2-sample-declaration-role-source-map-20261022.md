# R283 — pin Yulang2 sample declarations and role-source owners

Status: ACTIVE_PREPARATION; primary-only, read-only source owner packet; no code lease.
Parent: the unchanged Yulang2 sample execution and proof-backed inference/evaluation goal; R149 Types/Console remain a small increment of that broader goal.
Baseline: `f703a5d90` on `research/simple-sub-intrusion`.
Oracle source: immutable Y2 commit `a58eefc31e22141574b6f20c6a5748151c6d79f1`; no dirty oracle worktree file was read.
Authority: R149 design/proof plan and rev10 preparation contract; R150 rev2 stays unactivated. R152 rev2 explicitly stopped its prior source leaf at unknown helper owners; this is a new primary sequential read-only pin, not a continuation of that leaf or a code authorization.

## Outcome

For the exact Types and Console templates, connect the visible source binding/role declarations to their Y2 syntax, declaration registration, body-lowering, and role-method registration owners. Identify the precise point where actual selected DefIds, initialized root order, and Y3 correspondence still require evidence. No execution, selected-role, output, theorem, or production claim is in scope.

## Pinned source owners

All blob IDs below are from the immutable oracle commit above:

- `web/playground/src/main.ts` — `e6bec9fe44d673ccbf98af078ef4562c9267ef6c`
- `crates/infer/src/syntax.rs` — `5d511c71322d6af4fdc18378fdc2dbf65c94f1fd`
- `crates/infer/src/lowering/expr_syntax.rs` — `3f12b017e52a9e85d00c6ed6ba52a1153e9f2137`
- `crates/infer/src/module_map/mod.rs` — `0e20fedcfef410b647b3fc90e70afa3fc0cb73e6`
- `crates/infer/src/lowering/body/mod.rs` — `f33bdfb5525ddcee02eba9bcd8c181acd1f9ea99`
- `crates/infer/src/lowering/body/role.rs` — `e2d8dd2b078422ee2a4d518becace64d84609628`
- `crates/infer/src/lowering/body/register.rs` — `b089ff2e17e87f1eea6e5b97835d372e73722b43`
- `crates/infer/src/lowering/body/impl_decl.rs` — `fb747e6db395981f9961f30dbf41e9ec6612347a`
- `lib/std/core/fmt.yu` — `fd7b6607094c9ad70bde1fd41890363fa8bd6b31`
- `lib/std/io/console.yu` — `8c8eabe69755d28bc66a850745f5ea72c136cd74`

## Observations and limits

- The pinned Types sample declares `id`, `answer`, `name`, and `pair`, then has the top-level expression `pair.say`. The Console sample has two top-level expressions: `println "hello from Yulang"` and `say: 1 + 2`. The exact sample hashes remain those in R149.
- `syntax.rs` derives a binding's module value names from its header pattern. It treats applied/type-annotated/field patterns as a single head binding; `binding_has_single_head_pattern` uses that same head recognizer. `expr_syntax.rs` extracts binding arguments and the body from CST children.
- `module_map/mod.rs::register_binding_values` allocates a `Def::Let` per extracted value name, stores visibility/source span and module order, and appends the DefId to module children. `body/mod.rs::lower_binding_with_context` later resolves the next declaration for that name, sets its type root, registers it with the analysis work queue, and lowers the actual body. These are concrete declaration-to-producer owners, but this packet does not compute dynamic DefIds or prove successful publication/root classification for each sample declaration.
- The Y2 `Display` role in `std/core/fmt.yu` declares `show` and a default `say` that writes `show` plus a newline. Its library source includes `Display` implementations for `int`, `str`, and tuples; the tuple implementation formats the two elements recursively. `std/io/console.yu` declares host `out::write`, a generic `say` constrained by `Display`, and `println` using the write operation. Thus the source contains both a default role method and a same-spelling free function; spelling alone does not establish which declaration a call resolved to.
- `body/role.rs` walks role declarations and consumes method declarations in owner order. `body/register.rs` registers declared role methods by their role path and name. `body/impl_decl.rs` builds and registers implementation candidates from the actual role head and input/associated annotations, and records implemented members against the required role method. This identifies the candidate identity-bearing route; it does not establish which candidate the exact sample solver selected.
- No role solve or sample runtime was executed. Exact selected DefIds, the initializer census and composed runtime-root order, module-cycle behavior, the Console host continuation, HIR/solver correspondence, sample outputs, proof closure and production remain OPEN. R149's broad source/native, soundness and principality obligations retain their original scope.
- The governing effect correction remains: contravariant `[io]` denotes the open row `[io,'e]`; a `[state]` callback is not rejected solely because it is not `[io]`.

## Next discriminating evidence

Join these pinned producers to the actual resolved module declaration/role candidate identities and the composed runtime roots, then show the same identity through Y3 HIR, candidate solving, and runtime consumers. A source spelling match, module-file traversal order, or existence of an implementation candidate is not that join. The exact falsifier is any required import/member/root whose identity or order differs from the proposed join, or whose effect/continuation route changes the pinned output.

## Resources

Cap: 900 seconds; charged in full at assignment start, no carryover. No children or Astra resources.

## Scope and verification

Read-only inspection of the immutable Y2 commit and the governing Markdown references. No compiler files, fixtures, diagnostics, generated sample bytes, builds, tests, or runtime were changed/run. Primary-authored, solo, unreviewed evidence. No independent review or theorem closure is claimed.
