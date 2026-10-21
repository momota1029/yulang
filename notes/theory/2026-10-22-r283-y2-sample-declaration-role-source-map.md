# R283 — Yulang2 sample declaration and role-source map

Status: primary-authored, read-only, checkpointed evidence; unreviewed and non-closing.

## Source-to-declaration path

The pinned Types template contains module bindings `id`, `answer`, `name`, and `pair`, followed by the top-level expression `pair.say`. Console contains two top-level expressions: `println "hello from Yulang"` and `say: 1 + 2`. The source bytes and required outputs remain those fixed by Authoritative R149.

In the Y2 oracle commit `a58eefc31e22141574b6f20c6a5748151c6d79f1`, binding syntax helpers live in `crates/infer/src/syntax.rs` (blob `5d511c71322d6af4fdc18378fdc2dbf65c94f1fd`) and `lowering/expr_syntax.rs` (blob `3f12b017e52a9e85d00c6ed6ba52a1153e9f2137`). `binding_value_names` reads `BindingHeader -> Pattern`; applied, type-annotated or field patterns resolve a single head name, while ordinary patterns collect names. `binding_arg_patterns` and `binding_body_expr` extract the function arguments and actual body.

`module_map/mod.rs` (blob `0e20fedcfef410b647b3fc90e70afa3fc0cb73e6`) registers each extracted value as a `Def::Let`, with its visibility, source span, module order and child DefId. `lowering/body/mod.rs` (blob `f33bdfb5525ddcee02eba9bcd8c181acd1f9ea99`) later resolves the next matching declaration, assigns a type root, queues `RegisterDef`, and lowers the binding body. This pins the producer route, not each sample's successful `ComputedDef` publication or runtime-root position.

## Authentic library declaration route

Pinned `std/core/fmt.yu` (blob `fd7b6607094c9ad70bde1fd41890363fa8bd6b31`) declares role `Display`, its `show` method and default `say`, and includes `int`, `str`, and tuple implementations. The tuple implementation's `show` recursively formats both elements. Pinned `std/io/console.yu` (blob `8c8eabe69755d28bc66a850745f5ea72c136cd74`) declares host `out::write`, a generic `say` constrained by `Display`, and `println` through the host write declaration.

The candidate-identity owners are `lowering/body/role.rs` (blob `e2d8dd2b078422ee2a4d518becace64d84609628`), `lowering/body/register.rs` (blob `b089ff2e17e87f1eea6e5b97835d372e73722b43`), and `lowering/body/impl_decl.rs` (blob `fb747e6db395981f9961f30dbf41e9ec6612347a`). They lower role method declarations, register methods by role path/name, form implementation candidates from source heads/annotations, and associate implementation members with required methods. This proves that the source has a candidate route; no role solve was run, so the selected candidate and exact method DefIds remain UNKNOWN. The same spelling `say` may denote a default role method or an ordinary library function; resolution must come from identity, never spelling.

## Parent application

R282's post-parser barriers remain unchanged. This source map narrows the Y2 side of the future module/role correspondence but leaves the exact imported identities, initializer census/composed root order, selected implementation, host continuation and Y3 carrier/consumer join OPEN. No sample output, proof, production permission or language change follows. Contravariant `[io]` remains the open row `[io,'e]`.

The next evidence must join actual module-resolved DefIds and roots to the selected role/implementation and carry those identities through Y3 HIR, candidate solving and runtime. Module traversal order or matching names alone cannot establish the join.
