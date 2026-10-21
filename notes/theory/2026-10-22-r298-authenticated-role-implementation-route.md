# R298 — authenticated role-to-implementation source route

Status: source inventory bridge implemented and focused verification passed; no independent review. R149 remains OPEN.

## Parent and exact sample evidence

The unchanged R149 samples remain the parent: Types (142 bytes, SHA-256 `8cbfb97a8df8e5dc4916313769c39a84626ae124f91f8a9672f1ad8b866f98e6`) and Console (92 bytes, SHA-256 `ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076`). The exact CLI inputs were run before this source-only change. Types exits with `Collection(ComponentIdentityExhausted)` at the existing `FieldTail` consumer; Console exits with `Unsupported` at the imported-name preflight. Both produce no output. R149 requires exact inferred Types entries and captured output `(42, Yulang)\n`, and Console writes `hello from Yulang\n`, then `3\n`.

The converted unified design and proof companion remain governing. The source lookup below is not role satisfaction, a method type, type-directed implementation selection, provider scheme transport, or a compiler proof.

## Implemented correspondence

`resolve_source_role_implementations` takes one exact `SourceRoleId`, requires exactly one matching provider module and exact role declaration, rejects duplicate local role heads, and returns only non-recovered implementation declarations with bodies whose role type is exactly the same unqualified and unapplied spelling in that module. Qualified, applied or unparseable role heads stay unavailable. Each returned declaration retains its source-owned implementation ID and member IDs.

The pinned prelude `Display` import now has a tested source route into the exact `std::core::fmt` role inventory. That inventory contains the 14 pinned direct `Display` implementations, including the ordered two-element tuple implementation and its exact `show` member owner. The result is still a candidate inventory: the receiver's inferred type must later select the unique appropriate implementation, and generic `where` obligations must still be transported and discharged through the same provider/use world.

## Evidence

- Direct invocation of the unchanged CLI samples reproduced the existing failures above; no sample output was claimed.
- `cargo test -p yu-hir --features shadow source_role_implementation_lookup_rejects_ambiguous_local_role_heads` — passed.
- `cargo test -p yu-playground --lib pinned_public_export_route_retains_source_owned_edges_and_names` — passed; this exercises the actual imported role identity, its provider implementation inventory, the tuple member identity, and missing/duplicate/stale identity failures.
- `cargo test -p yu-playground` — passed.
- `git diff --check` — passed.

Existing unused/private-interface warnings remain in `yu-hir`, `yu-solver`, and the playground; this slice adds none. No independent review ran under the user's solo-work instruction.

## Exact remaining bridge

The normal playground `prepare` path still supplies `SemanticImports::empty()`. Candidate source preflight rejects imported Names and any nonempty `where` list; `FieldTail` still returns unavailable. The next implementation outcome must bring authenticated provider schemes and implementation evidence into the same inference world, consume the exact subject row already retained through Capture/FreshUse, and select the implementation from the inferred receiver type. Only then can the relevant source consumers be admitted and the unchanged samples run. Runtime host output, exact public type publication, source/native correspondence, principal typing and the original proof gates remain OPEN.
