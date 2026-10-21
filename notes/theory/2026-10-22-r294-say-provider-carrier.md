# R294 — pinned `say` declaration and its provider carrier

Status: primary-authored source/HIR investigation; unreviewed; R149 remains OPEN.

## Finding

R293 resolved public `say` through the pinned prelude route to
`std::io::console`, but joining that declaration against a provider lowered
with `lower_module_with_source_identity` returned `StaleDeclaration`.
The exact pinned header is `pub say(value: 'a): () =`; its formal is parsed as
`PatternCallTail`. Ordinary `plain_binding_header` only admits that node when
`local_source` is enabled, so source-identity-only HIR drops the direct binding.

A probe of `lower_module_with_local_source` on the whole pinned console module
returns `StructuralProjection`. Isolating each direct binding shows that the
simple binding roots and `say` itself can form LocalSource; host act and related
act-operation roots account for other failures in the full-module route. The
normal `lower_module` path is the appropriate seam: it already performs
ordinary HIR lowering and attaches ordinary source carriers to admitted
bindings. The next implementation step is to admit the pinned single typed
parenthesized formal in that ordinary source-carrier grammar.

## Required evidence

From the same `ParsedFile`, build the export index and both provider artifacts:
source-identity-only HIR should still demonstrate the old missing owner, while
normal `lower_module` should return an exact public `say` binding with a
supported ordinary source carrier. Check the carrier's `where 'a: Display`
clause, declaration root, and parse-owned source key. Then join that HIR binding
to the already resolved public export.

The carrier retains the prerequisite only. Candidate preflight currently
rejects `where` clauses because no identity-bound role-constraint consumer
exists yet. Do not treat retention as constraint generation, role selection,
imported scheme ownership, sample execution, or proof closure.

## Governing invariants

- Keep all 40 pinned source identities and exact Yulang2 bytes.
- Keep export route resolution as the source authority.
- Do not synthesize `say` from its spelling or turn `Display` into a chosen
  method implementation.
- Do not treat LocalSource retention or a passing test as source adequacy,
  candidate inference, runtime evidence, or proof closure.
- Preserve the user's correction that contravariant `[io]` means `[io,'e]`.

## R294 implementation result

Extended `plain_binding_header` so the ordinary source-carrier entrypoint
also retains a typed single-formal `PatternCallTail`. For this decomposition it
ignores the adjacent result-type annotation, while declarations without a
`PatternCallTail` keep their existing annotation handling. This enables
`lower_module` to admit the pinned `say` binding and form its ordinary
LocalSource carrier. The scope is tied to `ordinary_source_carriers`; the
source-identity-only mode remains unchanged.

The pinned closure test now constructs the export index, source-identity-only
HIR and ordinary `lower_module` HIR from the same `ParsedFile`. The older HIR
still rejects a `say` owner lookup as stale. The ordinary provider HIR joins
`say` to its exact public binding, and its carrier has the same
`DefinitionRootId`, exactly one `where 'a: Display` clause, and a source key
owned by the pinned console parse. Exact `println` and `Display` joins remain
covered.

A full `lower_module_with_local_source` probe for all of `console.yu` returned
`StructuralProjection`; isolated binding probes showed `say`, `print`,
`println`, `note`, `eprint`, `eprintln`, and `dd` individually form, while host
act and operation declarations fail that all-local-source module route. This is
why the production-shaped ordinary `lower_module` path is used for the provider
artifact.

The result establishes a declaration and prerequisite carrier only. The
existing candidate-source preflight still rejects nonempty `where_clauses`,
so `say` has no consumed `Display` premise, imported scheme, candidate typing,
or runtime result yet.
