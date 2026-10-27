# Provider root-context preparation

Status: Draft
Scope: Candidate preparation contract for the logical root `Context` supplied to `sourceRules` for the inspected provider path. This document does not adopt source semantics.
Drafted-by: Luna / primary
Reviewed-by: independent `spec_auditor` (research-draft scope)
Supersedes: none

## Purpose and boundary

The unchanged source/executor theorem remains the objective: all supported source programs, lawful finite Simple-sub histories, and retained extrusion occurrences, with their original lexical/type/event scopes, recursive monomorphic sharing, complete Call, effect hygiene, A/B, soundness, required principal coverage, progress, and termination.

The current narrow obstruction is `PSR-ROOT-CONTEXT-1`: the provider theorem consumes a concrete ordered `OriginalSource.Context`, but the inspected provider construction path does not establish the root rows or their order. This document records a candidate contract and the decisions needed to make it concrete. Its status is **Draft**; it grants no implementation, production API, or semantic authority.

## Existing authority and evidence

`OriginalSourceSyntax.lean:184-204` defines `Binding` with `name`, `owner`, `kind`, optional `component`, `annotation`, and `entry`, plus `singleUse`. `Context` is `List Binding`; `bindNames` prepends mapped rows; `lookupBinding` returns the first row with the requested name. These definitions establish the logical representation and lookup behavior, not the source-to-root conversion.

`OriginalSourceGeneration.lean:84+` defines `sourceRules (context)` and passes that context to the generated rules. The Lambda case at `:132+` adds a formal row before the incoming context. `patternContext` and `statementContext` also define their local extension operations (`:51-60`). These rules consume a context explicitly; they do not prepare a module root context.

The adopted Source-Generalize definition governs its stated source generalization construction. The inspected authority does not specify a frontend constructor that maps module/import/provider preparation into an ordered root `Context`. No such equation is assumed here.

The source census in `tasks/agent-loop/inbox/provider-root-context-definition-20261028-source.md` records the actual HIR, LocalSource, import, and export owners for the inspected `pub id x = x` fixture. It identifies source order and import-resolution facts in Rust, while preserving the distinction between those code facts and logical `Binding` semantics. It also confirms that the fixture's HIR declaration, formal/body link, and export join do not themselves supply root rows.

## Candidate preparation relation (unresolved)

The constructor still to be specified must relate one authenticated provider declaration entry and its preparation inputs to one ordered logical context. A suitable *shape* for the missing relation is:

```text
PrepareProviderRoot(entry, module-declarations, resolved-imports, prelude, Γroot)
```

This is notation for an obligation, not a new judgment or adopted rule. Its inputs must be owned by the actual source preparation path, and its output must be the exact context passed to `sourceRules` for that provider's source. It must not derive semantic fields from export visibility, spelling alone, HashMap iteration, or opaque caller evidence.

The consumer application for the fixture has this shape:

```text
sourceRules Γroot providerSource
```

This expression identifies the consumer; by itself it is neither an equation nor a preparation link. The companion proof-obligations note §3 states the unresolved `ROOT-EQUATION`, coverage, and exact-entry/source-link targets. Those targets remain incomplete until the source owner, inclusion policy, every row field, and list precedence are justified. In particular, this draft does not set `Γroot = []`, does not classify `id` as a logical Binding kind, and does not infer rows from the fact that `id` is public.

## Field and order authority matrix

| Logical datum | Existing source owner or consumer | Established fact | Missing definition or decision |
|---|---|---|---|
| `Binding.name` | `HirBinding.name` (`module.rs:1730-1787`); LocalSource binder/parameter spellings (`local_source.rs:572-612`); source export declaration names (`source_exports.rs`) | The source spelling and owning syntax are retained. | Approved mapping to Lean `Name`; which module declarations, imports, prelude names, formals, or other entities become root rows. |
| `Binding.owner` | Branded `DefinitionRootId` / `SourceRootId` (`module.rs:1162-1194,1298-1330`); `HirBinding.definition_root()` (`:1766-1771`); `LocalSource` root (`local_source.rs:63-78`) | Rust tracks artifact and source ownership. | Approved owner-to-Lean-`Site` mapping and the root row's exact owner equation. Branded IDs alone are provenance, not a logical Site. |
| `Binding.kind` | `HirItem::{Import, Binding, Expression, Error}` and `HirBinding` visibility/evaluation class (`module.rs:1730-1806+`); separate import environment | Rust distinguishes syntax/HIR item classes and import identities. | Selection among `external`, `formal`, `pattern`, `internal`, `local`, `continuation`, `published`, and `family`; visibility or export identity does not decide this field. |
| `Binding.component` | Nested `LocalSourceNamedGroup` identities and parent/group relations (`local_source.rs:96-130`) | Some nested forms retain group/component relationships. | Whether a root row has a component and, if so, the exact `Option Site` mapping. |
| `Binding.annotation` | LocalSource parameter/binding annotation (`local_source.rs:572-612`); annotation subsystem | Some source annotation syntax/evidence is retained. | Conversion to logical `Annotation` and policy by row class. Raw or opaque annotation payload is not a semantic certificate. |
| `Binding.entry` | HIR/LocalSource initializer and body identities (`module.rs:1730-1760`; `local_source.rs:602-612`) | Supported paths retain parse-owned source carriers for initializer/body material. | Conversion to logical `Entry` and its equation with source-rule entry/return behavior. Export identity is not an entry. |
| `Binding.singleUse` | HIR `evaluation_class` (`module.rs:1740-1759`) and LocalSource occurrence identities | A coarse evaluation classification and local source references exist. | A root single-use derivation. `evaluation_class` is not equivalent to `singleUse`; no Boolean value is selected here. |
| List order and shadowing | Ordered HIR items and source declaration vectors (`module.rs:1898-1920`; `source_exports.rs:790-840`); import resolver (`module.rs:348-456`) | These Rust operations retain source traversal order; explicit imports occupy names before implicit prelude insertion in that resolver. | Mapping to head-first `Context` order, row inclusion, collision rules across declarations/imports/prelude/formals, and module recursion. HashMap order is not semantic order. |

### Imports, prelude, modules, and recursive groups

`SemanticImports` stores resolved source-import identities or ambiguity separately from the logical context (`module.rs:116-123,777-840`). The inspected resolver gives explicit imports precedence over implicit prelude names for name resolution (`:348-456`). This does not establish their order or kind in `Context`.

Module declarations and public declarations are indexed as parse-owned export records (`module.rs:2319-2335`; `source_exports.rs:790-840`), not as logical Binding rows. The inspected module/HIR owner path has no root recursive-group identity or group-level context constructor. Nested LocalSource named groups do not settle module-level recursive monomorphic sharing.

The following are unresolved alternatives for a future authority decision: which module entries/imports/prelude names are included; whether one canonical sequence or several precedence tiers determine the list; how collisions are resolved under head-first lookup; how recursive declaration groups share their monomorphic context; and whether a source-owned preparation object must retain complete row certificates. This draft selects none of them.

## Required correctness clauses for any accepted constructor

An eventual accepted constructor must satisfy each clause below for every provider entry in its declared source domain:

1. **Entry identity:** the provider declaration, its retained source body, and the `sourceRules` input refer to the same parse-owned source occurrence. The existing fixture join is evidence for its exact fixture only.
2. **Complete row justification:** every emitted row's name, owner, kind, component, annotation, entry, and `singleUse` is justified by the approved source rule, including explicit absence where the rule says `none`.
3. **Order and lookup:** the produced list has a source-owned sequence whose head-first lookup implements the approved lexical/import/module precedence for every relevant name, including collisions and shadowing.
4. **Context preservation:** all context-sensitive consumers receive the same complete ordered context or a rule-authorized extension of it. Equality of one formal lookup is insufficient: closure/capture and binding atoms retain the whole context.
5. **Recursive sharing:** recursive module groups, if in the supported domain, use the approved shared monomorphic environment and do not become independent per-declaration contexts.
6. **Source/native interface:** the source preparation equation connects to the actual constraint generation, propagation, consumer, and execution path without treating identity joins or opaque payloads as semantic evidence.

Each clause is falsified by a provider entry whose emitted root differs from the approved source construction; an unjustified or mismatched field; a lookup that selects the wrong row; a closure/binding consumer receiving a different context; a recursive group split contrary to its rule; or a native path lacking the same source-owned input.

## Proof application and explicit premises

The separate obligation record, `notes/theory/2026-10-28-provider-root-context-preparation-obligations.md`, gives exact theorem/source locators and the future proof sequence. In summary, only after an approved and source-authenticated `Γroot` equation is supplied may the existing checked lexical bridge be instantiated at that incoming context. `formalContext` preserves its incoming tail, while the lookup non-identifiability lemma rules out recovering the root context from the fixture's observed formal lookup alone.

Application to `provider_from_total_completion` in `OriginalProviderPublicationCoverage.lean:292+` must retain its explicit context, kernel/environment, open replay, compatibility, initializer, Shared admission, binding-atom and publication premises. The theorem does not construct the root context or discharge those premises. Admission, Return/Shared, replay, publication, source/native correspondence, effects, A/B, complete Call, soundness, principal coverage, progress, termination, and production remain OPEN.

## Approval boundary

This document is a candidate, not `Authoritative`. A fresh independent review must first check the field matrix, source owners, exact fixture boundary, alternatives, and proof obligations. After review, the unresolved inclusion/classification/order/shadowing/recursive-group/source-link decisions must be presented for explicit user approval. Only a recorded decision can authorize dependent semantic implementation. If an exact existing authoritative construction is found instead, cite and derive it rather than treating the missing-definition proposal as adopted.

No Rust or Lean implementation, tests, builds, behavior changes, or parent-gate promotion are authorized by this draft.
