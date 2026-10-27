# PROVIDER-ROOT-CONTEXT-DEFINITION-20261028/r1 source handoff

Sprint-ID / contract revision and SHA-256: `PROVIDER-ROOT-CONTEXT-DEFINITION-20261028/r1`, `r1`; `tasks/agent-loop/sprints/provider-root-context-definition-20261028-r1.md`, `58a685b51a066c7f5df913a93d9805f460237da29e100c684baf46dba7e8259e`.

Assignment-ID / handoff revision: `PROVIDER-ROOT-CONTEXT-DEFINITION-20261028-SOURCE`, revision `1`.

Parent gate / original theorem and scope locator: `PSR-ROOT-CONTEXT-1`; unchanged universal source/executor theorem remains OPEN. `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1, 3, 5. Source rules receive an explicit `OriginalSource.Context` in `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean:84`; fields and context lookup are in `OriginalSourceSyntax.lean:184-198`.

Baseline / direct dependency hashes: baseline `f93b64fff351869384b0cdd0aaff520639980ab5`; integrated contract commit `ebfdc3631`. All admitted direct inputs were rehashed and matched before this read-only census:

| Input | SHA-256 |
|---|---|
| Sprint contract | `58a685b51a066c7f5df913a93d9805f460237da29e100c684baf46dba7e8259e` |
| `rules/design-authority.md` | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `notes/theory/lean/YulangClosure/OriginalProviderLexicalOwner.lean` | `bf4e6572e5f1bf9b97a4d0274488b8d20f4487528d5bf8346ad262d3c75bd2f7` |
| `notes/theory/lean/YulangClosure/OriginalProviderRootContext.lean` | `bde05d470435f0184a9203fb30a4612126aab3540b9889f57a0a087bf7b553f3` |
| `notes/theory/lean/YulangClosure/OriginalProviderPublicationCoverage.lean` | `62257d276004f6caf07872142e4a4369266d5205d992f4f3d56f36657ae69783` |
| `crates/yu-hir/src/module.rs` | `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `crates/yu-hir/src/module/source_exports.rs` | `03727fd3918738a48afde7f7a875de60b63b43ac2cc620896a4ed73d8b0a9179` |
| Frozen prior source handoff | `f133ccfbdb5bfd603dba1cbc58baded5ad0ef2b90172e8ee2492c12760143fe9` |

Role / actual worker ID / current session / launch or resume receipt: registered `implementer`, child `/root/provider_root_context_definition_source`; current session is this assignment. Collaboration runtime is the launch receipt; no separate runtime/model receipt exposed.

Requested model and effort / observed model and effort: Luna/high requested; observed model and effort UNKNOWN (not exposed by runtime).

Exact leased paths / authors and descendants: only `tasks/agent-loop/inbox/provider-root-context-definition-20261028-source.md` written by this worker; no descendants. Source inspection only. No Rust, Lean, test, manifest, or other handoff paths were written.

Outcome class: `source-native-evidence` / source-owner map for the admitted `pub id x = x` fixture path, and `source-qualified-counterexample` to the claim that the inspected owners already construct an ordered root `Context`. This does not establish global absence at every possible compiler entrypoint.

## Owner map and authority boundary

Code facts below identify retained source owners and consumers. They do not select source meaning for a root `Binding`. The only existing logical authority found is the Lean data shape and rule use: `Binding` has `name`, `owner`, `kind`, optional `component`, optional `annotation`, optional `entry`, and `singleUse` (`OriginalSourceSyntax.lean:184-198`); `Context` is `List Binding`, `bindNames` prepends mapped entries and `lookupBinding` returns the first matching name (`:198-204`). `sourceRules` consumes that context directly (`OriginalSourceGeneration.lean:84+`). These clauses do not define how Rust prepares a module root context.

| Logical datum | Actual Rust owner / consumer | What source establishes | Missing authority / proposed status |
|---|---|---|---|
| `Binding.name` | Parse/HIR: `module.rs:1730-1787` `HirBinding.name`; local source binders: `local_source.rs:602-612` `LocalSourceBinding.spelling`; parameters: `local_source.rs:572-585` `LocalSourceParameter.spelling`. Source exports retain declaration spelling in `source_exports.rs` declaration records. | Exact spellings and source ranges belong to declarations/binders. | No approved conversion to Lean `Name`, no decision whether a root row represents module definitions, formals, imports, or more than one class. Spelling alone cannot classify a row.
| `Binding.owner` | Authentic Rust roots are `DefinitionRootId` / `SourceRootId` (`module.rs:1162-1194,1298-1330`); `HirBinding.definition_root()` (`:1766-1771`); `LocalSource` stores its root owner (`local_source.rs:63-78`). | Owner IDs preserve artifact/source ownership and distinguish definitions from expression/member roots. | No Rust owner-to-Lean `Site` mapping or approved root `Site` equation. Branded identity is provenance, not a Lean semantic owner by itself.
| `Binding.kind` | HIR has `HirItem::{Import, Binding, Expression, Error}` (`module.rs:1806+`); bindings retain visibility and `evaluation_class`, but no Simple-sub `BindingKind` (`:1730-1760`). Import environment is separate. | Rust distinguishes declaration/import/expression structure. | No evidence selects `.external`, `.formal`, `.pattern`, `.internal`, `.local`, `.continuation`, `.published`, or `.family` for root rows. Visibility/export status is not sufficient classification.
| `Binding.component` | `LocalSourceNamedGroup` retains group source, enclosing group, ordered formals, terminal lambda/body (`local_source.rs:96-130`); source member roots and annotations have separate owners. | Some nested source constructs have identities and parent/group relations. | No approved `Option Site` assignment for any root binding, nor rule for component-bearing rows. Do not infer a component from hierarchy or syntactic nesting without decision.
| `Binding.annotation` | `HirBinding` carries no annotation field (`module.rs:1730-1760`); local parameter/binding carries `Option<SourceAnnotation>` (`local_source.rs:572-585,602-612`); declaration annotation owner is source annotation subsystem. | Annotation syntax/evidence is retained for selected local source entities. | No root-context annotation conversion to Lean `Annotation`, nor policy distinguishing declaration, formal, imported, or absent annotations. Raw/opaque annotation payload is not a semantic certificate.
| `Binding.entry` | HIR source expressions and `LocalSource` retain body/initializer indices (`module.rs:1730-1760`; `local_source.rs:602-612`); source export records carry declaration identity/range. | A binding initializer/body has a parse-owned source carrier on supported paths. | No approved conversion to Lean `Entry`; no equation connecting root row entries to source-rule `Entry`/judgment. Export identity is not an entry.
| `Binding.singleUse` | HIR `evaluation_class` is a coarse evaluation categorization (`module.rs:1740-1759`); no `singleUse` field or owner found in these admitted files. | Evaluation-class fact is available on HIR bindings, and source local references have identities. | Missing root single-use classification/derivation. `evaluation_class` is not equivalent evidence. Must not guess false/true from syntax or use shape.
| Root list order / shadowing | Parser-owned HIR `items` vector and `SourceExportIndex.declarations` vector preserve source traversal order (`module.rs:1898-1920`; `source_exports.rs` index construction around `:790-840`). Import resolution uses `HashMap` for names and explicit imports take precedence over implicit prelude (`module.rs:245-330,348-456`). | There are source order and import-resolution precedence facts for their respective Rust operations. | No rule maps either order to `Context` list precedence, determines inclusion/omission, or settles collisions among declarations/imports/prelude/formals. HashMap iteration order is non-semantic. Lean's `lookupBinding` is head-first, but source-to-list ordering is not supplied by that fact.

## Module, imports, and recursive groups

- Module declarations and public source declarations are indexed as parse-owned declarations, not as type-context rows: `module.rs:2319-2335` calls `source_exports::index`; `source_exports.rs:790-840` traverses direct top-level syntax and appends declarations in source traversal order. Mod declarations have a special missing-child resolution path (`source_exports.rs` declaration logic near `:690+`). The inspected API has no operation that turns a module declaration into `OriginalSource.Binding`.
- Imports: `SemanticImports::empty`, `with_implicit_prelude`, and `with_source_imports` are at `module.rs:777-840`. `with_source_imports` resolves indexed named/glob use leaves and then inserts prelude names not already occupied (`module.rs:348-456`); the names map stores `SourceImportBinding` identities/ambiguity, not ordered Binding rows. Explicit imports outrank implicit prelude *for that resolver*. This does not establish root Context order or Binding classification. Caller evidence explicitly certifies artifact association only (`module.rs:119-123` and prior outcome), not payload semantics.
- Recursive groups: in the inspected `HirBinding`/module source-owner API, no root recursive-group identity or group-level context constructor was found. Local named groups describe nested named source forms (`local_source.rs:96-130`), not module-level recursive declaration groups. Exact recursive monomorphic sharing is an unchanged parent requirement, not a conclusion supplied by module item order. A source rule for module recursion and its group context remains missing/proposed.
- Source order facts do not license HashMap order. HIR `items` and declaration vectors are ordered containers, but the conversion to the *head-first* Lean list and shadowing policy remains undecided absent explicit authority.

## Exact fixture boundary and consumer path

The prior frozen source handoff `tasks/agent-loop/inbox/provider-root-context-20261027-source.md` (hash above) and outcome `tasks/agent-loop/sprints/provider-root-context-20261027-r1-outcome.md` record the executed, provisional adapter result for exactly `pub id x = x`: HIR declaration owner and public source-export join; `LocalSource` lambda formal and body name resolve to the same HIR parameter; `SemanticImports::empty()` has no source-import environment. This fixture does not include or authenticate a root `Context`, nor does it cover arbitrary provider paths. The adapter/trace were provisional evidence instrumentation, not a semantic constructor or proof; the prior handoff names Luna as cleanup/replacement owner and gives the falsifier: an independently approved existing constructor supplying the exact ordered rows and justification of every field.

The inspected path is source parse -> HIR binding / branded `DefinitionRootId` -> supported `LocalSource` Lambda and parameter/body Name -> source export identity/visibility join. At the Lean boundary, `sourceRules context` needs its context as an input. None of these owners creates Simple-sub constraints, propagation state, or native/executor correspondence; those downstream steps cannot be inferred from the source identity join. The source-to-constraints-to-propagation-to-execution contribution here is limited to pinpointing the missing input edge and the owners that currently stop before it.

## Unresolved alternatives and source-level falsifiers

No alternative is selected. User/primary decision is needed for (a) which module declarations, imports, prelude names, formals, and other entities appear in root Context; (b) each row's `kind`, owner `Site`, `component`, annotation, entry, and `singleUse`; (c) canonical context order and head-first collision/shadowing precedence; (d) module-level recursive group formation/sharing; and (e) the Rust preparation constructor/equation authenticating the Lean `Context` passed to `sourceRules`. Do not choose empty Context, classify by visibility/export identity, spelling or opaque evidence, derive order from a `HashMap`, or equate evaluation class with `singleUse`.

The scoped missing-owner finding is falsified by a source path, within the inspected dependency cone or another admitted entrypoint, that constructs the provider root's ordered Lean-equivalent Binding rows and retains justification for every field, module/import/prelude inclusion, recursive group and precedence decision. A field-level claim is falsified by showing its actual owner and conversion rule in an approved constructor. An ordering claim is falsified by a source-owned sequence plus an approved equation mapping it to `Context` list order and collision semantics. A module-recursion claim is falsified by a retained source group identity and explicit root-context sharing rule. The `pub id x = x` fixture falsifies a claim that its existing import/export/HIR join alone already determines those facts: it has none of the required root rows or equation.

Parent application: no `Context` equation or theorem application follows. The admitted source facts can support a candidate contract only when missing decisions are explicitly marked proposals/alternatives. Original universal quantifiers and all parent obligations remain OPEN: source/native correspondence, A/B, complete Call, effect hygiene, soundness, required principal coverage, progress, termination and production.

Checks / budget: read-only `sha256sum`, `cat`, `sed`, and `rg` inspection only. No Cargo, Lean, tests, implementation, or additional toolchain execution. No test or proof claim is made. Total elapsed work was within the source lane's 450-second allocation; no resource-limit failure observed.

Prior evidence reused / rejected: reused the reviewed `NO_SAFE_CODE_SLICE` conclusion, exact fixture trace facts, and source handoff at the frozen hashes above. Rejected any inference from export visibility/identity, names, map iteration, opaque caller payload, HIR evaluation class, or the fixture's formal/body join to root `Binding` semantics. No withdrawn Simple-sub bypass is restored or proposed.

Mutual TODO / exact missing owner request: `PSR-ROOT-CONTEXT-1-AUTHORITY` — Luna to obtain/identify an approved root preparation constructor and its field/order/shadowing/recursive-group equation, or preserve each unresolved alternative for explicit user decision. Required evidence: source-owned ordered rows with field justification and the exact `sourceRules` input. Falsifier: constructor/authority evidence as specified above. This TODO grants no write or semantic authority to this worker.

Frozen artifact / SHA-256: `tasks/agent-loop/inbox/provider-root-context-definition-20261028-source.md`, SHA-256 recorded in the submission message after write.

Worker state / writes stopped receipt / scratch: STOPPED; sole leased handoff is frozen; no descendants. No scratch or generated paths created. No external/user contact or Git operations.

Commit-ready milestone: frozen source-owner handoff pending primary synthesis and fresh independent review. No parent theorem closure or implementation authorization.
