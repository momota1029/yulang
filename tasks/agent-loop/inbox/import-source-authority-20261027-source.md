# IMPORT-SOURCE-AUTHORITY-AUDIT-20261027/r1 — source-owner evidence

Claim class: bounded static source characterization and missing-construction
audit. No executed resolver trace, checked theorem, semantic adoption or parent
closure is claimed. Fresh independent review is pending.

## Baseline, lease and synchronization

The governing contract is
`tasks/agent-loop/sprints/import-source-authority-audit-20261027-r1.md`, SHA-256
`747522aadee09038ded3897f83c0c939384590cf1a60de41fb6baab274f0b82f`, at its
pinned code baseline `6da3e4a45`. Worker identity:
`/root/import_source_authority_source`; actual session UUID unavailable;
observed model `gpt-6.1-sol`, effort UNKNOWN. The start acknowledgement was sent
to the primary before source inspection.

The primary's live capacity update was received and acknowledged: the nine
UNKNOWN reservations were already released, this repeat adds no capacity, and
UNKNOWN observations and quarantined paths remain. My exact disjoint lease is
only this handoff and `/tmp/yulang-import-source-authority-20261027/source/`.
I did not create scratch files or descendants.

Independently rehashed the union of the caller proof's 56 inherited entries,
its ten source-map entries, and both contracts' direct path/hash rows: **61
unique pinned paths, all matching**. The caller proof, source, review and
outcome hashes also match respectively `c8753e75…989b`, `ef6f4321…ed4`,
`5ad88936…bfc`, and `9e09bd1f…00d`.

## What the existing Rust owners establish

The fixed source is exactly the caller adapter's constants at
`tools/inline-authentic-extraction/src/bin/original_caller_reify.rs:12–17`:
consumer `use std::core::id as identity`, `first = identity 1`, `second = id 2`,
and the unchanged nested-shadowing `value`; providers `std`, `std::core`, and
`std::prelude`, with `pub id x = x` and `pub use std::core::*`.

1. `SourceNodeKey` equality retains parse allocation, exact green node and
   start; `ParsedFile.owns_source_key` checks the parse brand
   (`crates/yu-syntax/src/full_parse.rs:69–90,128–138`).
2. `index_source_exports` constructs source keys from that parse and supplies
   its module, revision and header to the index owner
   (`crates/yu-hir/src/module.rs:2319–2335`). The index retains declaration
   kind, namespace, name, visibility, range, text and recovery, plus complete
   use trees (`module/source_exports.rs:9–51,686–718,774–847`). This module
   explicitly assigns **no type-level meaning** (`source_exports.rs:1–4`).
3. The public resolver validates public module routes, rejects recovered
   candidates and retains re-export leaves. It deduplicates only the same
   module/source/range declaration; distinct candidates are ambiguous
   (`source_exports.rs:1129–1191,1194–1260,1295–1325`).
4. Explicit import lowering chooses `exposed = alias.unwrap_or(selected)`;
   resolution remains of the selected provider name. Duplicate exposure of
   the same exact identity is merged, and explicit exposure precedes implicit
   prelude names (`module.rs:348–409,429–457`). Prelude lookup scans actual
   requested nonlocal names, skips local declarations and resolves through
   `std::prelude` (`module.rs:245–279,307–329`).
5. `with_source_imports` retains that environment and marks complete source
   uses; lowering checks the exact consumer module and parse root
   (`module.rs:797–808,2338–2366`). `NameResolution::Imported` and
   `LocalSourceResolution::Imported` retain `SourceExportId`
   (`module.rs:1520–1526`; `module/local_source.rs:442–444,2140–2151`).

Thus the inspected code and existing fixture
`module.rs:4817–4835` describe `identity` and prelude `id` resolving to the
same `std::core::id` declaration. That fixture was **read, not run**. A
`SourceExportId` has only module, exported name, source key, range and syntax
kind (`source_exports.rs:163–182`); it contains neither a semantic certificate
nor an OriginalSource Name/Site allocation.

The failed caller adapter did not execute these joins: its
`ShadowArtifact::from_parsed` precondition fails on the first provider before
the calls at lines 460 onward. The owner's admission conventions deserve a
separate repair: export indexing explicitly treats a `ModDeclaration` Missing
child as unresolved external-module lookup rather than recovery
(`source_exports.rs:694–707`), while `ShadowArtifact::from_parsed` rejects any
nonempty syntax-diagnostic projection (`shadow.rs:1669–1679`). The preserved
failure does not include the actual diagnostics, so this audit does not claim
that this static distinction uniquely explains that failure. Index admission
does not entail successful ShadowArtifact construction.

The intended provider HIR join is visible, but unexecuted, at caller adapter
lines 471–481: provider module, owned definition root, exact definition source
key and range. `HirBinding` carries id/root, visibility, spelling, parameters,
value and range (`module.rs:1729–1740,1766–1787`). Its lowering wraps named
parameters in actual Lambda nodes (`module.rs:3673–3691`). These facts are
provenance and raw source structure, not an independently typed provider
publication.

## Binding fields and their actual owners

`OriginalSource.Binding` requires all seven fields
(`OriginalSourceSyntax.lean:184–205`). `bindNames` is a raw constructor with
defaults; its availability does not establish that import elaboration used it.
The following table identifies existing producers, rather than selecting new
field values for the importer.

| Field | Existing source producer/rule | Evidence available for this fixture and exact gap |
| --- | --- | --- |
| `name` | Resolved lexical name allocation; `bindNames` consumes already allocated Names. Client Alias copies a binding and changes only its Name (`OriginalSourceGeneration.lean:430–438`). | Exposed strings `identity` and `id`, their use occurrences, and exact common provider identity are available from the Rust resolver. There is no adopted authenticated map from these consumer lexical exposures/provider key to the OriginalSource Nat Names and their lookup equations. Equal provider identity does not require equal lexical Name coordinates. |
| `owner` | Each source introduction retains its own Site: pattern records, publication records, Lambda formal registration (`OriginalSourceSyntax.lean:207–237`; `OriginalSourceGeneration.lean:132–136,377–403`). | Provider declaration key/range and HIR root have an intended exact join. Neither key/range nor HIR-local ordinal is an OriginalSource Site. Import installation must state which original introduction/publication owns the binding and authenticate its Site mapping; the resolver does not supply that equation. |
| `kind` | Recursive registration creates `.internal`; Lambda creates `.formal`; binding publication creates `.published`; Name generation treats `.published`/`.family` as actual instantiation sources (`OriginalSourceGeneration.lean:95–110,132–136,329–340,377–387`). Adopted SG §3.3 distinguishes external Mono/Established, prior Published and independently typed Family. | `pub` is visibility, not a `Published(p,Sigma_p)` receipt. The provider syntax and `SyntaxKind::BindingStatement` supply no independent provider derivation, source publication, installed Mono contract or Family binder tree. Choosing among `.external`, `.published`, and `.family` from resolver identity is unsupported. |
| `component` | `.internal` entries obtain `some site` from the actual recursive `letS` group (`OriginalSourceGeneration.lean:329–332`); ordinary constructors default to `none`. | The fixed provider text contains an ordinary unannotated identity declaration, not a supplied recursive-group registration. No component installation or imported binding constructor is emitted. A chosen `none` still requires the applicable constructor/correspondence, rather than a guess from public syntax. |
| `annotation` | Lambda copies the actual formal annotation (`OriginalSourceGeneration.lean:132–140`); binding rules separately retain/check the written final target (`377–403`). Published `bindingRecords` and `bindNames` use default `none` (`OriginalSourceSyntax.lean:200–202,225–229`). | The literal fixture has no written annotation. That syntax observation does not itself choose the import Binding constructor. In particular a source final target is handled through publication evidence, not automatically copied into a context flag. No inference result may be invented as a written annotation. |
| `entry` | Lambda formal registration sets `some formal.entry`; `Formal.entry` is determined by its outer source computation annotation (`OriginalSourceSyntax.lean:26–40`; `OriginalSourceGeneration.lean:132–143`). | The unannotated formal `x` has Value entry under a faithful provider reification. The exported callable `id` is not itself that formal. No import-entry equation exists; setting `id.entry := some .value` merely because `id` is a function would conflate these owners. |
| `singleUse` | Lambda registration computes `body.nameCount formal.name == 1`; the special formal-call predicate consumes the flag (`OriginalSourceGeneration.lean:60–72,132–136`). Other raw constructors default `false`. | The provider formal `x` has one body occurrence under its exact source reification. This does not classify imported `id`, whose two uses are distinct consumer occurrences. No imported-context constructor authenticates its flag or licenses the special formal-call rule. |

The first unsupported construction is therefore not a difficult equality of
serialized row ordinals. It is an import installation that, from the actual
resolved declaration **and independently established provider evidence**, builds
the original Context and proves every consumer lookup returns the Binding
produced by the appropriate owning rule. Opaque `CallerEvidenceBinding` cannot
fill it: its owner explicitly validates association, not payload meaning
(`module.rs:903–927,1040–1047`).

## What the adopted rules decide, and what is missing

The authoritative design adopts its companion §§3–5 while explicitly excluding
the production resolver/cutover from supersession and implementation authority
(`notes/design/2026-10-08-source-generalize-definition.md:3–9,35–38,132–155`).
The companion §3.3 says records are supplied by owning source rules and may not
be recovered from identifier spelling, endpoint shape or query success
(`notes/theory/2026-10-08-source-generalize-definition-and-proof.md:219–235`).
Its existing cases are discriminating requirements:

| Actual supplied provider evidence | Required use behavior |
| --- | --- |
| Installed immutable monomorphic value, `Mono(h,Contract_h)` with all `Established` fields | Name/projection restricts the same complete certificate; Alias shares h and allocates no instance. |
| Prior source publication `Published(p,Sigma_p)` and independent prior derivation | A real polymorphic Name instantiation has its original instance event, retaining p and all shared/executed fields. |
| Independently typed `Family(d0,T0,R0)` with its original binder tree | Instantiate that independently established family; its bound parameters are not free Mono import fields. |

These are not three arbitrary interpretations to choose because the export
name is the same. SG §3.4 requires exactly the provider derivation/evidence
appropriate to the real construction (`270–292,305–320`). The current artifact
set supplies none of those three installation receipts for this provider.
The source shape `pub id x = x` routes through Parameter/Lambda/Name and source
publication once faithfully elaborated and independently justified; it does
not by itself supply those semantic premises or the importer correspondence.

In particular, syntax `use ... as identity` is an **exposure-name alias** in
the module resolver. It is not automatically SRC-J `alias(h,j)`, whose premise
is an existing monomorphic handle. The same export may be exposed twice while
each lawful Published/Family Name instantiates independently. Conversely two
names for an already installed Mono must share its certificate. Resolver-key
equality alone cannot distinguish these cases.

## Complete roots remain a separate obligation

The caller candidate's `root_inventory` compares every direct CST root and
HIR item in order, verifies exact ranges, and retains Import versus Binding
(`original_caller_reify.rs:153–188`). `HirItem::Import` is admitted only by the
complete parse-bound source resolver; the existing tests retain negative cases
for implicit-only, syntax-only, selected-root and foreign-parse environments
(`module.rs:4838–4862`). These tests were inspected only. Import lowering
retains its range, not source linking semantics (`module.rs:3539–3546`).

OriginalSource has three statement constructors: `letS`, `expressionS`, and
`moduleS`; it has no raw `use` constructor (`OriginalSourceSyntax.lean:117–119`).
`moduleS` registers one independently interpreted `sourceModuleLinking` atom
and recurses into an already supplied Source statement body
(`OriginalSourceGeneration.lean:344–347`). It neither consumes a Rust
SourceImportEnvironment nor constructs an imported Context. A symbol search
in `YulangClosure` found `sourceModuleLinking` only at its syntax inventory and
this generation clause; no SourceExportId/SourceImportEnvironment bridge is
defined there.

Consequently, even a successful complete ordered root table would still need
an adopted, authenticated elaboration relation that accounts for the explicit
use root, implicit prelude installation, every declaration/initializer and
their source order, and produces the resolved Source plus its Context and
linking premises. Dropping the use row or replacing it by an arbitrary empty
`moduleS` does not establish that relation. The selected nested-shadowing
subtree's accepted owner map remains useful but covers no other root.

## Coverage, resources and handoff

Commands were source reads/searches and Python hashing of pinned bytes. No
Cargo, compiler, Lean/Lake/checker, tests, formatter or Git command ran; no
execution trace was generated. The prior caller failure and the existing test
expectations are preserved evidence, not independent executions. Resource
usage is source reading only; exact CPU/memory measurement is unavailable.
No original source domain or semantic rule was changed. All original parent
gates remain OPEN. Writes stop with this handoff.

Recommended next action: independently review this field audit together with
the proof-rule lane, then assemble the smallest concrete import-elaboration
construction that retains actual provider publication/family/Mono evidence
and complete root correspondence. If that construction needs a new semantic
decision, present its reviewed alternatives and consequences before adoption;
do not ask the user to choose a Binding kind without its owning evidence.

Commit packet for the primary: exact path
`tasks/agent-loop/inbox/import-source-authority-20261027-source.md`; baseline
`6da3e4a45`; no dependency hashes changed; review pending; checks already run:
61 unique input hashes matched, static source inspection only. Proposed
checkpoint message: `Record import source owner and Binding authority gaps`.
Shared-record deltas left for the primary: source lane STOPPED, no verifier
expenditure, imported Context and complete import-root elaboration OPEN;
capacity override remains idempotent and path quarantines retained.
