# SOURCE-ORIGINAL-OWNER-REIFICATION-20261027/r5

Status: Luna-approved versioned continuation; original inference/executor goal remains OPEN
Branch / baseline: `yulang3` / `a5d1e79ee` (r4 contract pin correction; no language or dependency changes since r1)
Authority: user-provided continuing goal for full Lean proofs and Rust inference/executor; `AGENTS.md`; `rules/goal-driven-sprints.md`; original source clauses listed below
Contract revision: r5; supersedes r4 for the exact Cargo.lock pin correction; source scope, exact output leases and total resource cap do not expand or reset.

## Original outcome and success evidence

The unchanged parent is the full Yulang type-inference/executor correctness goal:
original supported source domain and quantifiers; Rust source-to-constraints,
propagation and execution; Lean proofs of soundness, effect hygiene,
principality and termination, plus required source/native bridges. Every parent
gate remains OPEN unless its own required proof/review/application closes it.

This sprint targets the named source-owner boundary
`SOURCE-ORIGINAL-OWNER-REIFICATION-1`: construct the original source-owned
identity and enclosing application for the accepted r2 fixture from the actual
ParsedFile/HIR/LocalSource/Shadow owners, with a checked Lean consumer that
applies existing `OriginalIdentityEntryOrigin` equations. Use typed origin
tables and a checked table-to-source relation; physical sites, formal sites,
administrative wild sites and resolved names remain distinct coordinates.
Never infer allocation from a newly chosen Nat code or runtime label.

Fixed outcome: either deliver a fresh-reviewed finite source-owned
reification/Identity/application instance, or identify the first unavailable
allocation/constructor equation at its actual Rust owner, with a checked Lean
interface stating exactly which premise is absent. A finite instance is not a
universal frontend refinement and closes none of the full parent gates by
itself. Success is judged by the new equation/instance or a strictly localized
owner obstruction, not by artifact or test counts.

Fixture held fixed from r2: `my value = \\x -> { (\\x -> x) x; x }`.
Retain the outer declaration/binding and containing source boundary, outer and
inner Lambda, exact binder token, raw Apply callee and Group projection, actual
argument, ordered body incidence, nested resolution and restored sibling.
Falsify with same-spelling shadowed parameters, foreign parse/HIR ownership,
reordered occurrences, wrong Group projection, fabricated root Context or
declaration, and conflated formal/administrative-wild/physical coordinates.

Before-state: r2 provides an executed authentic Rust/HIR trace and twelve
checked finite Lean theorems with empty transitive axiom sets, independently
reviewed for that exact trace. It does not construct original Site/Name/
Declaration/Context or the ambient event telescope. After-state must establish
the typed owner relation and apply the existing original source constructors,
or name the exact missing owner equation. Universal frontend refinement,
original A/B, soundness, effect hygiene, principality, progress/termination,
complete Call, source/native, receipt/admission and production remain OPEN.

## Governing sources and frozen inputs

- Contract/baseline HEAD: `1e65096fe5eacf74ced2fca0d1a2e497203d6227`.
- Reviewed r2 outcome: `tasks/agent-loop/sprints/inline-authentic-extraction-20261027-r2-outcome.md`, SHA-256 `8f8b03bcd6bfb92ab7d48a7366e2da0dee8740bf5b1456f7f3ab0143eab2faf3`.
- Authenticated Rust trace: `notes/theory/lean/YulangClosure/OriginalAuthenticInlineExtractionTraceR2.lean`, `73a4a8aa65e5d7d44611a70e52b9d2b6ac5940c2292a7c06e01e69834f2ac5e3`.
- Finite Lean consumer: `notes/theory/lean/YulangClosure/OriginalAuthenticInlineExtractionR2.lean`, `ed25ec65c5760e4a523fabe75f392c67476a710d3af60e345c07e5bf5eaeeb09`.
- Prior interpretation candidate (conditional only): `notes/theory/lean/YulangClosure/OriginalInlineIdentityInterpretation.lean`, `3aca1be7523880d0fef1cc8b2991ade174fda2c79445e9e9014982eccccb352a`.
- Original constructors/consumers: `OriginalSourceSyntax.lean` `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`; `OriginalSourceGeneration.lean` `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`; `OriginalSourceEnvironment.lean` `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132`; `OriginalSourceEvents.lean` `cfd5f502a1e68a97e27e11a75400fae8789f167c92596aedb08ef7dfbb724342`; `OriginalFormalShared.lean` `abb9d69546e284fcb5fe6be9bb3c18269227e91da94e09eebf1a62e0b56e67f7`; `OriginalIdentityRealization.lean` `30b0676f4af22dc7da2c75596a338db57a24b17662a4057801cfdff7ab4a2f42`; `OriginalIdentityEntryOrigin.lean` `9df7fccfe03becec491665a28a7fb65760e1245d76e68330fc9626da5533163e`.
- Rust owner pins: `crates/yu-syntax/src/full_parse.rs` `dd92603f8f5549b8b3f6e45ab6cb39b6598480b7f1cda7897e27b5113107db93`; `crates/yu-hir/src/module.rs` `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`; `crates/yu-hir/src/module/local_source.rs` `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1`; `crates/yu-hir/src/source_identity.rs` `4bd5fa4066a1fd445a9757374c44d602decd1d791a394cd81c6066efa063fb23`; `crates/yu-hir/src/shadow.rs` `b964bab6dcdb7ebeca9f964c134ac8fb041c928c20ce0a895fea6b6af0fbb93e`.
- Isolated runner inputs (immutable): `tools/inline-authentic-extraction/Cargo.toml` `21c64b4a22318a1ae89c346357161812a6ac313b6f0c4999853272cf73e2832b`; `Cargo.lock` `2ee467b8f6416aa7dda36f96e3401a0b0ae24a739ff7c6a2efccc1323777ee91`; existing `src/main.rs` `fc22f1ab490e815a800a6b1e91eb4ea978006d6956ac838329cddf7b09ad1472`.
- Governing original definition: `notes/design/2026-10-08-source-generalize-definition.md` and `notes/theory/2026-10-08-source-generalize-definition-and-proof.md`; plus the identity/entry-origin Lean modules above. These specify source data and event-owner walks; this sprint may not replace their accepted constructors or meanings.
- Revalidate every pin and the complete Lean project/toolchain import cone before consuming or checking outputs. Lean remains project-pinned 4.35.0. No dependency change or network resolution.

## Versioned schema repair and exact amendment

R1's candidate schema prefix SHA-256 `3bd35c260b390350b5cef5d01f548bc909a643e700dd3bc7bd8f5f159e45ba89` was inspected before implementation consumption and rejected as incomplete. Its `TableToSource` constructors did not require exact `PhysicalRow` membership; its Name resolution did not join `parameterOrdinal` through the matching `FormalRow` and `NameRow`. The byte-exact r1 candidate remains preserved at `/tmp/yulang-source-owner-reification-20261027/proof/schema-prefix.lean`; the corrected r2 candidate (`630ae255e08940b249ab28f1e951ddfd1b63ba232399879e68a4ad39bfd91c9c`) is preserved at `/tmp/yulang-source-owner-reification-20261027/proof/schema-prefix-r2.lean`. The r2 candidate also failed schema review before implementation consumption because `AdminStatementKey.application` was not joined to the first ordered BodyRow. Its first Lean check (call 1/6) exited 1: `syntax` is reserved as a field identifier and `name` is invalid in the relevant pattern binding. The complete failure log is preserved in the proof scratch; this failed call remains charged. Neither candidate supplies admitted source evidence or implementation authority. The r3 candidate is preserved at `/tmp/yulang-source-owner-reification-20261027/proof/schema-prefix-r3.lean`, SHA-256 `78e37e98428be93ac7db801394f733caa29528a7f9675c8224d3a27bcc6b1430`; it was not consumed and has not yet received Luna schema acknowledgment.

Before implementation writes, proof must freeze a corrected r5 schema prefix that:

1. requires, for each physical expression constructor, an exact same-key `PhysicalRow` membership and occurrence/source-key/range join where the row denotes a real HIR occurrence (administrative statement/wild rows remain typed non-HIR origins);
2. connects each resolved `NameRow` and `ResolutionRow` through the exact actual `FormalRow`, including matching `FormalKey`, `parameterOrdinal`, lambda owner and authentic same-root resolution identity; spelling equality alone is never a join;
3. retains the raw Group owner and authenticated projected child edge, the complete ordered body incidence, exact binder token and actual Apply argument; and
4. renames the invalid Lean identifiers (`syntax` and the conflicting pattern binder) while preserving their data meaning;
5. gives administrative statement sites their own typed `AdminStatementRow` membership joining key, enclosing block, source order 0 and the exact first expression occurrence; do not claim the administrative statement is a CST/HIR physical node; and
6. allows a finite typed coordinate representation to be constructed from authenticated owner keys only when its functional/injective consistency and table-to-source equations are proved; this is a reification of the original formal source data, not a claim that Rust emitted the same Nat values; and
7. carries explicit root scope/context provenance linked to the actual containing module/resolver owner; a missing row is not evidence of an empty scope. Derive the inner Context from the outer Lambda source rules and derive the target ambient `ScopeEntry` list from the actual matching owner in the full root `sourceOwners` walk. Keep that ambient list distinct from the `Telescope` supplied to `Identity.introduction`, which must be derived from the actual owner route. Never assume an empty Context, ambient list, telescope or declaration. If those owner links cannot be constructed, preserve them as the precise OPEN premise.

Luna must inspect the revised schema, verify its exact byte snapshot/hash, record that hash and its exact file-slice boundary in `current.json`, and send explicit acknowledgment to both lanes. The implementation remains read-only until this occurs. The Cargo.lock SHA-256 in r1-r4 was incorrect; r4 still had a character substitution despite the right length. The actual current SHA-256 is `2ee467b8f6416aa7dda36f96e3401a0b0ae24a739ff7c6a2efccc1323777ee91`. The input dependency bytes did not change. The proof schema must expose a constructible typed coordinate map with the exact owner-preservation laws and a root scope/context origin interface; it may leave an uninhabited/evidence-free field OPEN but may not use a default. Proof may replace the unconsumed r1/r2/r3 candidate prefix only under this r5 grant and after retaining all prior snapshots. This revision is not an extension or reset of the 5400-second envelope; all r1/r2/r3 time, Lean calls and Cargo calls remain charged. The failed schema check is Lean call 1/6; at most five remain. No other Lean check has started.

## Two continuing lanes

**Proof — registered `lean_prover`, 1800 active seconds.** Own the Lean interface, table-to-source relation, finite reification theorem, parent application attempt and complete type/axiom audit. Construct finite coordinate maps only from authenticated typed owner keys, with checked consistency and table-to-source equations; derive the containing Context from actual module/resolver scope data, and derive the ambient event telescope by the actual `sourceRules`/`OriginalSourceEvents.owners` walk. Do not insert arbitrary `Expansion` fields, empty contexts/telescopes, convenient fresh labels, or a supplied successful correspondence proposition. Reuse the reviewed `OriginalIdentityEntryOrigin` equations only after their `Identity` is constructed. First freeze the schema in `OriginalSourceOwnerReification.lean`; implementation must consume that frozen interface.

**Implementation — registered Luna/high `implementer`, 1500 active seconds.** Own a provisional research adapter only, using the immutable existing runner/package and the authenticated r2 source path. Inspect actual declaration, expression, formal, binding, scope and event-owner identities. Emit typed provenance plus the complete fixture source needed by the Lean schema; preserve constructor identity and ordered incidence. Reject foreign roots/parses and mismatched token/source origins before output. Do not edit compiler/HIR/parser/runtime semantics, expected outputs or dependency manifests/lockfiles. If a constructed finite reification cannot be shown faithful to the original resolved source/declaration/context relation, return the exact owner boundary rather than inventing one.

Lanes are disjoint. The implementer may inspect and map existing owners while proof repairs the schema, but must not create its leased Rust file or trace until Luna records the corrected r5 schema SHA-256 in `current.json` and acknowledges the immutable interface. Proof can continue independent owner-equation work during that wait. Once r5 schema is frozen, implementation consumes that exact hash; proof consumes only the executed, frozen trace. Further schema change requires another versioned contract revision before writes.

**Fresh independent review — registered `compiler_referee`, 1200 active seconds**, after both artifacts/handoffs and direct inputs freeze. Review source-owner authenticity, each origin-table equation, full Identity tuple, event telescope, exact argument/Group projection, Lean proof/audit and parent application. Author/coauthor cannot review.

## Permissions, exact leases and resources

Exact implementation outputs:
- `tools/inline-authentic-extraction/src/bin/original_owner_reify.rs`
- `notes/theory/lean/YulangClosure/OriginalSourceOwnerReificationTrace.lean`
- `tasks/agent-loop/inbox/source-owner-reification-20261027-source.md`

Exact proof outputs:
- `notes/theory/lean/YulangClosure/OriginalSourceOwnerReification.lean`
- `notes/theory/lean/AuditOriginalSourceOwnerReification.lean`
- `tasks/agent-loop/inbox/source-owner-reification-20261027.md`

Fresh review output: `tasks/agent-loop/inbox/source-owner-reification-20261027-review.md`.
Primary-only outputs: this contract, `tasks/agent-loop/sprints/source-owner-reification-20261027-r1-outcome.md`, and existing `tasks/agent-loop/current.json`.
Exact isolated scratch roots: `/tmp/yulang-source-owner-reification-20261027/impl/` and `/tmp/yulang-source-owner-reification-20261027/proof/`; review is read-only.

Total envelope: 5400 active seconds—proof 1800, implementation 1500, Luna integration 600, independent review 1200, dispatch 300. Astra 0. One heavy verification process at a time; at most two offline/locked Cargo runs, 120 seconds each, 1 CPU/1 GiB; at most six Lean source-checking runs / 360 seconds total. All execution receipts live under the exact scratch roots. No tests are requested or authorized by this contract; do not run them. No retry or resource reset. A genuine missing-owner result does not authorize a larger or different sprint.

No compiler or dependency file is leased. Nine earlier capacity reservations remain released idempotently; that grants neither paths nor authority. Legacy UNKNOWN observations and exact quarantines remain intact and off limits. All new paths above are checked disjoint from those quarantines. RUNNING is recorded only after actual launch acknowledgement with current worker/session and active-work receipt; otherwise use ASSIGNED/WAITING or UNKNOWN accurately.

## Frozen seam, parent application and stop conditions

Use explicit typed coordinate types/records so physical source sites, formal sites, administrative wildcard sites, declarations and resolved names cannot be silently interchanged. Every emitted origin must join to its exact same-owner HIR occurrence/parameter/source key and exact syntax range; preserve raw Group edges. A finite Nat representation is admissible only as a constructed owner-key reification with the checked equations above, never as a selected convention standing alone. The Lean reifier must establish the complete concrete `Identity` tuple (declaration, ambient scope entries, Context, Lambda/formal/admin-wild/Name Sites and Name), enclosing application call site, actual complete argument, target owner route, and `Telescope` derived from that route. `Identity.ambient` is the scope prefix at the target source owner; it is not itself the event Telescope. Then apply at least the relevant identity source, registration, body-binding, application-owner and event-owner equations. If the root declaration/Context/telescope allocator is absent, expose precisely that owner equation as OPEN; no inferred fallback.

Review snapshot freezes implementation, schema, trace, proof, audit and direct source hashes together. The reviewer returns to Luna; only Luna adjudicates and may integrate. Stop on foreign-owner acceptance, coordinate conflation/collision, wrong token or incidence, omitted/corrupted argument/body, unsupported Group projection, fabricated root owner/Context/telescope, pin/dependency drift, lease conflict, unbounded resource use, or the exact missing-owner boundary. Preserve failed receipts; do not retry beyond the grant.

Continuation within this sprint may repair or extend the reifier and proof only under these exact paths, pins, schema, semantics and limits. Consult dispatcher again at a genuine owner/authority/dependency/lease/resource obstruction, frozen review seam or END. A reviewed finite instance is source/native evidence only; original A/B and whole-language/production gates stay OPEN. Luna alone stages explicit paths, commits and pushes the coherent reviewed slice.
