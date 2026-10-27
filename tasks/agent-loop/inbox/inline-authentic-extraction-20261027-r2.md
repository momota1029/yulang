# INLINE-AUTHENTIC-EXTRACTION-20261027/r2 — proof lane

Assignment `/root/inline_authentic_extraction_proof_r2`; revision 2, phase 1
**FROZEN OWNER INSPECTION / WAITING FOR EXECUTED TRACE**. Contract
`tasks/agent-loop/sprints/inline-authentic-extraction-20261027-r2.md`, SHA-256
`af6c0f6e462f6ad414f7c82572216422925fe9ff3a68c1fe8d99df8f1605672e`;
assignment baseline `1cc8406e3`, contract parent baseline
`232b024e0d793714027170a388ab746ce0d2b429`. Requested role `lean_prover`;
observed model, effort and session UUID UNKNOWN. No descendants or Git operations.

## Original source and unchanged parents

Authority: `notes/design/2026-10-08-source-generalize-definition.md` §2 selects
`notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §§3–5.
Inspected §3.1 Parameter/Lambda/Name/Bind/Call, §3.3 source-owned scopes and
§§4–5 rule construction/publication. Original syntax inventory is
`docs/yulang-source-type-safety-ja.tex` `sec:source` and `sec:all-source`:
13 expressions, 11 patterns, 3 statements. Its opening correction/status
notice remains binding; the unreviewed integration manuscript grants no blanket
semantic authority or frontend correspondence.

Original whole parent: `docs/yulang-whole-proof-closure-ja.md` §§1/4 and
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1/3/5,
with the authoritative `2026-10-24-birth-level-scc-intrusion.md` §§2–6
correction and unchanged 2026-10-11 top-level inference principles. Preserve
every supported source program, lawful finite construction history, retained
extrusion occurrence, original lexical/type/event scopes, shared joint
witness, accepted natural inference, complete Call and effects. The parent
soundness/effect hygiene/principal coverage/progress/termination/source-native/
whole-language/receipt/admission/production gates all remain OPEN.
`YulangClosure.SourceProblem.InferenceSoundness`, `PrincipalCoverage` and
`InferenceTermination` in `Contracts.lean:128/138/152` are proposition
definitions; no concrete instance follows here.

## Exact inspected owner equations

- `crates/yu-syntax/src/full_parse.rs:72–138`: `SourceNodeKey` retains parse
  Arc, green-node allocation and byte start. Equality compares those three;
  `ParsedFile::owns_source_key` checks the parse Arc. Source paths and ranges
  are locators, not a replacement identity.
- `crates/yu-hir/src/module.rs:1377–1418`: `HirParameterId` contains
  `SourceRootId` and ordinal; equality/hash retain both. An ordinal alone
  loses its owner. `local_source.rs:1433–1437` creates it from the current
  owner and checked next-parameter counter.
- `local_source.rs:50–62/169–178/1484–1493`: `LocalSourceIndex` contains
  owner and arena ordinal; `LocalSource::expression` requires the same owner
  before indexing. `slot` allocates the arena index.
- `local_source.rs:2092–2122`: the inline Lambda builder checks the actual
  backslash/Identifier/arrow/body constructor, records the exact binder token
  range, constructs an unannotated `LocalSourceParameter` with neither unit
  nor record pattern, and retains the body index. It pushes the branded
  parameter binding and schedules `Work::Restore` around the body.
- `source_identity.rs:152–157`: `record_inline_parameter` records only
  `HirParameterSourceOrigin::InlineLambda { lambda, binder_range }` in the
  parameter-owner map. It emits no OriginalSource tuple.
- `local_source.rs:1438–1481/2137–2162`: `push_binding` retains prior lexical
  entries; `restore` reestablishes them; Identifier resolution takes the
  latest spelling's stored `LocalSourceResolution`, otherwise namespace
  resolution. This is concrete Rust ownership/lookup code, not a proved
  refinement into `OriginalSource.lookupBinding`.
- `local_source.rs:131–165/1520–1550`: published occurrence ordinals are
  assigned by source descendant order and map back to parse keys; temporary
  occurrence assignment/arena order is distinct. The comment explicitly
  distinguishes candidate worklist order from published source child order.
- `shadow.rs:1787–1829/1871–1889`: `parameter_source_origin` checks HIR/root
  ownership, the same parse, the Lambda position and its unique Identifier
  token with the retained binder range. `parameter_source_position` returning
  `MissingSource` for InlineLambda is its documented narrower interface.
  `source_position` rejects foreign parse and ambiguous/missing keys.
- `tools/inference-playground/src/runtime/program.rs:160–164/213/598–604/972`:
  runtime `SourceSite` retains `{ source_root, occurrence, range }` and
  `from_hir_with_roots` computes a code `Label(offset + index.ordinal())`
  only after `source.expression(index)` succeeds. This is an actual runtime
  label allocation equation. It is not an equation into original Nat `Site`,
  `Name`, `Declaration`, root `Context` or ambient `ScopeEntry`.

The original definitions inspected are
`YulangClosure.OriginalSource.{Site,Name,Declaration,Context,Source}` in
`OriginalSourceSyntax.lean:20–22/79–146/198`,
`OriginalSourceEvents.ScopeEntry`/`sourceOwners`,
`OriginalParameterWorld.Parameter.{source,registration,typeScope}`,
`OriginalFormalShared.{formalContext,bodyContext,lambdaTree,actual_lambda_tree}`,
and `OriginalIdentityRealization.Identity`/`Identity.parameter`.
`Identity` has declaration, ambient telescope, root Context, lambdaSite,
formalSite, patternSite, nameSite and Name. `Identity.parameter` builds a
formal plus a separate administrative `.wild patternSite` and resolved `.name`.
The physical binder token is not a Wild CST node; formal and administrative
wild remain different coordinates even though raw Nat inequality is unproved.

`OriginalInlineIdentityInterpretation.lean:74–117` has candidate arithmetic
`coordinateCode`/`parameterName` and caller-supplied
`Expansion.{declaration,ambient,context}`. Its opening notice explicitly says
these are candidate conventions with no authentic extraction theorem.
`OriginalIdentityFrontendJoin.lean:14–30` exposes this same frontend boundary.
A focused search of `Original*.lean` finds actual Rust owner names only in
those two explanatory modules; this is a bounded inspection observation,
not a theorem asserting universal absence of all possible allocation laws.

## First missing owner equation and parent application

Required owner: the original-source/frontend interpretation (primary source/
proof integration), consuming one authenticated ParsedFile + HIR + LocalSource
root and its actual surrounding ordered graph. It must construct the original
resolved declaration, ambient `List ScopeEntry`, containing `Context`, Lambda
Site, distinct formal/admin-wild coordinates, Name occurrence Site, resolved
lexical Name, enclosing Apply Site and original argument. Its equations must
preserve the actual parameter identity/resolution and explicit Group→inner
projection, rather than identify the raw Apply callee with the projected
Lambda or reuse a runtime label/ordinal as an original Site by convention.

The inspected owners above establish only branded frontend provenance and
runtime labels. They do not supply this original tuple or its incidence and
scope equations. No general impossibility claim or source-qualified
counterexample is made. Next discriminating evidence is an executed frozen
trace plus the owner-supplied original interpretation equation; the trace alone
can establish finite ranges/constructors/order/resolution without filling the
original allocator.

Available reviewed equations, still only source-stated here, are the fully
qualified `YulangClosure.OriginalIdentityEntryOrigin.identity_source`,
`identity_registration`, `identity_registration_operands`,
`identity_closure_owner`, `identity_application_owners`,
`identity_application_ports`, `identity_invocation_owner`,
`identity_receipt_owner`, `identity_value_entry_sequence`,
`identity_name_binding` and `identity_name_rule`. All quantify over an already
constructed `OriginalIdentityRealization.Identity`; Apply equations additionally
accept an original callSite and whole original argument. Applying them before
the missing construction would assume the missing bridge. None has been
specialized to invented Nat coordinates here.

## Checks, writes and resource receipt

Read the Lean proof skill and both references, root AGENTS/pre-sprint,
goal-driven sprint rules, current state/README and the exact contract.
A Python SHA-256 check of all 28 rows in the r1 frozen-input table returned
`{'pin_count': 28, 'mismatches': []}` (exit 0); r2 contract hash matched exactly.
Read current `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`: pin
Lean 4.35.0; project flags `-j1 -M1024`; no external packages. No executable
version or checker receipt is claimed.

Checker calls: **0/6**, checker seconds **0/360**. No Lean/Lake/Cargo/test
process started by this lane. No theorem constructed, kernel acceptance,
type printing, axiom audit, independent review, trace/data construction or full
import-cone checker audit has occurred. These are pending trace arrival.
No represented finite instance yet; no original constructor is removed from
parent scope. Phase-1 source read/hash work only; no source counterexample.

Writes: this handoff only. Scratch directory
`/tmp/yulang-inline-authentic-extraction-20261027-r2/proof` exists and is empty.
Leased proof/audit Lean modules are not created. Inspection-phase writes stopped;
lane WAITING for primary's frozen graph/trace/versioned contract acknowledgement.
Budget remains the fixed proof 1200 active seconds and <=6 checker calls/360s;
this handoff grants no renewal or independent certification.

## Inspected dependency/source hashes

These are file-byte pins for the bounded inspection, not a compiled imported
source-cone receipt. All hashes were computed directly with Python SHA-256.

| Path | SHA-256 |
| --- | --- |
| `crates/yu-syntax/src/full_parse.rs` | `dd92603f8f5549b8b3f6e45ab6cb39b6598480b7f1cda7897e27b5113107db93` |
| `crates/yu-hir/src/module.rs` | `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `crates/yu-hir/src/source_identity.rs` | `4bd5fa4066a1fd445a9757374c44d602decd1d791a394cd81c6066efa063fb23` |
| `crates/yu-hir/src/shadow.rs` | `b964bab6dcdb7ebeca9f964c134ac8fb041c928c20ce0a895fea6b6af0fbb93e` |
| `tools/inference-playground/src/runtime/program.rs` | `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907` |
| `tools/inference-playground/src/runtime/machine.rs` | `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e` |
| `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `notes/theory/lean/YulangClosure/OriginalSourceEvents.lean` | `cfd5f502a1e68a97e27e11a75400fae8789f167c92596aedb08ef7dfbb724342` |
| `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` |
| `notes/theory/lean/YulangClosure/OriginalParameterWorld.lean` | `7b5f849f744dbe56f374d8be6b11a5a218176abf6eeda2fb9da8180c7b1ff802` |
| `notes/theory/lean/YulangClosure/OriginalFormalShared.lean` | `abb9d69546e284fcb5fe6be9bb3c18269227e91da94e09eebf1a62e0b56e67f7` |
| `notes/theory/lean/YulangClosure/OriginalIdentityRealization.lean` | `30b0676f4af22dc7da2c75596a338db57a24b17662a4057801cfdff7ab4a2f42` |
| `notes/theory/lean/YulangClosure/OriginalIdentityEntryOrigin.lean` | `9df7fccfe03becec491665a28a7fb65760e1245d76e68330fc9626da5533163e` |
| `notes/theory/lean/YulangClosure/OriginalIdentityFrontendJoin.lean` | `cc89fcd3d541b6f9f789a7e2a89a7568545bb9f6a6883d0fa043fb1669e7fd1f` |
| `notes/theory/lean/YulangClosure/OriginalInlineIdentityInterpretation.lean` | `3aca1be7523880d0fef1cc8b2991ade174fda2c79445e9e9014982eccccb352a` |
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `docs/yulang-source-type-safety-ja.tex` | `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166` |
| `docs/yulang-whole-proof-closure-ja.md` | `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5` |
| `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/design/2026-10-24-birth-level-scc-intrusion.md` | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
