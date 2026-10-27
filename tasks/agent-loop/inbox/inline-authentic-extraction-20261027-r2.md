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


## Final proof handoff — executed trace consumer, frozen revision 3

This section supersedes the phase-1 WAITING/writes/checker status above;
phase-1 source investigation and its original frontier remain preserved.
Same identity `/root/inline_authentic_extraction_proof_r2`; actual session UUID,
model/effort and total active-time meter remain UNKNOWN. No descendants.
Authority is the primary's explicit rev6 resume plus
`tasks/agent-loop/sprints/inline-authentic-extraction-20261027-r2-rev6.md`
SHA-256 `a650bdbd86b3b88fe18d7b1200e4303b7237e3db4863411d075b11891529fbde`.
Acknowledged repaired Rust source hash
`fc22f1ab490e815a800a6b1e91eb4ea978006d6956ac838329cddf7b09ad1472`,
implementation handoff rev5 hash
`976fc2b754263b3afb534dfcc32e1e00895269036f0378fc3c732cce0de345b9`,
and generated trace hash
`73a4a8aa65e5d7d44611a70e52b9d2b6ac5940c2292a7c06e01e69834f2ac5e3`
were computed directly and all matched before construction. The trace was never
edited by this lane. Source producer owns the successful Cargo execution
receipt (call 6/6, exit 0, 1.46 seconds); this lane did not run Cargo.

### Result, scope and exact parent application

`YulangClosure.OriginalAuthenticInlineExtractionR2` contains twelve checked
finite-data theorems, whose full originating types and complete transitive axiom
results appear below. No theorem takes additional hypotheses. All twelve
printed axiom sets are empty. They establish facts about the actual generated
trace: UTF-8 length; bounds of every serialized position; exact binder bytes and
token rows; the full six-field Group edge and distinct raw/projected indices;
Group range nesting; actual Apply tail-range convention; all seven fields of
both ordered direct StatementBlock children; all eight fields of all three Name
rows; Name/position joins; and the outer/inner/outer ordinal snapshot.
`foreign_report_inventory` proves only the exact emitted four-string list.
No literal Bool flag is used to derive a Rust execution fact.

The authentic fixture is one unannotated outer Lambda with a StatementBlock,
one statement-expression Apply, one raw Group edge to a nested same-spelling
Lambda, one inner body Name, an outer-parameter argument and one restored final
Name. Its outer/inner parameter ordinals are 0/1; arena indices and published
occurrence ordinals are retained separately. There are no binding-statement
initializers, Sequence instances, annotated/computation/record/unit formals,
multiple Group edges or arbitrary source forms represented by this one trace.
Those cases remain in the unchanged parent domain; this result omits them from
its finite claim rather than assuming them away from a universal theorem.

A material actual source convention is preserved: `applySourceForm` is
`MlArgument` and `applyRange = rawApplyArgumentRange = (29,30)`; the raw callee
range is `(19,28)`. Thus a purported whole-Apply containment fact would be
false for this authentic trace. `apply_tail_range` checks the actual convention;
it does not alter any source owner. Inner-body Name range `(25,27)` retains
trailing whitespace, so only the actual binder-token ranges are equated to the
single byte `x`.

Application to the original parent reaches precisely the previously identified
allocation seam. These checked finite coordinates/lookup rows are now available
as concrete input facts. They still do not construct
`OriginalIdentityRealization.Identity` from this Rust owner. No inspected owner
supplies the original declaration, ambient telescope, containing Context,
Lambda/formal/admin-wild/name Sites, Name, Apply Site, original whole argument or
its Group projection equation. Therefore no application of
`OriginalIdentityEntryOrigin` to this trace is justified or claimed. Supplying
an arbitrary Identity or a candidate Nat convention would assume this very
missing premise; no conditional replacement lemma was added.
Next owner remains the primary's original-source/frontend interpretation lane,
which must construct the full tuple and prove the original source/lexical/scope
incidence equations from the authenticated surrounding graph. The finite trace
is neither a proof of universal frontend refinement nor a counterexample to the
possibility of that bridge.

Independent foreign parse/HIR rejection is the external executed assertion
path in the frozen Rust source/run, not the serialized strings. Registered
binder-range equality likewise relies on that executed path; Lean independently
checks byte slices and the token-position rows but the registered parameter
ranges are not separate fields in the trace. Pointer/root brands are not
serialized or reconstructed. The bound source-schema inspection also found
that hypothetical binding rows omit initializer incidence; the actual trace has
no such row. All original A/B, soundness, effect hygiene, principality,
progress/termination, full Call, source/native, receipt/readout/admission,
whole-language and production parents remain OPEN. No independent review or
production authority is claimed.

### Pinned environment, actual commands and failure retention

Read-only `elan which lake` returned
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`
(exit 0). The skill checker actually printed:

```text
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

Native binary SHA-256: Lake
`8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1`,
Lean `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.
No installation, dependency update, root-import edit, test or global-default
change occurred.

Verification used one exclusively owned minimal project copy under
`/tmp/yulang-inline-authentic-extraction-20261027-r2/proof/project`.
Its pin/lakefile/manifest are byte copies of the unchanged project inputs;
only the actual generated trace and this consumer/audit were copied. It has no
root import/default-target build. Explicit module build refreshed the actual
trace and consumer imports before checking. Shared repository `.lake` was not
written. The checker sets `LEAN_NUM_THREADS=1`; project and manual audit use
`-j1 -M1024`. No overlapping verifier was started by this lane.

Checker wrapper calls 1/2 used the following exact argv (also stored as JSON):

```text
python3 /home/momota1029/rust/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py --project /tmp/yulang-inline-authentic-extraction-20261027-r2/proof/project --lake /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --module YulangClosure.OriginalAuthenticInlineExtractionR2 --timeout 120 --theorem YulangClosure.OriginalAuthenticInlineExtractionR2.input_byte_length --theorem YulangClosure.OriginalAuthenticInlineExtractionR2.all_position_ranges --theorem YulangClosure.OriginalAuthenticInlineExtractionR2.exact_binder_bytes --theorem YulangClosure.OriginalAuthenticInlineExtractionR2.binder_position_rows --theorem YulangClosure.OriginalAuthenticInlineExtractionR2.group_projection_incidence --theorem YulangClosure.OriginalAuthenticInlineExtractionR2.group_range_contains_projected_lambda --theorem YulangClosure.OriginalAuthenticInlineExtractionR2.apply_tail_range --theorem YulangClosure.OriginalAuthenticInlineExtractionR2.complete_direct_body_incidence --theorem YulangClosure.OriginalAuthenticInlineExtractionR2.exact_name_resolution_rows --theorem YulangClosure.OriginalAuthenticInlineExtractionR2.names_have_source_positions --theorem YulangClosure.OriginalAuthenticInlineExtractionR2.shadow_and_restoration_snapshot --theorem YulangClosure.OriginalAuthenticInlineExtractionR2.foreign_report_inventory
```

Call 1 failed: exit 1, 3.164 seconds. Its log preserves actual goals/diagnostics:
missing `Decidable` synthesis for the opaque `ValidRange` bounded forall and
large tuple equalities, plus UTF-8 `ByteArray.toList` reduction stuck in
`exact_binder_bytes`. Repairs were proof-local: unfold `ValidRange`, use
explicit constructor/reflexivity terms for definitionally equal tuple rows, and
inspect UTF-8 array data directly via `.data.toList`. No trace or theorem claim
was weakened. Call 2 passed: exit 0, 2.676 seconds; it built the consumer and
printed/audited all twelve declarations. The first failing log is retained.

Call 3 checked the delivered audit file with this exact command, cwd the
isolated project and `LEAN_NUM_THREADS=1`, outer timeout 60 seconds:

```text
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache env lean -j1 -M1024 AuditOriginalAuthenticInlineExtractionR2.lean
```

Call 3 passed: exit 0, 2.519 seconds. Total bounded wrapper elapsed time is
8.359 seconds across 3 calls. The wrappers caused 5 actual Lean source-checking
executions: initial trace build + failed consumer, repaired consumer + helper
audit, and delivered audit. Thus both counts are within the <=6-call budget;
version queries are not source checks. No further checker work is pending for
these final bytes. No default whole-project build or root integration check was
run, because the exact import/root path is outside this leaf lease.

Source scan of the three-module project cone found no `sorry`, `admit`, project
axiom, native-evaluation assumption or kernel bypass. The only `axiom` matches
are the audit file's twelve `#print axioms` commands. Kernel dependency output,
not that text scan, establishes the reported empty axiom sets.

### Frozen outputs and full source-cone inventory

| Path | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalAuthenticInlineExtractionR2.lean` | `ed25ec65c5760e4a523fabe75f392c67476a710d3af60e345c07e5bf5eaeeb09` |
| `notes/theory/lean/AuditOriginalAuthenticInlineExtractionR2.lean` | `85e0dd8adcef88c9e10c6aebde526dcb2340a1f58e03a67a5dd4e903f08ad089` |
| `notes/theory/lean/YulangClosure/OriginalAuthenticInlineExtractionTraceR2.lean` | `73a4a8aa65e5d7d44611a70e52b9d2b6ac5940c2292a7c06e01e69834f2ac5e3` |

`full-source-cone.json` recursively inventories all project imports plus implicit
`Init` and the installed standard-library import closure: 656 modules = the
three project modules above and 653 pinned toolchain source files. Every entry
retains source path, SHA-256 and direct imports. The inventory is a source-file
hash manifest; it is not an independent review or additional compiler receipt.
No OriginalIdentityEntryOrigin cone is imported, since no concrete original
application was available. Its source and prior review remain the exact
phase-1 original frontier, not a newly checked dependency of these theorems.

Scratch receipt paths below are relative to
`/tmp/yulang-inline-authentic-extraction-20261027-r2/proof`:

| Artifact | SHA-256 |
| --- | --- |
| `check1.command.json` | `9784c7680852658156c091e41258579696f8a3fa68d54b99484abacef47ba015` |
| `check1.receipt.json` | `f9aadd25029fea4a563b3fa228c63367af1040dd4547e77615914a5995e45d47` |
| `check1.log` | `58c5df986c4e7da0ba54fe4329ae82ea313231f6366cae4e2eb985c36dcf0b10` |
| `check2.command.json` | `9784c7680852658156c091e41258579696f8a3fa68d54b99484abacef47ba015` |
| `check2.receipt.json` | `498b8fd7362626cdf08ce5ca22486f168419297ee7e3ea6a85475b500d156deb` |
| `check2.log` | `d122b73b8e19046b507f4a18e64ca53d8d91b0edb642a966c473e193779cd0a9` |
| `check3.command.json` | `4af26e35a2833c1a8e8724f7c679e509cac933714ca71fe05ff44f8c5d77a3bb` |
| `check3.receipt.json` | `870c888ec332c4c7920793e849c139b399af7b4b1b3392e5dc62544cdff59612` |
| `check3.log` | `3d0573de29b83b9b3e2744c26343bf1e7c7399787d913cc4401a65e9255ee12b` |
| `full-source-cone.json` | `243f41ff5b9ff1f3110c34d74c09bb5e6691a7d7a8e31e2b7dd97ddfd68eb396` |

Other writes under that scratch root: isolated `project/` copies and its
`.lake` build/cache/generated IR/olean/ilean/setup outputs. The skill checker
also created and automatically removed its temporary
`/tmp/yulang-lean-audit-c6rxwpsp/YulangProofAudit.lean`; its complete printed
receipt is in `check2.log`. All generated outputs are accounted for by this
lane. Prior implementation scratch remains outside this lane's ownership.

Repository writes are exactly the consumer Lean file, delivered audit Lean
file and this sequential handoff. The generated trace is read-only input.
All execution has completed; no child/build/Cargo/Lean/Lake process remains
owned by this lane. **Writes stopped** after final handoff freeze. Fresh
non-author review, primary adjudication and Git integration remain with Luna.
No budget reset/refund or theorem-parent promotion is requested.

### Complete delivered theorem-type and axiom receipt

The following is the unabridged stdout of the successfully checked delivered
audit file, not a manually reconstructed type listing:

```text
YulangClosure.OriginalAuthenticInlineExtractionR2.input_byte_length : YulangClosure.OriginalAuthenticInlineExtractionTraceR2.inputUtf8.toUTF8.size =
  YulangClosure.OriginalAuthenticInlineExtractionTraceR2.inputByteLength
'YulangClosure.OriginalAuthenticInlineExtractionR2.input_byte_length' does not depend on any axioms
YulangClosure.OriginalAuthenticInlineExtractionR2.all_position_ranges : ∀
  (row : YulangClosure.OriginalAuthenticInlineExtractionTraceR2.TraceSourcePosition),
  row ∈ YulangClosure.OriginalAuthenticInlineExtractionTraceR2.sourcePositions →
    YulangClosure.OriginalAuthenticInlineExtractionR2.ValidRange row.byteRange
'YulangClosure.OriginalAuthenticInlineExtractionR2.all_position_ranges' does not depend on any axioms
YulangClosure.OriginalAuthenticInlineExtractionR2.exact_binder_bytes : YulangClosure.OriginalAuthenticInlineExtractionR2.bytesAt
      YulangClosure.OriginalAuthenticInlineExtractionTraceR2.outerBinderTokenRange =
    "x".toUTF8.data.toList ∧
  YulangClosure.OriginalAuthenticInlineExtractionR2.bytesAt
      YulangClosure.OriginalAuthenticInlineExtractionTraceR2.innerBinderTokenRange =
    "x".toUTF8.data.toList
'YulangClosure.OriginalAuthenticInlineExtractionR2.exact_binder_bytes' does not depend on any axioms
YulangClosure.OriginalAuthenticInlineExtractionR2.binder_position_rows : List.map
    (fun row => (row.label, row.byteRange))
    (List.filter (fun row => row.kind == "token")
      YulangClosure.OriginalAuthenticInlineExtractionTraceR2.sourcePositions) =
  [("outer-binder-token", YulangClosure.OriginalAuthenticInlineExtractionTraceR2.outerBinderTokenRange),
    ("inner-binder-token", YulangClosure.OriginalAuthenticInlineExtractionTraceR2.innerBinderTokenRange)]
'YulangClosure.OriginalAuthenticInlineExtractionR2.binder_position_rows' does not depend on any axioms
YulangClosure.OriginalAuthenticInlineExtractionR2.group_projection_incidence : List.map
      (fun edge =>
        (edge.groupIndex, edge.innerIndex, edge.groupOccurrence, edge.innerOccurrence, edge.groupRange,
          edge.innerRange))
      YulangClosure.OriginalAuthenticInlineExtractionTraceR2.groupProjectionPath =
    [(YulangClosure.OriginalAuthenticInlineExtractionTraceR2.rawApplyCalleeIndexOrdinal,
        YulangClosure.OriginalAuthenticInlineExtractionTraceR2.projectedInnerLambdaIndexOrdinal,
        YulangClosure.OriginalAuthenticInlineExtractionTraceR2.rawApplyCalleeOccurrenceOrdinal,
        YulangClosure.OriginalAuthenticInlineExtractionTraceR2.innerLambdaOccurrenceOrdinal,
        YulangClosure.OriginalAuthenticInlineExtractionTraceR2.rawApplyCalleeRange,
        YulangClosure.OriginalAuthenticInlineExtractionTraceR2.innerLambdaRange)] ∧
  YulangClosure.OriginalAuthenticInlineExtractionTraceR2.rawApplyCalleeIndexOrdinal ≠
      YulangClosure.OriginalAuthenticInlineExtractionTraceR2.projectedInnerLambdaIndexOrdinal ∧
    YulangClosure.OriginalAuthenticInlineExtractionTraceR2.rawApplyCalleeForm = "Group" ∧
      YulangClosure.OriginalAuthenticInlineExtractionTraceR2.projectedCalleeForm = "Lambda"
'YulangClosure.OriginalAuthenticInlineExtractionR2.group_projection_incidence' does not depend on any axioms
YulangClosure.OriginalAuthenticInlineExtractionR2.group_range_contains_projected_lambda : YulangClosure.OriginalAuthenticInlineExtractionTraceR2.rawApplyCalleeRange.fst <
    YulangClosure.OriginalAuthenticInlineExtractionTraceR2.innerLambdaRange.fst ∧
  YulangClosure.OriginalAuthenticInlineExtractionTraceR2.innerLambdaRange.snd <
    YulangClosure.OriginalAuthenticInlineExtractionTraceR2.rawApplyCalleeRange.snd
'YulangClosure.OriginalAuthenticInlineExtractionR2.group_range_contains_projected_lambda' does not depend on any axioms
YulangClosure.OriginalAuthenticInlineExtractionR2.apply_tail_range : YulangClosure.OriginalAuthenticInlineExtractionTraceR2.applySourceForm =
    "MlArgument" ∧
  YulangClosure.OriginalAuthenticInlineExtractionTraceR2.applyRange =
      YulangClosure.OriginalAuthenticInlineExtractionTraceR2.rawApplyArgumentRange ∧
    YulangClosure.OriginalAuthenticInlineExtractionTraceR2.rawApplyCalleeRange.snd <
        YulangClosure.OriginalAuthenticInlineExtractionTraceR2.applyRange.fst ∧
      YulangClosure.OriginalAuthenticInlineExtractionTraceR2.rawApplyCalleeIndexOrdinal ≠
        YulangClosure.OriginalAuthenticInlineExtractionTraceR2.rawApplyArgumentIndexOrdinal
'YulangClosure.OriginalAuthenticInlineExtractionR2.apply_tail_range' does not depend on any axioms
YulangClosure.OriginalAuthenticInlineExtractionR2.complete_direct_body_incidence : YulangClosure.OriginalAuthenticInlineExtractionTraceR2.outerBodyForm =
    "StatementBlock" ∧
  List.map
      (fun row =>
        (row.kind, row.sourceOrder, row.localSourceIndex, row.bindingOrdinal, row.occurrenceOrdinal, row.byteRange,
          row.sourcePositionOrdinal))
      YulangClosure.OriginalAuthenticInlineExtractionTraceR2.outerBodyIncidence =
    [("statement-expression", 0, some YulangClosure.OriginalAuthenticInlineExtractionTraceR2.applyIndexOrdinal, none,
        some YulangClosure.OriginalAuthenticInlineExtractionTraceR2.applyOccurrenceOrdinal,
        some YulangClosure.OriginalAuthenticInlineExtractionTraceR2.applyRange, some 39),
      ("final-expression", 1, some 2, none, some 8, some (32, 33), some 48)]
'YulangClosure.OriginalAuthenticInlineExtractionR2.complete_direct_body_incidence' does not depend on any axioms
YulangClosure.OriginalAuthenticInlineExtractionR2.exact_name_resolution_rows : List.map
      (fun row =>
        (row.label, row.sourceIndex, row.occurrenceOrdinal, row.spelling, row.resolutionKind, row.parameterOrdinal,
          row.sourcePositionOrdinal, row.byteRange))
      YulangClosure.OriginalAuthenticInlineExtractionTraceR2.nameResolutions =
    [("apply-argument", YulangClosure.OriginalAuthenticInlineExtractionTraceR2.rawApplyArgumentIndexOrdinal,
        YulangClosure.OriginalAuthenticInlineExtractionTraceR2.rawApplyArgumentOccurrenceOrdinal,
        YulangClosure.OriginalAuthenticInlineExtractionTraceR2.outerParameterSpelling, "Parameter",
        YulangClosure.OriginalAuthenticInlineExtractionTraceR2.outerParameterOrdinal, 41,
        YulangClosure.OriginalAuthenticInlineExtractionTraceR2.rawApplyArgumentRange),
      ("inner-body", YulangClosure.OriginalAuthenticInlineExtractionTraceR2.innerBodyIndexOrdinal,
        YulangClosure.OriginalAuthenticInlineExtractionTraceR2.innerBodyOccurrenceOrdinal,
        YulangClosure.OriginalAuthenticInlineExtractionTraceR2.innerParameterSpelling, "Parameter",
        YulangClosure.OriginalAuthenticInlineExtractionTraceR2.innerParameterOrdinal, 34, 25, 27),
      ("restored-sibling", 2, 8, YulangClosure.OriginalAuthenticInlineExtractionTraceR2.outerParameterSpelling,
        "Parameter", YulangClosure.OriginalAuthenticInlineExtractionTraceR2.outerParameterOrdinal, 48, 32, 33)] ∧
  YulangClosure.OriginalAuthenticInlineExtractionTraceR2.outerParameterSpelling =
      YulangClosure.OriginalAuthenticInlineExtractionTraceR2.innerParameterSpelling ∧
    YulangClosure.OriginalAuthenticInlineExtractionTraceR2.outerParameterOrdinal ≠
      YulangClosure.OriginalAuthenticInlineExtractionTraceR2.innerParameterOrdinal
'YulangClosure.OriginalAuthenticInlineExtractionR2.exact_name_resolution_rows' does not depend on any axioms
YulangClosure.OriginalAuthenticInlineExtractionR2.names_have_source_positions : ∀
  (name : YulangClosure.OriginalAuthenticInlineExtractionTraceR2.TraceNameResolution),
  name ∈ YulangClosure.OriginalAuthenticInlineExtractionTraceR2.nameResolutions →
    ∃ position,
      position ∈ YulangClosure.OriginalAuthenticInlineExtractionTraceR2.sourcePositions ∧
        position.kind = "node" ∧
          position.positionOrdinal = name.sourcePositionOrdinal ∧ position.byteRange = name.byteRange
'YulangClosure.OriginalAuthenticInlineExtractionR2.names_have_source_positions' does not depend on any axioms
YulangClosure.OriginalAuthenticInlineExtractionR2.shadow_and_restoration_snapshot : List.map
      (fun row => row.parameterOrdinal) YulangClosure.OriginalAuthenticInlineExtractionTraceR2.nameResolutions =
    [YulangClosure.OriginalAuthenticInlineExtractionTraceR2.outerParameterOrdinal,
      YulangClosure.OriginalAuthenticInlineExtractionTraceR2.innerParameterOrdinal,
      YulangClosure.OriginalAuthenticInlineExtractionTraceR2.outerParameterOrdinal] ∧
  List.map (fun row => row.sourceOrder) YulangClosure.OriginalAuthenticInlineExtractionTraceR2.outerBodyIncidence =
      [0, 1] ∧
    List.map (fun row => row.localSourceIndex)
          YulangClosure.OriginalAuthenticInlineExtractionTraceR2.outerBodyIncidence =
        [some YulangClosure.OriginalAuthenticInlineExtractionTraceR2.applyIndexOrdinal, some 2] ∧
      YulangClosure.OriginalAuthenticInlineExtractionTraceR2.applyRange.snd < 32
'YulangClosure.OriginalAuthenticInlineExtractionR2.shadow_and_restoration_snapshot' does not depend on any axioms
YulangClosure.OriginalAuthenticInlineExtractionR2.foreign_report_inventory : YulangClosure.OriginalAuthenticInlineExtractionTraceR2.foreignOwnerChecks =
  ["equal-text foreign SourceNodeKey rejected as ForeignParse",
    "foreign parameter identity rejected as ForeignHirArtifact",
    "foreign parse artifact rejected selected parameter origin as ForeignParse",
    "foreign HIR occurrence rejected by selected HIR"]
'YulangClosure.OriginalAuthenticInlineExtractionR2.foreign_report_inventory' does not depend on any axioms
```
