# INLINE-AUTHENTIC-EXTRACTION-20261027/r2 — isolated authentic trace and original allocation frontier

Status: ADMITTED by Luna at baseline `232b024e0d793714027170a388ab746ce0d2b429`.
Exact worker leases are issued only after this frozen contract is committed and
the current snapshot is synchronized. This is a fresh sprint after reviewed r1
`FAILED_INCOMPLETE`; r1 budget and receipts are not transferred or erased.

## Original goal and fixed outcome

The user goal remains the full Yulang type-inference and executor Lean proofs and
Rust implementation, including original Simple-sub A/B, soundness, effect
hygiene, principality, progress/termination, complete Call behavior,
source/native correspondence, whole-language coverage and production gates.
Every original quantifier, accepted source form, meaning and open gate remains
unchanged. This sprint advances one authentic frontend-to-original-source
instance and its exact remaining allocation obligation; a finite instance does
not close universal refinement or any full parent gate.

Obtain an executed trace from one authentic parse/HIR/LocalSource/Shadow path,
then validate that trace in Lean and apply the reviewed `OriginalIdentityEntryOrigin`
equations only where the actual trace supplies their premises. The trace must
retain:

- the exact inline Lambda and binder token range, matching the corresponding
  `LocalSourceParameter.range`;
- the parameter ID, body occurrence and actual resolved Name, with parse/HIR
  ownership authenticated before serialization;
- the actual enclosing Apply, its raw callee and argument, and every explicit
  `Group -> inner` projection edge (raw identity is not projected identity);
- the enclosing body constructor and byte range plus its complete ordered child
  incidence, including the nested same-spelling Lambda and restored sibling;
- sufficient owner/key/index data to reject a foreign parse or HIR artifact.

The first outcome should either establish one reviewed source→HIR→trace→Lean
instance and its exact application, or identify the first unavailable equation
at the real owner. Do not replace branded source/HIR identity with an invented
Nat allocation convention. The original mapping for `Site`, `Name`, declaration,
root `Context` and ambient event telescope stays explicit and OPEN until proved.

## Frozen authority and dependencies

- Branch `yulang3`, baseline `232b024e0d793714027170a388ab746ce0d2b429`.
- r1 contract SHA-256 `015c8c276dde26747b82cea6bf1ff14784a19ced91a8234487cff93c46b09254`;
  r1 reviewed outcome SHA-256 `a035d1d9e44aaa89d044b11bf252c765bc3671a90d7bffaa0ee964cbe47919c8`;
  r1 review SHA-256 `2a861eb9d91ad7f800ed38ac826e290e09a71798528dab25252163c9a6d74f13`;
  source/proof handoffs `a6b09733222243b779cfb8ed4c2e7ba4da3aa0fc3c765c0bc225ef7852463d30`
  and `001de7deee35769a92f7beacb12e253443fd74993aa04f327cb8979a996b880f`.
- Revalidate the complete original r1 source and Lean input pin set verbatim
  before work. The independent r1 reviewer verified all 28 pins. Relevant direct
  owner hashes at this baseline remain: `local_source.rs`
  `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1`,
  `shadow.rs` `b964bab6dcdb7ebeca9f964c134ac8fb041c928c20ce0a895fea6b6af0fbb93e`,
  `source_identity.rs` `4bd5fa4066a1fd445a9757374c44d602decd1d791a394cd81c6066efa063fb23`,
  `module.rs` `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`,
  and `full_parse.rs`
  `dd92603f8f5549b8b3f6e45ab6cb39b6598480b7f1cda7897e27b5113107db93`.
- Existing root and crate manifests/lock hashes: `Cargo.toml`
  `a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a`,
  `Cargo.lock` `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`,
  `crates/yu-hir/Cargo.toml`
  `a97f52fc6b9e577f23be4160ecdda9693bec8fe48c626d0e9b7c0e3b0c6fe8d1`,
  `crates/yu-syntax/Cargo.toml`
  `567b705fabf7558250dbfa59e833d4ff04cb3041db8ed742311865d8cf3081d3`.
  `yu-hir` normal dependencies only on `yu-syntax`; extractor package must use
  its `shadow` feature and must resolve no `yu-solver` edge.
- Lean origin pins: `OriginalIdentityRealization.lean`
  `30b0676f4af22dc7da2c75596a338db57a24b17662a4057801cfdff7ab4a2f42`,
  `OriginalIdentityEntryOrigin.lean`
  `9df7fccfe03becec491665a28a7fb65760e1245d76e68330fc9626da5533163e`,
  `lakefile.toml` `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`,
  and `lean-toolchain`
  `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`.
  Use pinned Lean 4.35.0 and the existing project import cone; no root import,
  toolchain or project dependency changes.

## Implementation lane — registered `implementer`, Luna/high

Exact leased outputs:

- `tools/inline-authentic-extraction/Cargo.toml`
- `tools/inline-authentic-extraction/Cargo.lock`
- `tools/inline-authentic-extraction/src/main.rs`
- `notes/theory/lean/YulangClosure/OriginalAuthenticInlineExtractionTraceR2.lean`
- `tasks/agent-loop/inbox/inline-authentic-extraction-20261027-r2-source.md`
- scratch root `/tmp/yulang-inline-authentic-extraction-20261027-r2/impl`

The isolated package must declare its own `[workspace]` and depend only on path
crates `yu-hir` with `features = ["shadow"]` and `yu-syntax`, plus the minimal
direct dependencies required by the extractor. First stage only: create the
manifest and offline lock, then run a metadata-only/offline graph query (one
process, <=30 seconds, 1 CPU/1 GiB, no compilation). Freeze the complete resolved
graph and manifest/lock hashes to Luna. **Do not compile or run the extractor
until Luna returns a versioned contract revision pinning those exact hashes and
confirms `yu-solver` is unreachable and external package versions/checksums match
the existing lock.**

After that acknowledgement, implement the extractor against the real
`ParsedFile`, HIR, `LocalSourceIndex`, `ShadowArtifact`, exact binder origins,
published occurrences and resolution owners. Preserve raw Apply callee and
projection edges separately; preserve the full ordered body graph. Reject
foreign parse/HIR inputs and range mismatches before serialization. Generate a
deterministic Lean trace and record actual stdout, commands, exit/duration,
source/trace hashes, exclusions and stop status in the one handoff.

Budget across both stages: at most 3 Cargo invocations total (one metadata-only
call <=30s and at most two `--offline --locked` compile/run calls <=120s each),
1 CPU/1 GiB, one heavy process at a time. No tests added or run, no installs,
no root workspace edits, no compiler/HIR/parser/runtime/API/semantic/expected
output changes. The candidate is a provisional evidence tool only.

## Proof lane — registered `lean_prover`

Exact leased outputs:

- `notes/theory/lean/YulangClosure/OriginalAuthenticInlineExtractionR2.lean`
- `notes/theory/lean/AuditOriginalAuthenticInlineExtractionR2.lean`
- `tasks/agent-loop/inbox/inline-authentic-extraction-20261027-r2.md`
- scratch root `/tmp/yulang-inline-authentic-extraction-20261027-r2/proof`

Before trace arrival, inspect the original Identity constructors, reviewed entry-
origin equations and actual HIR/source owners for any existing allocation
equation connecting `SourceNodeKey`, `HirParameterId`, LocalSource indices and
resolution to original Sites, Names, declaration, root Context and ambient
events. Report the exact first missing owner/equation. Do not run Lean against a
hand-authored replacement trace or treat extracted Nat ordinals as original
coordinates. Once the exact executed trace is frozen, construct its Lean
representation and prove the finite constructor/range/order/resolution facts it
actually supports; apply reviewed entry-origin equations with all allocation
premises explicit. Keep universal refinement and every full parent gate OPEN.

Use Lean 4.35.0, one checker owner, at most 6 checker calls and 360 aggregate
seconds (`-j1 -M1024`). Hash the full imported source cone and report every
originating theorem type with complete transitive axiom audits. No installs,
root imports or tests.

## Primary, review, resources and stop conditions

The implementation schema/trace and lock graph are immutable review inputs.
After both authors stop, a fresh non-author `compiler_referee` reviews source
ownership, exact binder, Group projection, full ordered incidence, foreign
owner rejection, commands/raw receipts, trace serialization, Lean type/axiom
audit and the exact application to the original parent. It also checks that the
unresolved original allocator is neither hidden nor asserted absent universally.
Luna owns the review handoff, adjudication, outcome, `current.json`, Git and all
integration.

Fresh r2 budget: 3600 active seconds total — proof 1200, implementation 900,
primary 600, review 720, dispatch 180; Astra 0. One verifier process at a time.
Preserve all r1 spend and failures. Stop for pin/dependency drift, any reachable
`yu-solver`, cache/resource failure, foreign-owner acceptance, incorrect token,
Group edge, ordered incidence or resolution, a lease conflict, or a source
counterexample. No automatic budget renewal. Consult at a material obstruction,
dependency/authority/lease change, frozen review seam or END.

Read-only dispatch: `/root/r2_start_selector` recommended this isolated trace
route and the staged graph-pin seam. It granted no lease/resource; effective
session/model metadata was unavailable. All work remains inside the original
full user goal. No parent proof, source/native, receipt/admission,
whole-language or production gate closes by this packet.
