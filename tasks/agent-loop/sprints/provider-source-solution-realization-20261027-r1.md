# PROVIDER-SOURCE-SOLUTION-REALIZATION-20261027/r1

Status: ADMITTED by Luna after start-dispatcher delta, pin check and live-roster
reconciliation, 2026-10-27.
Parent: full Yulang inference/executor correctness, still OPEN.
No compiler semantics or production implementation changes are authorized.

## Fixed constructive outcome

Use the already audited provider `pub id x = x`, with the consumer exposures
`identity` (explicit `std::core::id as identity`) and `id` (implicit prelude).
Construct a provider-specific, source-owned chain:

```text
authenticated declaration/formal/body
  → original provider Source and genuine incoming Context relation
  → actual initializer / Return-rebind / Shared evidence
  → independently justified fixed publication-map equation
  → complete record transported to both consumer exposures
```

The packet exists to construct this witness; do not require the complete chain
as a prerequisite to starting. Establish each equation as soon as its actual
inputs are available, and identify the first constructor/consumer that cannot
be connected. The implementation lane may build a research-only adapter using
existing owners. The proof lane must attempt provider interpretation and
finite publication-graph completion from actual event/source data, proving
lookup consistency and preservation of the provider judgment. Merely replacing
the map so `publicationValid` becomes true is not admissible.

Do not infer `Mono`, `Published` or `Family` from visibility, route, spelling,
or `SourceExportId`. Do not equate Rust exposure aliasing with SRC-J
`Client.alias`. No fabricated empty Context, successful Kernel, arbitrary
frames, omitted captures, or assumed `publicationValid`. A conflicting record
at the same publication identity is a falsifier. Complete ordered import-root
elaboration remains separate.

## Parent claim and authority

Keep the unchanged parent at
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md:16–44`, with the
birth-level correction at `notes/theory/2026-10-24-birth-level-scc-intrusion.md:2–6`
and the Authoritative inference algorithm in
`notes/design/2026-10-11-yulang-inference-top-level-principles.md`. It retains
all supported source forms, source typing/principal coverage, soundness,
progress/termination, complete Call, Effect hygiene and shared witnesses.
This finite-provider packet may discharge only its exact subclaims; it cannot
narrow or close the parent.

Apply the adopted Source-Generalize design §2 and companion construction §§3–5.
Source semantics stay unchanged. A real contradiction returns for independent
review and user authority; this packet does not select a new meaning.

## Baseline and direct dependency pins

Baseline: `754c959462d415ea523cecab894e61d99f7fdff3`, branch `yulang3`.
Luna revalidates all rows before admission; each worker revalidates the rows it
relies on. Baseline/source identity is the primary's Git observation; child
Git is prohibited.

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| `notes/theory/2026-10-24-birth-level-scc-intrusion.md` | `67c2a44b7a4009a96424dc329ed4385fffdbc6d6661bf4155408cfbd62de3bfa` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` |
| `notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean` | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| `notes/theory/lean/YulangClosure/OriginalSourceOwnerReification.lean` | `95d9749ce93ecfc82d6423ba193a261f2725178a7e62cea469b57ae316af3d7e` |
| `notes/theory/lean/YulangClosure/OriginalSourceOwnerReificationInstance.lean` | `3aab685323e00b69cb9c21d847582e442590e0ff5e810fab50662b7d9127f887` |
| `notes/theory/lean/YulangClosure/OriginalSourceOwnerReificationTrace.lean` | `b9a15df005c730db27fc385c58ca07b433f1095f017e0969155106da7478fb0a` |
| `notes/theory/lean/YulangClosure/OriginalFormalAdmission.lean` | `77230ab7984ee544db16fe4d9663b73f98b9afa9c5d2610fad59c26753d5ac7c` |
| `notes/theory/lean/YulangClosure/OriginalEffectHygiene.lean` | `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f` |
| `notes/theory/lean/YulangClosure/NativeContextReadback.lean` | `321d087c8d2df5099f67beb75e4316d44114806bbfae2aa64ebda22a34bd83f2` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| `notes/theory/lean/README.md` | `8d27e0b90fc04eb8a0a30606a857e564e5269e8e33e72fddbf1190cb6a7072e3` |
| `crates/yu-hir/src/module/source_exports.rs` | `03727fd3918738a48afde7f7a875de60b63b43ac2cc620896a4ed73d8b0a9179` |
| `crates/yu-hir/src/module.rs` | `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `crates/yu-hir/src/shadow.rs` | `b964bab6dcdb7ebeca9f964c134ac8fb041c928c20ce0a895fea6b6af0fbb93e` |
| `crates/yu-hir/src/source_identity.rs` | `4bd5fa4066a1fd445a9757374c44d602decd1d791a394cd81c6066efa063fb23` |
| `crates/yu-syntax/src/full_parse.rs` | `dd92603f8f5549b8b3f6e45ab6cb39b6598480b7f1cda7897e27b5113107db93` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `tools/inline-authentic-extraction/Cargo.toml` | `21c64b4a22318a1ae89c346357161812a6ac313b6f0c4999853272cf73e2832b` |
| `tools/inline-authentic-extraction/Cargo.lock` | `2ee467b8f6416aa7dda36f96e3401a0b0ae24a739ff7c6a2efccc1323777ee91` |
| `tools/inline-authentic-extraction/src/bin/original_caller_reify.rs` | `4652e48fe3305d34c9d271f3a711cee97785a1d167ca19d4a4b01c147e775620` |
| `tasks/agent-loop/sprints/import-publication-construction-20261027-r1.md` | `f8f8e5293bbf79490e2762d53345fc87f148192b89cedc06c6e0930083c30574` |
| `tasks/agent-loop/inbox/import-publication-construction-20261027-source.md` | `4ea9245a78c01bca1bfe93c5e2dbe420b0c48d2157057387cac4f550cc474204` |
| `tasks/agent-loop/inbox/import-publication-construction-20261027-proof.md` | `d90465d045fece0d696077b8ea04312086c7c5d0e353ded4e53eb824d86aa08e` |
| `tasks/agent-loop/inbox/import-publication-construction-20261027-review.md` | `4a84c2fbec9511c0eb4a35bbd452ea7da5d21873860fde53706f8eeecc00906e` |
| `tasks/agent-loop/sprints/import-publication-construction-20261027-r1-outcome.md` | `fbe39e2b3cb5a048b3215bd8fadd4844860e1d63cf78f7aed9c3a66b1efe1ea3` |
| `notes/design/2026-10-27-import-publication-construction.md` | `bf04c7f2eecd80c08cdfbe2820b2b533308c04825897480243122058ed2f952e` |

These pins cover the direct governing and implementation/proof dependencies.
Any new direct source owner must be recorded with its hash before relying on
it. Existing language schemas, source definitions, Cargo manifests/locks and
dependencies are immutable in this packet. The source lane owns one new,
research-only, acyclic data interface: the generated
`OriginalProviderSourceSolutionTrace.lean` defines the adapter trace schema and
data; the proof module imports it. No generated trace imports the proof. This
interface does not become an adopted language schema or production certificate.

## Start-dispatcher delta applied

The dispatcher accepted the adapter-plus-proof route and required five
clarifications, now reflected here: (1) source owns the standalone generated
trace schema, which proof imports; (2) the adapter records exact cwd, absolute
output path, source hash and foreign-owner rejection before emission; (3) one
verification process runs at a time, with the final Lean call reserved for
complete type/axiom reporting; (4) all prior inputs have exact path/hash pins,
including `full_parse.rs` and `source_identity.rs`; and (5) the HIR trace is
provenance only, not semantic execution or Return/Shared evidence. The finite
publication graph construction must preserve existing records and prove
same-identity consistency in the same graph as the provider judgment.

## Leases and lanes

**Source adapter — registered `implementer` (Luna/high)**

- Write only `tools/inline-authentic-extraction/src/bin/original_provider_reify.rs`,
  `notes/theory/lean/YulangClosure/OriginalProviderSourceSolutionTrace.lean`,
  and `tasks/agent-loop/inbox/provider-source-solution-20261027-source.md`.
- Scratch only under `/tmp/yulang-provider-source-solution-20261027/source/`.
- Fixed source fixture is the exact UTF-8 byte sequence `pub id x = x\n`,
  SHA-256 `9b830a0650483a3387ced1724463b5fb18434366fb5a082f8cf7597ca8e7519e`.
- Use actual HIR/CST/source-owner APIs to retain the provider declaration,
  formal, body occurrence and consumer export identity. Replace the prior
  ShadowArtifact-dependent approach if its exact-provider precondition fails;
  do not broaden the source fixture to hide that failure.
- Emit only data owned by those constructors. Trace the attempted original
  Source/Context/environment/fixed-map relation and its first missing owner.
  No guessed Context, Source coordinate, Kernel proof or `PublicationRecord`.
- Label the emitted HIR/CST trace as provenance only: this adapter does not run
  the semantic initializer or supply logical Return/Shared payloads. Do not
  choose degenerate Sorts or kernel meanings to make proof data line up.
- Invoke with the exact absolute leased output path; record actual cwd, fixture
  bytes/hash, command/environment and complete stdout/stderr. Perform the
  foreign-parse and foreign-HIR ownership rejection checks before emission.
  If `ShadowArtifact` admission fails, preserve the exact diagnostics and stop
  that route; do not change the provider fixture or parser admission here.
- At most two `cargo run --offline --locked` attempts (including build and
  execution), one Cargo process at a time, 1 CPU / 1 GiB / 180 seconds per
  process, with `CARGO_TARGET_DIR` isolated under the leased scratch root.
  No tests, production crate changes, manifest/lock edits, dependencies,
  formatter or Git. Preserve command/stdout/stderr/resource receipts.

**Constructive proof — registered `lean_prover`**

- Write only `notes/theory/lean/YulangClosure/OriginalProviderSourceSolution.lean`,
  `notes/theory/lean/AuditOriginalProviderSourceSolution.lean`, and
  `tasks/agent-loop/inbox/provider-source-solution-20261027-proof.md`.
- Scratch only under `/tmp/yulang-provider-source-solution-20261027/proof/`.
- Construct the provider-specific source/solution relation under the adopted
  rules. Attempt a finite publication-graph completion from actual event and
  source data; prove consistency at the identity and preserve the provider
  judgment in the same graph before transporting the complete record to both
  exposures. Reuse existing replay/alias results only after their premises are
  derived. Do not prove only a generic map-overwrite lemma.
- The source trace is not an assumption. Do not read it until the source lane
  freezes the exact bytes and Luna acknowledges its hash. The proof lane may
  advance on pinned source definitions while waiting, then incorporate the
  trace under the same lease. Source owns the trace; proof owns all theorem and
  audit modules. No simultaneous Lean build while source is writing the trace.
- The finite graph argument must preserve all already reachable records and
  prove same-identity consistency, as well as retaining captures, entry and
  completed states and Shared evidence. A sequential insertion into a map
  whose provider judgment is already assumed does not close the central goal.
- At most 8 Lean/Lake/checker calls and 600 seconds of Lean execution total;
  each process 1 CPU / 1 GiB / 180 seconds; one proof owner owns the project
  cache. Run the pinned project/checker and report full theorem types and
  per-theorem axiom audits. No `sorry`, project axiom, assumed successful
  Kernel, default/empty Context or external package.

**Review — fresh non-author `compiler_referee`**

- Luna owns `tasks/agent-loop/inbox/provider-source-solution-20261027-review.md`.
- Start after both producer handoffs and their output paths are frozen.
- Read/hash commands are permitted. No writes, Git, Cargo, Lean/Lake, tests or
  formatters. Review actual provenance, context and fixed-map construction,
  trace-to-theorem correspondence, complete publication tuple, consumer
  exposure transport and the original parent boundary.

**Luna/primary** owns this contract, `current.json`, the outcome
`tasks/agent-loop/sprints/provider-source-solution-realization-20261027-r1-outcome.md`,
design note `notes/design/2026-10-27-provider-source-solution-realization.md`,
review, adjudication, resource synchronization, staging and Git.

## Envelope and stop conditions

Fresh active budget: **4200 seconds** — source 1200, proof 1800, Luna 500,
review 600, dispatcher 100; Astra 0. At most two producers active together,
then one reviewer; maximum six active/reserved/unknown assignments in the
sprint. At most one verification process across both lanes at any moment:
source Cargo build/run first, then proof Lean/checker after the source trace is
frozen. Reserve the final Lean call for all delivered theorem types and complete
axiom audits. One Cargo target directory and one Lean cache owner; tests 0.

Stop the affected lane on pin drift, overlapping/quarantined lease, source
artifact mismatch, conflict at a publication identity, any need to choose new
semantics, fabricated kernel/frame/context, or the resource bound. Missing
source/Context data is the packet's target: isolate the first exact owner and
keep advancing independent proof/source construction. If the fixed map can be
constructed but the provider judgment does not follow in it, preserve that
concrete counterexample for review; do not patch by weakening the source rule.

No production certificate creation, compiler behavior change, import-root
elaboration claim, or parent-gate closure is authorized. Luna recorded admission
after the selector delta, 38 direct-pin checks, live-roster reconciliation,
exact disjoint leases and a successful current-state capacity check.
