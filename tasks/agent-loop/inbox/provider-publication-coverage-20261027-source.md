# PROVIDER-PUBLICATION-COVERAGE-20261027/r1 — source handoff r1

Contract SHA-256: `e3996c31afb32756468068b25b587bcd7499cc0a4d628383b54780c490f8753d`.
Baseline: `b54ae2df5dd0113779ee95d380cfcbdbd2fb14e0`; branch `yulang3`.
Assignment: `/root/provider_publication_impl`; requested `gpt-6-luna` / `high`.
Observed model/effort: `UNKNOWN` / `UNKNOWN`; this runtime exposed no effective
model metadata. No claim that Luna actually executed this work.

**Outcome class: source-native evidence, provenance only.** The unchanged
`pub id x = x\n` fixture parsed and lowered through public HIR APIs. Its local
source carrier retained the named formal, lambda/body indices and parameter
resolution; exact parse ownership was checked. Foreign parse keys and foreign
HIR occurrences were rejected before trace emission. Explicit `identity` and
implicit prelude `id` both resolved to the exact same provider
`SourceExportId`. This supplies the requested source-to-HIR/export path; it
does not execute the initializer or establish original logical event data,
publication coverage, a judgment, or any parent gate.

## Exact writes and frozen artifacts

- Adapter: `tools/inline-authentic-extraction/src/bin/original_provider_reify.rs`
  - Frozen starting hash: `5ed03633e8a37775847d7c28fc08d2d7acc98965299e0dbe27568b266fd2b8ed`.
  - Final SHA-256: `39be34a6c0ae2eea673af07dd427e9316f72290687cc937ba2faa13615067729`.
- Generated trace: `notes/theory/lean/YulangClosure/OriginalProviderPublicationCoverageTrace.lean`
  - SHA-256: `9e2578c3e96f95d335263d1c0ed874af36ed411676fbb4977676314a28af56e1`.
- This handoff: `tasks/agent-loop/inbox/provider-publication-coverage-20261027-source.md`.

Only the leased adapter, generated trace, and this handoff were written. No
production crate, manifest, lockfile, test, diagnostic, source domain, semantic
rule, or Git state was changed. The original provider fixture bytes and hash
remain exactly `pub id x = x\n` and
`9b830a0650483a3387ced1724463b5fb18434366fb5a082f8cf7597ca8e7519e`.

## Prior evidence and owner correspondence

The starting adapter hash matched the contract. I read both complete compiler
logs from the prior source assignment. Attempt 1 exposed the private-module
path, non-`Error` conversions, borrowed parameter comparison, and source-key
reference mismatch. Attempt 2 repaired those, then isolated two ambiguous
`SourceText.as_ref()` slices and a borrow of the export index held across the
import resolver call. The frozen starting adapter already included the first
set of repairs. I fixed the remaining adapter-owned errors with direct `&str`
range indexing and an owned provider export source key. No compiler owner
module was edited.

I inspected the previous `original_caller_reify.rs` and its independent review.
That adapter required `ShadowArtifact::from_parsed` for the provider; the
reviewed attempt failed there before resolver joins or foreign-owner checks.
That candidate is rejected as runtime evidence. This adapter follows the
public `lower_module` / `LocalSource` path and does not restore a Simple-sub
bypass or depend on `ShadowArtifact`.

Relevant unchanged owner pins:

| Owner/evidence | SHA-256 |
| --- | --- |
| `crates/yu-hir/src/module.rs` | `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `crates/yu-hir/src/module/source_exports.rs` | `03727fd3918738a48afde7f7a875de60b63b43ac2cc620896a4ed73d8b0a9179` |
| `crates/yu-hir/src/source_identity.rs` | `4bd5fa4066a1fd445a9757374c44d602decd1d791a394cd81c6066efa063fb23` |
| `crates/yu-syntax/src/full_parse.rs` | `dd92603f8f5549b8b3f6e45ab6cb39b6598480b7f1cda7897e27b5113107db93` |
| `crates/yu-syntax/src/lib.rs` | `770a4af4a5832b3210050b4fc5513545569b0ca4718597f67434a714f76f301d` |
| `tools/inline-authentic-extraction/Cargo.toml` | `21c64b4a22318a1ae89c346357161812a6ac313b6f0c4999853272cf73e2832b` |
| `tools/inline-authentic-extraction/Cargo.lock` | `2ee467b8f6416aa7dda36f96e3401a0b0ae24a739ff7c6a2efccc1323777ee91` |
| `tools/inline-authentic-extraction/src/bin/original_caller_reify.rs` | `4652e48fe3305d34c9d271f3a711cee97785a1d167ca19d4a4b01c147e775620` |
| `tasks/agent-loop/inbox/source-owner-caller-realization-20261027-review.md` | `5ad88936a23504a429d9dbaeeced0325a37849fe7628786e6ebfeaed97a1cbfc` |
| `tasks/agent-loop/inbox/import-publication-construction-20261027-source.md` | `4ea9245a78c01bca1bfe93c5e2dbe420b0c48d2157057387cac4f550cc474204` |
| `OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `OriginalSourceEnvironment.lean` | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` |
| `OriginalSourceInterpretation.lean` | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |

The source-owner chain evidenced by the successful run is:

1. `parse_file` constructs the provider `ParsedFile`; its `owns_source_key`
   checks parse-identity ownership.
2. Public `lower_module` enables ordinary source carriers. The exact public
   `id` HIR binding owns a definition source key and a `LocalSource` whose one
   named group is owned by that definition. Its Lambda points to a retained
   `x` formal and body; the body is a retained `x` name resolved to that exact
   parameter. The run checked the ranges and parse-owned CST keys against the
   unchanged input.
3. `index_source_exports` supplied the public `std::core::id` declaration.
   `SemanticImports::with_source_imports` resolved the explicit alias and
   unshadowed implicit prelude name. Both full `SourceExportId` values
   (module, name, source key, range and syntax kind) equaled the indexed
   provider export.
4. The explicit foreign-parse key and foreign-HIR occurrence checks ran before
   the single trace write. Both foreign identities were rejected; the chosen
   provider HIR owned its own checked body occurrence.

The existing owner test in `crates/yu-hir/src/module.rs:4817–4838` also asserts
the alias/prelude equality. It was inspected, not run. This assignment ran the
adapter executable only; tests: 0.

## First cross-system owner gap

The Rust path above owns CST/HIR provenance and exact export identity only. No
Rust owner constructs a corresponding `OriginalSource.Source`, its logical
`Site`/`Name`/`Declaration` coordinates, incoming `Context`, or independent
local source admission. The first missing bridge is therefore **provider
Source/Context introduction**. The actual proof-side owners remain distinct:

- `OriginalSource.Source` constructors are declared in
  `OriginalSourceSyntax.lean`; `Context` is consumed by `sourceRules` in
  `OriginalSourceGeneration.lean`. The inspected `formalContext` helper in
  `OriginalSourceInterpretation.lean` constructs a Lean context from already
  chosen logical values; it does not derive those values from this HIR trace.
- Generation records initializer entry state in `Environment.enterInitializer`
  and owns `Environment.extend`;
  `prefixAtShared` and `publicationCandidate` inspect actual Shared and
  Return-rebind frames. `publicationValid` requires the candidate's exact
  `PublicationRecord` to occur in `Environment.publications`. `publish` adds
  names from candidates; it does not add or prove the fixed map equation.
- `Payload.shared`, `Payload.runtime`, and `Admissions.shared` /
  `Admissions.returnRebind` are proof-side data/admission owners in
  `OriginalSourceEnvironment.lean`. No such payload, admission, event path,
  replay, captures, initializer execution or record was produced by the Rust
  owner path.

Thus the trace makes no original Source coordinates, Context, Return/Shared
data, replay, finite support, or publication equation. `PSR-SOURCE-OWNER-1`,
`PSR-EVENT-MAP-1`, and `PSR-EXPOSURE-TRANSPORT-1` remain open. The proof result
must independently apply to `PSR-EVENT-MAP-1`; this trace cannot show its
assumptions inapplicable and cannot establish the provider judgment.

## Execution receipts

Both runs used cwd `/home/momota1029/rust/yulang` and this exact Cargo command
and argument (the second attempt was additionally CPU-affined with
`taskset -c 0`):

```sh
cargo run --offline --locked --manifest-path tools/inline-authentic-extraction/Cargo.toml --bin original_provider_reify -- /home/momota1029/rust/yulang/notes/theory/lean/YulangClosure/OriginalProviderPublicationCoverageTrace.lean
```

They used isolated
`CARGO_TARGET_DIR=/tmp/yulang-provider-publication-coverage-20261027/source/target`,
`CARGO_BUILD_JOBS=1`, 1,048,576 KiB address-space limit, 180-second CPU/wall
limits, and the new grant of at most two runs. Logs and wrapper time reports:

| Run | Result | Wall / max RSS | Notes |
| --- | --- | --- | --- |
| 1/2 | exit 1 | 22.83s / 526,552 KiB | Compiled adapter; stopped at stale output-path guard before fixture parsing. `CARGO_BUILD_JOBS=1`; CPU affinity was not applied to Cargo on this run. |
| 2/2 | exit 0 | 0.40s / 144,636 KiB | `taskset -c 0`; parsed/lowered provider; foreign parse/HIR rejected; both joins passed; emitted trace. |

The first failure was adapter-owned: `OUTPUT_RELATIVE` and `LEAN_MODULE` still
named the prior sprint trace target. Both constants were corrected within the
leased adapter; the second run is the only run that reached provider behavior.
Full receipts are under the leased scratch root:

| File | SHA-256 |
| --- | --- |
| `attempt1.stdout` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `attempt1.stderr` | `fa17852d0ecb3c3f5c09a8467d9d2c679f8f6bbb3da4326a98280e9f0fff82b8` |
| `attempt1.time` | `d463d1e60059f95cb4c19614d19a91a9f52b594f4f1ed2815d08df3e8755384d` |
| `attempt1.status` | `4355a46b19d348dc2f57c046f8ef63d4538ebb936000f3c9ee954a27460dd865` |
| `attempt2.stdout` | `47fac61ed367741e28dc4fbf3ed2464f346e03b4f97a3e914733e7521982cb6f` |
| `attempt2.stderr` | `a46dbcd864945ebdf9c678e34ebecfdc07914ac058747d5f016b95082e0745f2` |
| `attempt2.time` | `0ab5d8c9e3e2856caefbe46931810961366a3172bca1bf47babd0f5d5b43906c` |
| `attempt2.status` | `9a271f2a916b0b6ee6cecb2426f0b3206ef074578be55d9bc94f6f3fe3ab86aa` |

The successful output identifies provider `std::core::id#0`, declaration byte
range `(0,12)`, formal `(7,8)`, body `(11,12)`, LocalSource lambda index `0`,
body index `1`, and HIR occurrence ordinal `3`. Parser diagnostics are empty.
The explicit alias and implicit prelude id both compare equal to the full
provider export identity.

Lean verification: 0 calls by this assignment. The proof worker completed its
8-call envelope separately; this trace was not typechecked here. No Cargo tests
or other tests were run. Independent review and Luna adjudication remain
pending. All parent mathematical, source/native and production gates remain
OPEN.

## Stop, scratch, and next step

All two Cargo attempts are spent. No further Cargo, Lean, Lake, tests,
formatters or Git operations are authorized in this assignment. All writes to
the three leased paths have stopped; no child or background process remains.
The next related in-envelope step is fresh read-only review of this frozen
trace against the adapter and exact owner definitions, followed by Luna's
application to the open source/event-map premises.

Known disposable scratch is only
`/tmp/yulang-provider-publication-coverage-20261027/source/`: isolated Cargo
target plus both stdout/stderr/time/status receipt sets. No repository-local
build output or other new path is known. The prior sprint scratch at
`/tmp/yulang-provider-source-solution-20261027/source/` remains prior-assignment
evidence and was not modified or cleaned.
