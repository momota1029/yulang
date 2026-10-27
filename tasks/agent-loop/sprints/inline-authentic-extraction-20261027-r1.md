# INLINE-AUTHENTIC-EXTRACTION-20261027/r1 — authentic inline source trace

Status: **CANDIDATE** until Luna verifies the pins, admits the contract in
`current.json`, and issues the disjoint leases below.

Branch / baseline: `yulang3` / `7a8423743c3f3b7bed9860a2def5f4c23e3e943b`.
Authority: the unchanged user goal of completing the original Yulang inference
and executor proofs and Rust implementation, including soundness, effect
hygiene, principality and termination. This packet advances one source-owner
bridge only; it does not narrow the source domain or close any parent gate.

## Fixed outcome

Extract one finite trace from the same immutable `ParsedFile`, HIR artifact and
`LocalSource` owner. It must contain a real inline Lambda, its exact binder
token, parameter ID, body occurrence and resolved Name; an enclosing real
Apply with its actual callee and argument; and a nested same-spelling Lambda
whose later sibling resolves again to the outer parameter. Authenticate every
source/HIR join before emitting data. Preserve actual owner/key/occurrence
identities in the handoff and generated Lean trace.

The proof lane consumes the frozen trace, checks its byte ranges and internal
constructor relationships, derives the corresponding original `Identity` and
applies the reviewed entry-origin equations where their premises follow. Keep
the mapping from Rust-branded identities and runtime labels to original Nat
`Site`/`Name` values explicit. If no existing source allocator establishes
that mapping, expose it as the first OPEN premise; do not silently adopt a new
numeric convention. Finite trace validation is an instance, not a universal
frontend-refinement theorem.

Success is either (1) a reviewed authentic source→HIR→trace→Lean instance with
an exact, honest parent application, or (2) the first unavailable owner law or
authentic counterexample that determines the next proof/source route.

## Hard boundaries

- Preserve original A/B quantifiers, the entire accepted source domain,
  accepted inference behavior, lexical/type/event scopes, complete Call,
  effect hygiene and shared witnesses. No proof-parent or production gate is
  closed by one finite trace.
- Change no compiler, HIR, parser, runtime, public API, semantic behavior,
  expected output, test source, Cargo manifest/lockfile, Lean root import,
  toolchain or governing rule.
- The Rust executable is a provisional research extractor under
  `tools/inference-playground/src/bin/`; it is not a compiler feature and must
  reject foreign HIR/parse ownership, mismatched binder ranges and unrelated
  Apply/callee/argument joins before serialization.
- Do not treat `parameter_source_position`'s `MissingSource` for an inline
  parameter as a defect. Use `parameter_source_origin` and its exact token.
- Keep source receipt/readout/admission, Callee/provider/Closure selection,
  source/native simulation, original A/B, whole-language correspondence and
  production readiness OPEN.

## Proof lane — registered `lean_prover`

Apply `.agents/skills/yulang-lean-proofs/SKILL.md`. Read the original Identity
constructors and reviewed `OriginalIdentityEntryOrigin` results pinned below.
Consume the generated `OriginalAuthenticInlineExtractionTrace.lean` only after
its producer freezes it. Prove exactly what its concrete source and owner
fields support: span/source agreement, extracted Lambda/formal/body/Name
relationships, actual Apply incidence and nested-shadow/restored-sibling
resolution. Construct a corresponding original source instance using explicit
Site/Name allocation premises and immediately specialize reusable entry-origin
equations. Do not use the previous arbitrary `Expansion.context`/`prior` or
raw candidate tags as if they were extracted. If the real Context/name/site
allocator is not connected to the original model, name that exact missing
equation and leave it OPEN.

Leases:

- `notes/theory/lean/YulangClosure/OriginalAuthenticInlineExtraction.lean`
- `notes/theory/lean/AuditOriginalAuthenticInlineExtraction.lean`
- `tasks/agent-loop/inbox/inline-authentic-extraction-20261027.md`
- scratch only: `/tmp/yulang-inline-authentic-extraction-20261027/proof`

Budget: at most six checker calls and 360 aggregate checker seconds; Lean
4.35.0, `-j1 -M1024`, one verification owner. Hash the complete imported
project-source cone, print every originating theorem type and full transitive
axiom audit. No installs or root import edits.

## Implementation lane — registered `implementer`, Luna/high

Build a provisional extractor only at
`tools/inference-playground/src/bin/inline_authentic_extraction.rs`; Cargo's
automatic `src/bin` discovery is expected, so no manifest edit is authorized.
Use the pinned parser, `lower_module_with_local_source`, `ShadowArtifact`,
`parameter_source_origin`, published occurrences and actual `LocalSource`
indices. Authenticate the same-parse/same-HIR owner before deriving or
serializing any relation. Emit a deterministic standalone Lean data module at
`notes/theory/lean/YulangClosure/OriginalAuthenticInlineExtractionTrace.lean`
and document exact owner values, source bytes, execution command and limits in
the handoff.

The input fixture must exercise an outer `x`, an inner inline `x` used as the
callee of an Apply with the outer `x` as its real argument, and a later sibling
`x` after inner-lambda exit. The extractor must identify the inner body Name as
the inner parameter and the later sibling Name as the restored outer parameter.
Also attempt owner-crossing rejection using equal source text from a distinct
parse/HIR artifact. No compiler edits or test-suite additions/runs are leased.

Leases:

- `tools/inference-playground/src/bin/inline_authentic_extraction.rs`
- `notes/theory/lean/YulangClosure/OriginalAuthenticInlineExtractionTrace.lean`
- `tasks/agent-loop/inbox/inline-authentic-extraction-20261027-source.md`
- scratch only: `/tmp/yulang-inline-authentic-extraction-20261027/impl`

At most two bounded offline Cargo invocations and 240 seconds aggregate,
including generation of the real trace. Use `--offline --locked`; no installs.
The run must be one process at a time, individually bounded to 120 seconds and
1 CPU / 1 GiB. If the cache or native toolchain is unavailable, return the exact
owner/environment obstruction; do not change manifests or fetch dependencies.

## Review and integration

After both producers stop and all outputs are frozen, a fresh non-author
reviewer checks source/HIR authentication, `SourceNodeKey` and
`HirParameterId` provenance, actual Apply/body/argument incidence, nested
shadowing/restoration, trace serialization, Lean trace use and the exact
original-parent application. The reviewer is read-only and performs no
checker/build/test. Luna adjudicates and records the outcome. An accepted finite
trace leaves the universal extraction law and all original gates OPEN.

Review lease:

- `tasks/agent-loop/inbox/inline-authentic-extraction-20261027-review.md`
- scratch only: `/tmp/yulang-inline-authentic-extraction-20261027/review`

## Primary paths, budget and stop conditions

Primary owns this contract, its uniquely named outcome file and
`tasks/agent-loop/current.json`:

- `tasks/agent-loop/sprints/inline-authentic-extraction-20261027-r1.md`
- `tasks/agent-loop/sprints/inline-authentic-extraction-20261027-r1-outcome.md`

Total: 3600 active seconds—proof 1200, implementation 900, primary 600,
review 720, dispatch 180. Astra 0. Reserve review/integration capacity. The
nine user-released capacity reservations remain accounting-only and confer no
path rights; legacy UNKNOWN identities and quarantines remain unchanged. No
additional checker/Cargo process may overlap the active verification owner.

Stop for a foreign-owner acceptance, wrong binder or Apply join, stale scope,
allocation contradiction, pin mismatch, unowned semantic/API change, resource
bound, path conflict or user STOP. Preserve failed execution receipts. Consult
the selector at a material counterexample/owner obstruction, dependency or
lease/resource change, review seam or END—not after every internal result.

## Frozen input pins

Every pin must match before assignment. Baseline is the clean supplied tree at
`7a8423743c3f3b7bed9860a2def5f4c23e3e943b`.

| Input | SHA-256 |
| --- | --- |
| `tasks/agent-loop/sprints/inline-identity-interpretation-20261027-r1.md` | `2f58d64fdba41d66bb4049ae7e5236c439f2426c0f8eabd1b93fe627a183b94f` |
| `tasks/agent-loop/sprints/inline-identity-interpretation-20261027-r1-outcome.md` | `db87f99ebabc7fa119cc2bf5c3e84704c7ef080819099416932145645082f2ce` |
| `notes/theory/lean/YulangClosure/OriginalInlineIdentityInterpretation.lean` | `3aca1be7523880d0fef1cc8b2991ade174fda2c79445e9e9014982eccccb352a` |
| `notes/theory/lean/AuditOriginalInlineIdentityInterpretation.lean` | `6cdee91fb3afc311453618eba2df6a21cd84cbaf7ba1f16119df7695243a2c0c` |
| `tasks/agent-loop/inbox/inline-identity-interpretation-20261027.md` | `4e8a2d012d54707c1ef1560a95bb80424047f2598d704e8abe96a25ae164eaf5` |
| `tasks/agent-loop/inbox/inline-identity-interpretation-20261027-source.md` | `05afe4c31201caef5fd1a3df278bab2739d85e9cbbacc7691674ef66823d04ba` |
| `tasks/agent-loop/inbox/inline-identity-interpretation-20261027-review.md` | `26efb87db3a1b39faca1ab28293c085df7f63a3c29da3a451063c317e8bce1ea` |
| `notes/theory/lean/YulangClosure/OriginalIdentityEntryOrigin.lean` | `9df7fccfe03becec491665a28a7fb65760e1245d76e68330fc9626da5533163e` |
| `notes/theory/lean/AuditOriginalIdentityEntryOrigin.lean` | `dc2eaa3f53d9b841c108040fd2a4d7bb6f05d8eac52bd4b37e4957d1a79583b2` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `crates/yu-hir/src/module.rs` | `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646` |
| `crates/yu-hir/src/source_identity.rs` | `4bd5fa4066a1fd445a9757374c44d602decd1d791a394cd81c6066efa063fb23` |
| `crates/yu-hir/src/shadow.rs` | `b964bab6dcdb7ebeca9f964c134ac8fb041c928c20ce0a895fea6b6af0fbb93e` |
| `crates/yu-hir/src/lib.rs` | `4daa2b1753fcf2984c5c27bacb968541c51115ca9f7619d36f8c0e6c7972ef5b` |
| `crates/yu-syntax/src/full_parse.rs` | `dd92603f8f5549b8b3f6e45ab6cb39b6598480b7f1cda7897e27b5113107db93` |
| `crates/yu-syntax/src/lib.rs` | `770a4af4a5832b3210050b4fc5513545569b0ca4718597f67434a714f76f301d` |
| `crates/yu-hir/tests/inline_lambda_local_source.rs` | `1fe9cc2e03ffb4d633dab22d2d9c8f6a9682d8013feded572fb2251a77442899` |
| `tools/inference-playground/Cargo.toml` | `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56` |
| `tools/inference-playground/src/lib.rs` | `45bf78af436efa50e02ca97ba3b639c11f7dd88272d87c47f2822643786653d4` |
| `tools/inference-playground/src/runtime/program.rs` | `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907` |
| `tools/inference-playground/src/runtime/machine.rs` | `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e` |
| `Cargo.toml` | `a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a` |
| `Cargo.lock` | `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5` |
| `crates/yu-hir/Cargo.toml` | `a97f52fc6b9e577f23be4160ecdda9693bec8fe48c626d0e9b7c0e3b0c6fe8d1` |
| `crates/yu-syntax/Cargo.toml` | `567b705fabf7558250dbfa59e833d4ff04cb3041db8ed742311865d8cf3081d3` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
