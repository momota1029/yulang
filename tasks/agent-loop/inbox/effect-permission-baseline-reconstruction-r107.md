# R107 Rust baseline/provenance audit

Status: frozen research evidence; independent review PENDING. Author
`/root/r107_rust_baseline`; no descendants. Claim class: bounded byte
characterization and source classification, with conditional integration
recommendation. No implementation, semantic, theorem or production approval.

## Objective, baseline and authority

Map the six dirty solver files against baseline
`d177c46ec61fcadd70a3d587c2f8934f6bc91f46`, R107 contract SHA-256
`47bf64e9e7e3d099c002083d1300a1573e49458f0064c820e7876b0d2b823efa`.
Apply `AGENTS.md`, preserved hard invariants in `AGENTS.pre-sprint.md`,
`rules/research-lab.md` and its preserved evidence-quality/one-baseline clauses,
`rules/design-authority.md` (authority order and test contracts),
`rules/git-concurrency.md` (disjoint leases and frozen snapshots), and
`rules/goal-driven-sprints.md` sections 2, 5 and 7. The sprint skill was read.
The top-level inference principles sections 1, 1.1, 3 and 4 remain binding.
No selected language meaning is changed. In particular, source admission,
effect hygiene, original A/B quantifiers and source/native correspondence
remain obligations; observation checks cannot establish them.

Only this inbox path was written. All source reads were limited to the six
named files and their immutable baseline blobs. Relevant R98/R104/R105/R106
handoffs/outcomes were read; quarantined runtime paths were not accessed.

## Frozen six-file inventory

Hashes are SHA-256 of complete bytes; all current hashes matched the R107 pins.

| File under `crates/yu-solver/src/` | Baseline blob | Current bytes |
| --- | --- | --- |
| `candidate_effect.rs` | `1c80c55c62b724b9d2080bd2ddcdabfa35a5ba641c1bf45d9735dfd7fd05be41` | `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15` |
| `candidate_receiver.rs` | `6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2` | `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf` |
| `candidate_scheme.rs` | `064df99d57aa657f6f1491f16b249403d2ee155b36142e15ca67cafb070df070` | `4494ba879a05f90767779e12c9ca8e1364f2203f2f60eb63239a544c0d0da470` |
| `candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `lib.rs` | `c43fcc4f39e4ba8bfea10aa39879c37973100d9f4b8bdef71fa5b3dc3fae01df` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| `shadow_apply.rs` | `2e0aba4d172e97dd60ba909a7aca873c109785f3d38cce46ddd033c70f64613d` | `caeb837cd13b2e75e76fbed59dcc601e8c9d0a6a6a6f56f6959c0b0b9a98007f` |

## Responsibilities and compilation classification

`lib.rs:210–236` gates all five candidate modules and `shadow_apply` on
`shadow-apply-candidate`. Thus ordinary compiled candidate behavior below
means a non-test build with that feature. It does not imply default-feature
behavior or approved production behavior.

- **candidate_effect:** R98 adds the existing `candidate_scheme::RowKey`
  import; it resolves ordinary feature-build name resolution. Remaining
  pre-test-module deltas are `cfg(test)` typed constructor/origin/memo/delegated
  port/capture witnesses and textual Support logs, plus equivalent statement
  expansion/line wrapping around existing calls. The test module begins at
  current line 2829. It contains added source-tree/port expectations,
  source/capture/remap inventories, protected-case observations and the R106
  test at line 2968. These are test code and observers, not new solver rules.
  Current complete bytes are **uncertain**: R106 admitted unscoped replacements
  outside its new block. No full pre-R106 preservation claim is possible.
- **candidate_receiver:** exactly four changed hunks. Three dereference
  `HirOccurrenceId` comparisons (current 4187, 4386, 4628 vicinity), resolving
  R98 type errors without changing intended equality. The fourth replaces
  the incomplete Definition/Expression match with
  `local_source.hir.owns_source_root(&registration.owner)` at line 4433,
  covering Member through the existing ownership API. These occur outside
  `cfg(test)` in feature-gated inventory/certificate code. They are compiled
  observer/validation behavior, not test-only edits. R98 fixes are exactly
  attributable; the fourth hunk is present as an R104 frozen dependency and
  compiled in its final run. The inspected records do not identify its
  original author's exact earlier packet; no invented provenance is assigned.
- **candidate_scheme:** mixed component. Ordinary feature code retains raw
  `entry_effect` through `LambdaArgumentEffectCapture`, its fresh incidence,
  capture extraction and fresh remap; exposes the private native incidence
  type to sibling modules; adds
  `bind_native_formal_entry_permission_use` at line 505. This adapter validates
  registration, occurrence and route identity, then calls the existing
  effect-state binder. It is a read-only evidence adapter with no retained
  consumer, but its data fields/capture bookkeeping compile outside tests.
  Separately, `formal_capture_trace_id`, intern/canonical row witnesses,
  capture-owner logs and captured-row events are `cfg(test)`. Complete current
  bytes match the R104 reviewed/final-run pin. R98 already depended on a
  different dirty scheme hash; R104 provenance alone does not assign authorship
  or independent approval to every earlier ordinary adapter hunk.
- **candidate_source:** only two added `cfg(test)` calls around
  `execute_candidate_action` at 2453/2460; they log schedule/action and
  diagnostics before/after. Current hash is R104's exact reviewed final pin.
  No ordinary source collection/admission decision changes in this delta.
- **lib:** three ordinary feature-build compile repairs from R98: two
  unavailable `exhausted` references become the existing
  `SolveAvailabilityError::IdentityExhausted`; the private
  `candidate_source::SourceRootId` path becomes the imported `SourceRootId`.
  R104 adds `cfg(all(test, feature=...))` constraint/diagnostic logs and
  `cfg(test)` logs inside the feature propagation branch. Existing calls are
  bound to `result` and returned unchanged. Complete current hash matches
  R104's reviewed/final-run pin. Calling this whole file delta test-only
  would omit the R98 compilation repairs.
- **shadow_apply:** the permission-export event is `cfg(test)` and reads
  effect witnesses plus `Graph.formal_capture_trace_id`. Two `Graph` test
  literals inside the `cfg(test)` module gain `lambda_argument_effects` and
  `formal_capture_trace_id`. These dirty deltas are test-only; they do not
  change ordinary solve admission. Current hash is an exact R104 frozen
  dependency. R98 used an earlier dirty shadow hash, so the full earlier
  authorship/review history is not reconstructed by the inspected evidence.

## Discriminating byte-recovery experiment

Executed a single-process Python 3 in-memory comparison using
`git show d177c46...:<one of the six paths>`, `pathlib.read_bytes/read_text`,
`difflib` and `hashlib`; no patch, scratch, cache or environment was created.
The initial `python` command was unavailable (exit 127); only `python3` ran.
No compiler/checker/test invocation occurred.

1. Apply exactly the three R98-v2 authorized `lib` textual replacements to
   its immutable baseline blob. The multiline candidate-graph context matched
   once. Result SHA-256 is
   `6eb6b5df29bda1d1bd1fecabcbc2cc6e85e777dda2045f1d1ab86084f64cd84f`,
   exactly R98's frozen final `lib` hash. This reconstructs the entire reviewed
   historical file in memory, excluding R104 observer additions.
2. Apply exactly the three R98 receiver dereferences to its baseline blob;
   each old expression matched once. Result is
   `03553455bb3b0a4cb0f0ad2fb04b1b8dbf8fac00982547323fe8b6439edbb34d`,
   exactly R98's frozen receiver hash. Replacing the one incomplete owner
   match with the current ownership API then yields
   `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf`,
   equal to the complete current receiver file.
3. As a negative discriminator, adding only the two visible
   `lambda_argument_effects` initializers to baseline `shadow_apply` produces
   `2fa42a5570e660babab5da6361e0d71e0c022b234a21f7e01b78eafbfc65f278`,
   not its R98 dependency pin `c328e086...`. Therefore those additions alone
   do not recover that historical input; no further guessed restoration was
   attempted.

Coverage is six complete baseline/current byte comparisons and the three
specific reconstruction trials above. No random seeds, semantic enumeration
or mutation tests apply. Hash equality is an independent byte oracle relative
to the producer's reported edits; it shares trust in Git blobs, SHA-256 and
the historical receipt hashes. It proves reconstruction of bytes, not source
rules, runtime correctness or provenance of unrecorded edits. Failure
conditions are a hash/context mismatch, stale dependency, or missing original
receipt. The shadow mismatch is preserved as incomplete recovery evidence.

## Prior gates and exact remaining obstructions

- R98 diagnostic compile: exit 101, nine errors, no tests, 29.64 s,
  643,192 KiB RSS. Final compile: exit 101, incomplete Member match,
  no tests, 29.59 s, 634,340 KiB RSS. R98 final gate FAILED; its allowances
  exhausted. The reconstructed lib/receiver hashes belong to this failed
  snapshot, not a passed focused test gate.
- R104 early reviews rejected missing/no-row/remap observations. The repaired
  first Cargo call failed compiling an unsupported Debug formatter (exit 101,
  73.13 s, 1,211,796 KiB). Those earlier candidate successes are superseded
  by the final reviewed formatter bytes. Final call compiled and ran: 47
  passed, four failed, two ignored, 771 filtered; exit 101, 98.91 s,
  1,727,936 KiB. Independent receipt review passed; source promotion failed.
  This supplies compilation evidence for five unchanged current files with
  the **older** effect hash `fab53f41...`; no current-combination pass follows.
- The protected failures remain shared-tail Int/Function conflict,
  identity-only unequal transport (no ParentWrite), recursive consumer with
  no returned effect forms, and live Support absent from both captured
  templates. Later assertions were not reached. R105 established that the
  shared-tail direct-session helper bypassed ordinary `solve` and returned
  `pure : alpha -> Int` against an incompatible function-to-function terminal
  annotation. This is not a proven solver omission. Identity-only transport
  does not locate canonicalization loss; live Support does not establish
  capturable reachability or remapping loss.
- R105 Rust: no edits, Cargo 0/1, accepted source-contract obstruction only.
  Its unchanged effect baseline is `fab53f41...`.
- R106 revision 1/2 candidate reviews rejected negative concrete-port and
  consumer-type mistakes. Final report review accepted its corrected chain
  `left id -> first id -> run 1` and honest uncertainty. The test remains
  UNRUN, Cargo 0/1. Removing its new block yielded
  `0c0f9ccd62eb274c5b603e4d9b37c76cc8ae52e6a95a3346f81349da49ef26d4`,
  not `fab53f41...`; the author acknowledged generic replacements may have
  modified protected older code. No exact pre-R106 full bytes are recovered.

## Dependency boundary and recommendation

The smallest recovered **candidate** is the three-hunk R98 `lib` compilation
repair, reconstructed as complete hash `6eb6b5df...`. It uses baseline types
and the already imported error/owner identities; it introduces no references
to new effect observer helpers or scheme fields. Thus it is dependency-closed
with respect to dirty deltas in these six files and avoids uncertain effect
bytes. Each smaller individual repair leaves other known baseline feature
compile defects; the three-hunk cause is the coherent minimum in this owner.
This is recoverability, not a stageability or passing-build claim. Whole-feature
verification additionally needs the three receiver fixes and complete Member
ownership handling, plus any other baseline failures not inspected here.

The exact current receiver is a second recoverable four-hunk candidate,
independent of new effect trace symbols. Its fourth hunk depends on the
external HIR `owns_source_root` API: R104 records HIR `module.rs` hash
`6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`,
but this audit was not leased that source. Its present API and full provenance
therefore require fresh primary/reviewer validation. Do not infer that the
R98 failed snapshot independently approved this later hunk.

The R104 observer component is coupled: scheme/source/lib/shadow events call
effect trace helpers; scheme Graph trace fields require matching test literals;
effect tests inspect scheme and route inventories. It cannot be promoted from
the current effect file because protected-byte preservation is unresolved.
The scheme ordinary entry-effect/permission adapter is distinct from test
observers, but its exact earlier review history and dependency-closed
verification are not recovered here. Do not extract it by intuition or call
the mixed file observer-only. Complete source promotion remains obstructed.

Recommended next action: freshly review the three-hunk reconstructed R98 lib
candidate and current receiver boundary against exact baseline/HIR inputs in
a separately authorized reconstruction/verification packet. Preserve the
entire current effect file; seek an authenticated pre-R106 byte artifact
before any dependent observer or R106 execution.

## Evidence pins, resources and handoff

Direct receipt SHA-256 pins:

| Receipt | SHA-256 |
| --- | --- |
| R98 source handoff | `ef3de85b8f4cee9fc550ec5c29f0203714412023b5484883e6ca2425b8861546` |
| R98 outcome | `ada9ab138fba5ebe480eccfdc58229d9bb18d624da546b486929cfbbc47d3108` |
| R104 source handoff | `4a4227fb6ca8cbefa3240cbec4b4fd485f3583750816827338b0717e0dfed5d5` |
| R104 outcome | `27017db2b1c8da8cee760695ab072ded47599f7926cd9c078ac99e266e730cc9` |
| R105 source handoff | `916527c003a2f209838b6bfbb513e21bef2f3557146fd01e3066db4a854fb44f` |
| R105 outcome | `c63b183903a5911faee34798061fd14678b77a2577f456f70e054015efe42f39` |
| R106 source handoff | `cee4b743bb7503cb8b13cdf7b1ee2ffb44929e2a416bd9b71ef7a74767c2bc81` |
| R106 outcome | `0f0ad632aba0b5e6f735c2eda7c9233d670589bd425ab0a7c183470150e779e9` |

Read-only shell commands: cat/sed/rg, six-path `git show`, Python 3 in-memory
diff/hash reconstruction, sha256sum. No Git mutations, Cargo/Rust/build/test,
scratch or environment creation. No heavyweight processes or children. Each
reported command completed in under one second; process RSS and total CPU were
not measured. Work stayed within the 300-second author envelope. Broad diff
output was truncated by the tool; focused per-file/pre-test reads supplied the
classifications, not an assertion that every large test expectation was
independently audited. No protected assertion was edited or re-executed.

Commit packet: exact leased path
`tasks/agent-loop/inbox/effect-permission-baseline-reconstruction-r107.md`;
baseline `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`; dependency changes: none;
source pins above unchanged. Review status: independent review pending.
Checks already run: byte-pin comparisons and in-memory reconstruction only.
Proposed message: `research: map R107 Rust provenance and recover compile-repair boundary`.
Shared-record deltas left to Luna/curator: candidate boundary, uncertain effect
quarantine, four protected failures, unrun R106, and separate future authority
for reconstruction/review/verification. Writes stop at this frozen submission.
