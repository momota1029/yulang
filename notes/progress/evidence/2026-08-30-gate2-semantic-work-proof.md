# Declaration companion Gate 2 semantic-work proof and bounded evidence

Status: Gate 2 evidence complete; independent performance and specification reviews approved.

Authority:
`notes/design/2026-08-30-declaration-companion-gate2-performance-amendment.md` §§2–8.

The source proof and harness-identity sections below were closed before any prebuild, package-wide
test, ignored harness, or timing run. The authorized bounded work is recorded in the final sections.

## Source identities

- Baseline commit: `07fac51e506585131362a39b59f747fb19ca17d5`
- Baseline tree: `3e1774424d19625f156b142c47a6f5790bac5d72`
- Candidate tree, written through an alternate index containing only the three owned file updates:
  `b269b31d728d91fa7dad8fd5a1ae63ae298163d5`
- Candidate working blobs:
  - `grammar/declaration/companion.rs`: `8ef07248059d9e2d3861f3563fff2ad547557152`
  - `grammar/expression.rs`: `e60fd2f65e4f5bab27187b434544f3b414226f51`
  - `session.rs`: `d3b873bc5b03527b787723b7b324b1fdabd8539c`
- Binary diff size: 105,637 bytes
- Binary diff SHA-256: `cf047b3af7a0c89c915066128cae0a7a1919bfa37e108680e195da00da1b5f86`
- Numstat:
  - `companion.rs`: +1596/-2
  - `expression.rs`: +884/-57
  - `session.rs`: +71/-0

The exact candidate diff is retained as
[2026-08-30-gate2-semantic-work-candidate.patch.gz.b64](2026-08-30-gate2-semantic-work-candidate.patch.gz.b64).
Its encoded-file SHA-256 is
`b95d30a4b4d50fd9e456f3a1c70253fac0b51208bca4022b001482b10e7e2219`; decoding with
`base64 -d | gzip -d` produces the 105,637-byte binary diff and the diff SHA-256 above.

The candidate tree was produced without changing the shared index:

```text
GIT_INDEX_FILE=<temporary-index> git read-tree 07fac51e
GIT_INDEX_FILE=<temporary-index> git add -- \
  crates/yu-syntax/src/grammar/declaration/companion.rs \
  crates/yu-syntax/src/grammar/expression.rs \
  crates/yu-syntax/src/session.rs
GIT_INDEX_FILE=<temporary-index> git write-tree
```

## Protected ordinary bodies

The protected comparison uses this exact top-level source-slice extractor. For each rustfmt-formatted
module-level function it starts at the definition line containing `fn <name>` and includes source
through the first unindented closing brace. `awk` emits the final newline in both baseline and
candidate slices.

```text
for gate2_fn in \
  parse_statement_sequence \
  parse_braced_statement_sequence \
  commit_statement_sequence \
  commit_braced_statement_sequence \
  commit_statement_sequence_statement \
  commit_canonical_statement
do
  git show 07fac51e:crates/yu-syntax/src/grammar/expression.rs |
    awk -v name="$gate2_fn" \
      'index($0, "fn " name) {inside=1} inside {print} inside && /^}$/ {exit}' |
    sha256sum
  awk -v name="$gate2_fn" \
    'index($0, "fn " name) {inside=1} inside {print} inside && /^}$/ {exit}' \
    crates/yu-syntax/src/grammar/expression.rs |
    sha256sum
done
```

The following protected slices have identical baseline/candidate SHA-256 values:

| Function | Baseline and candidate SHA-256 |
| --- | --- |
| `parse_statement_sequence` | `8e6cb84472ab3123c1fbdce6f665a7c20fddb2fa47e83d457112f15998275ed8` |
| `parse_braced_statement_sequence` | `c4d8231c52402569d1670cb26a1e8ab050c32eb88bd0b536856a03db285c376d` |
| `commit_statement_sequence` | `f1b8a28e41e5133a0d27504b11331dd3c76919f8b555b5d05f5f1511c3618baa` |
| `commit_braced_statement_sequence` | `ce96d8a4e1d2c25e5418f9a12fa1fb87f7a61147bec46a5af35c6ccc736f0085` |
| `commit_statement_sequence_statement` | `9a2bd2d57752f701c421d92896ab009d81ae72aed09eb734b15bfa5a2c1fcfd0` |
| `commit_canonical_statement` | `f71b01f559e496e57df204d77418c71deb1d321ce1d4400684662d0d7cfa17fe` |

Only the three ordinary recovery helpers authorized by the recovery amendment changed:

- `direct_canonical_statement_candidate` delegates to the shared input-only candidate;
- `braced_next_statement_leading` delegates to the shared missing-separator trivia decision;
- `statement_sequence_error_retry` delegates to the shared comment-atomic invalid-run scanner.

## Call-edge audit

The shared input candidate has these production call sites only:

1. `recognize_braced_missing_separator_trivia`, after accepted separator recognition fails;
2. `direct_canonical_statement_candidate`, preserving the existing recovery/probe API;
3. `canonical_statement_invalid_run`, only after a non-empty malformed prefix.

`canonical_declaration_statement_intro` is called only by
`canonical_statement_candidate_input`.

Authorized helper call sites:

- `braced_next_statement_leading`: one call from `commit_braced_statement_sequence`, only after
  separator recognition fails;
- `statement_sequence_error_retry`: one call from `commit_statement_sequence_statement`, only after
  `commit_canonical_statement` returns false;
- `direct_canonical_statement_candidate`: pre-existing declaration recovery/probe sites in
  `mod_decl.rs` ×4, `role_decl.rs` ×1, `act_decl.rs` ×1, and `impl_decl.rs` ×1.

No ordinary entrypoint calls a companion adapter. The four adapter definitions have call sites only
inside `companion.rs`'s `#[cfg(test)]` module. No accepted ordinary path reaches the shared recovery
candidate, malformed-run scanner, or companion/Derives decision.

## Accepted-path operation ledger

Every before/after count is unchanged. The owning ordinary bodies are byte-identical.

| Path and position | Executed semantic work, baseline → candidate | Delta |
| --- | --- | ---: |
| AST indented, first accepted item | policy branch; `Vec::new`; canonical parse ×1; result push ×1 | 0 |
| AST indented, separator-followed item | owner-stop judge ×1; separator recognizer ×1; terminal judge as applicable; canonical parse ×1; push ×1 | 0 |
| AST indented, terminal dedent | owner-stop/separator terminal decision; no candidate, parse, traversal, or push | 0 |
| AST braced, first accepted item | close-pending checkpoint/recognizer ×1; `Vec::new`; canonical parse ×1; push ×1 | 0 |
| AST braced, separator-followed item | close-pending ×2; separator recognizer ×1; canonical parse ×1; push ×1 | 0 |
| AST braced, terminal close | close-pending ×1; no candidate, parse, or push | 0 |
| Direct indented, first accepted item | Statement node start/finish ×1; canonical commit ×1; recovery edge not taken | 0 |
| Direct indented, separator-followed item | owner-stop probe ×1; separator recognizer probe/emitter ×1; terminal probe as applicable; Statement wrapper ×1; canonical commit ×1 | 0 |
| Direct indented, terminal dedent | existing owner-stop/separator probe; no candidate or Statement commit | 0 |
| Direct braced, first accepted item | existing close/EOF judgment; Statement wrapper ×1; canonical commit ×1 | 0 |
| Direct braced, separator-followed item | close probe ×1; separator recognizer/emitter ×1; existing slot judgment; Statement wrapper ×1; canonical commit ×1 | 0 |
| Direct braced, terminal close | close probe ×1; return; missing-separator candidate not queried | 0 |

Across every row:

- traversals remain 0 → 0;
- clones, caches, replays, and indirect dispatch remain 0 → 0;
- companion/Derives queries remain 0 → 0;
- new accepted-path probes and calls are zero;
- AST retains only the existing ordinary result vector;
- direct CST streams to its existing sink.

The companion focused table resets a cfg(test)-only candidate counter and asserts zero candidate
calls for valid 1k and 10k sequences in all four companion adapters.

## Static allocation and reachability audit

- Exactly four companion adapters exist: AST/direct × indented/braced.
- They remain production-unreachable in Gate 2.
- Normal companion items call canonical Statement parse/commit directly.
- Companion AST owns one `Vec<Recovered<DeclarationCompanionItem>>` and the already-authorized
  per-item `Box<Statement>`; direct CST owns no result vector and performs no replay.
- No runtime companion mode, generalized sequence abstraction, trait object, function pointer,
  closure dispatch, cache, side index, static initializer, or accepted-path allocation was added.
- `session.rs` snapshot/prefix-output helpers and the candidate counter are `#[cfg(test)]` only.

## Ordinary measurement harness identity

Stable markers:

```text
// GATE2_ORDINARY_PERFORMANCE_HARNESS_BEGIN
// GATE2_ORDINARY_PERFORMANCE_HARNESS_END
```

Marker-inclusive extraction:

```text
sed -n \
  '/^    \/\/ GATE2_ORDINARY_PERFORMANCE_HARNESS_BEGIN$/,/^    \/\/ GATE2_ORDINARY_PERFORMANCE_HARNESS_END$/p' \
  crates/yu-syntax/src/grammar/expression.rs
```

- Extracted size: 3,117 bytes including final newline
- Extracted SHA-256: `75b7761544e94faa07179108350b72cf72a3ff1aa82be3aea2ea05ec01ccad72`

The detached baseline was prepared at
`/tmp/yulang-gate2-baseline.oZ5veV/worktree` from detached HEAD
`07fac51e506585131362a39b59f747fb19ca17d5`. The exact marker-delimited candidate block was inserted
immediately before the baseline test module's final brace with `apply_patch`. Before either binary
was built, the extraction above produced this retained identity result:

```text
candidate_bytes 3117
baseline_bytes 3117
candidate_sha256 75b7761544e94faa07179108350b72cf72a3ff1aa82be3aea2ea05ec01ccad72
baseline_sha256 75b7761544e94faa07179108350b72cf72a3ff1aa82be3aea2ea05ec01ccad72
cmp_identical yes
```

Removing exactly the marker-inclusive range from the baseline working file reproduces the HEAD
blob byte-for-byte. Its only diff is the 76-line harness insertion in `grammar/expression.rs`:

```text
baseline_numstat 76 0 crates/yu-syntax/src/grammar/expression.rs
baseline_diff_bytes 3535
baseline_diff_sha256 dca94422b49a0c516a173cc8526264772f3d7ce291208252cd23f8d2bd82b58b
```

`git diff --check` passed in the detached baseline. No build, test, ignored harness, or timing process
ran during preparation.

The harness:

- accepts only `indented_direct`;
- constructs source and canonical operator table outside the repeated kernel;
- positions input and invokes `commit_statement_sequence` directly, not a root parser;
- retains and black-boxes the final result;
- validates item count, consumed range, recovery count, and losslessness once after repeats;
- contains no companion or comment-stress timing mode.

## Verification and resource inventory

Focused checks run:

```text
cargo test -p yu-syntax gate2_ordinary_recovery_table -- --nocapture
# 1 passed; 570 filtered out

cargo test -p yu-syntax gate2_companion_sequence_table -- --nocapture
# 1 passed; 570 filtered out
```

Scoped `rustfmt --check`, `git diff --check`, protected-function hashing, and static call-site audit
also passed. One initial `--exact` command selected zero tests and made no changes.

The current focused runner exposes 571 library-test entries (one selected plus 570 filtered). The
same candidate topology previously completed the package suite without resource failure before
rollback, and the current focused runs compiled the final test binary successfully. This is
sufficient inventory/resource evidence for the one final `cargo test -p yu-syntax` recorded below.
No workspace suite is authorized for this isolated gate.

## Prebuild environment and binary identities

Both binaries were built after the marker identity was rechecked at 3,117 bytes and SHA-256
`75b7761544e94faa07179108350b72cf72a3ff1aa82be3aea2ea05ec01ccad72`, with `cmp -s`
returning zero. The source was not altered after that check.

Environment:

```text
active toolchain: stable-x86_64-unknown-linux-gnu (default)
rustc: 1.92.0 (ded5c06cf 2025-12-08)
rustc commit: ded5c06cf21d2b93bffd5d884aa6e96934ee4234
LLVM: 21.1.3
cargo: 1.92.0 (344c4567c 2025-10-21)
host: x86_64-unknown-linux-gnu
profile: test (unoptimized + debuginfo)
features: default; no feature arguments
RUSTFLAGS: empty
CARGO_INCREMENTAL: 0
allowed CPUs: 0-11
selected CPU: 10, core 5; sibling CPU 11 was not selected
CPU governor query: unavailable; no governor or turbo setting was changed
```

Both worktrees used the same build command; compilation was excluded from every timing sample:

```text
env CARGO_INCREMENTAL=0 RUSTFLAGS='' cargo test -p yu-syntax --locked --no-run
```

Binary evidence:

| Revision | Binary | SHA-256 | Bytes | text | data | bss |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| Baseline | `/tmp/yulang-gate2-baseline.oZ5veV/worktree/target/debug/deps/yu_syntax-cb402ef39304271b` | `5402419faf4ca8343eec8f9466c53d0b50b5f7ec1868bdd4eaa88a5d312fa84f` | 56,807,304 | 10,804,560 | 422,217 | 2,400 |
| Candidate | `/home/momot/rust/yulang/target/debug/deps/yu_syntax-cb402ef39304271b` | `9c9b2b1c1ce9d7a135cac6e0d0f8e5793edee72876370a44c82050404a13be02` | 58,308,304 | 11,069,868 | 432,449 | 1,344 |

Executable size movement is retained as binary-layout evidence only, as required by the semantic-work
gate. It is not an accepted-path operation count.

## Bounded diagnostic measurement

The driver observed no running `cargo`, `rustc`, or `yu_syntax-*` process before the measurement or
any sample. Every sample was launched successfully through `taskset -c 10`, reported 99-100% CPU
utilization, exited zero, and ran the harness's item-count, consumed-range, recovery-count, and
losslessness assertions successfully. No independent per-child affinity observation was captured;
the utilization value is not treated as affinity proof. No sample was invalidated or retried.

The exact per-sample command shape was:

```text
timeout --foreground --signal=TERM 60s \
  taskset -c 10 \
  /usr/bin/time -v -o <raw-time-file> \
  env YULANG_GATE2_SEQUENCE_ITEMS=10000 YULANG_GATE2_SEQUENCE_REPEATS=8 \
  <prebuilt-binary> \
  --exact grammar::expression::tests::gate2_statement_sequence_performance_harness \
  --ignored --nocapture
```

The 60-second timeout was an additional per-invocation cap. The recorded phase timestamps establish
that the whole phase remained within its hard ten-minute budget. The fixed order was one unmeasured
warm-up pair `B -> C`, followed by measured pairs `B -> C`, `C -> B`, and `B -> C`. Exactly eight
benchmark processes ran, with no smoke run, extra case, retry, bootstrap, or companion/comment-stress
timing.

Raw results:

| Invocation | Class/order | Revision | Wall seconds | Peak RSS KiB | Exit/validation |
| ---: | --- | --- | ---: | ---: | --- |
| 1 | warm-up 1 | Baseline | 44.52 | 9,780 | 0; 1 passed |
| 2 | warm-up 2 | Candidate | 32.36 | 10,176 | 0; 1 passed |
| 3 | measured pair 1, first | Baseline | 36.85 | 9,780 | 0; 1 passed |
| 4 | measured pair 1, second | Candidate | 29.66 | 10,048 | 0; 1 passed |
| 5 | measured pair 2, first | Candidate | 30.39 | 9,920 | 0; 1 passed |
| 6 | measured pair 2, second | Baseline | 28.97 | 9,908 | 0; 1 passed |
| 7 | measured pair 3, first | Baseline | 28.65 | 9,780 | 0; 1 passed |
| 8 | measured pair 3, second | Candidate | 26.99 | 10,048 | 0; 1 passed |

Measured-only summary:

| Revision | Wall median | Wall range | RSS median KiB | RSS range KiB |
| --- | ---: | --- | ---: | --- |
| Baseline | 28.97 s | 28.65-36.85 s | 9,780 | 9,780-9,908 |
| Candidate | 29.66 s | 26.99-30.39 s | 10,048 | 9,920-10,048 |

Paired candidate-minus-baseline observations were `-7.19 s / +268 KiB`,
`+1.42 s / +12 KiB`, and `-1.66 s / +268 KiB`. Aggregate measured medians moved
`+0.69 s / +268 KiB`; the wall ranges overlap and the candidate was faster in two of three pairs.
Under the Authoritative §6 contract these wall/RSS observations create no tolerance and do not by
themselves pass or roll back Gate 2. The independent performance auditor recomputed the results and
adjudicated the movement against the closed call-edge and operation ledger above. It found no added
executed ordinary work and approved performance closure; the movement remains diagnostic,
layout-sensitive evidence.

The bounded phase began at `2026-08-30T23:28:55.734484614+09:00` and ended at
`2026-08-30T23:34:44.809904853+09:00`: approximately 349.08 seconds, within the hard ten-minute
ceiling. Process budget consumed: 8 of 8 authorized benchmark invocations.

Raw `/usr/bin/time -v`, stdout, and stderr artifacts are archived under
[2026-08-30-gate2-bounded-raw](2026-08-30-gate2-bounded-raw/README.md). All eight stderr files are
empty. That directory also records the exact driver shape, preflight provenance boundary, and
timestamp source. The non-empty artifact SHA-256 values are:

| Sample | stdout SHA-256 | time SHA-256 |
| --- | --- | --- |
| `01_warm_baseline` | `7034cdcf07455d7c970f0054fb5b5e864921cf73e26cf6e351724a411f6b0c94` | `93ff864ce9783d73484594b3a41ae361f29236108d23910031622ac1e2177fa1` |
| `02_warm_candidate` | `d9b437797f4b4e59b68cf9fcf1900ed4a161adefb553b833c5cd4e221e3da00f` | `9e761174d7a587f8b989500529996dee0cd9e09dfe2d06bac475c4d9463c5d64` |
| `03_measured_pair1_baseline` | `f89603157d64e8bbb7df90b2809de6ab623fb9e8808d5bd80817465c92bc4b14` | `fb4b76f87a8f81e51bf8bb2f5a51f1003f032d34c0a67ff844e9e1721c345588` |
| `04_measured_pair1_candidate` | `b439ee0e9f3a6d4ddba9b3b2596e755b53b5d93e3ea7d7ce6a74797bbfcbaac6` | `5b3429069c690e673e77e95bd7e239d44448fbaa0e2ea777aa871c61b897f8aa` |
| `05_measured_pair2_candidate` | `5a357199db372e76f470bac3b42865829433520de9dcbdcc4f6732c921a99cdf` | `62fa1622740396576bda8860836334ac388da6352e414640307d741c499ba400` |
| `06_measured_pair2_baseline` | `4c09076ac5986d46de6691822ec1ca7439004cf9a352bd83c65b62e94bde11cf` | `01313b636bc14952782d11f5183e577f2e3874978f0e548a3a88991e67a18937` |
| `07_measured_pair3_baseline` | `52c6bb3a463221a4d8b4b87f151250e15c4af2e46b452a3b0db4d0a9650e584c` | `3c9430335f5fc70514aa26bdfda4f1a699e2d328c9f0b01b1c6afbee27645ca4` |
| `08_measured_pair3_candidate` | `c0d6c2132b5bbd84346d67ed701e3667b1f3ce4bb26b67f7c3b000097c0370dd` | `0d805e51b8333c8eb8e134c8470dd7961e165d69b8f44489b6eb5af1b205c65c` |

## Final package verification

After the bounded phase, and exactly once on the candidate:

```text
cargo test -p yu-syntax
```

Result:

```text
570 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out
doc-tests: 0 passed; 0 failed
```

The ignored entry is the manual Gate 2 measurement harness. No workspace suite or repeat package
suite ran. Existing compiler warnings were emitted; there was no new build or test failure.
