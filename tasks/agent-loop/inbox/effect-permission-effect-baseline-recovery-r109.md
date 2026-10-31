# R109 `candidate_effect.rs` baseline provenance recovery

Assignment: R109 `candidate_effect.rs` baseline recovery. Requested model and
effort: Luna/high. Observed runtime model metadata: UNKNOWN. Worker: Luna
primary's assigned read-only recovery lane; no descendants.

## Result

The complete R107 baseline is recoverable from authenticated immutable Git
objects. Its SHA-256 is
`1c80c55c62b724b9d2080bd2ddcdabfa35a5ba641c1bf45d9735dfd7fd05be41`.
The corresponding Git blob object is
`20c1635c7c3974a22ff14b62916cad76062e256c`, addressed by
`d177c46ec61fcadd70a3d587c2f8934f6bc91f46:crates/yu-solver/src/candidate_effect.rs`.
The same complete bytes occur at that path in the R98 base `fd97f480...`,
R105 base `d1931550...`, and R108 checkpoint `54526ec9...`.

The live file SHA-256 is
`4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15`, matching
the R106/R107 frozen pin. A read-only Git comparison against the R107 baseline
reports 1,144 insertions and 36 deletions (1,180 changed lines total).
The current-versus-baseline byte comparison is therefore reproducible from
the named immutable blob and the live file; no source reconstruction or
materialization was performed.

## Provenance that the records support

- R98 records the `candidate_scheme::RowKey` import and test/source observer
  edits. Its frozen `candidate_effect.rs` hash was
  `bf7528133a1ebaa0a80434f2bf114d21c06717235575bab45fbf4c5dffc7cb57`.
  R98's compile gates failed before tests; this is not approval of its source
  candidate.
- R104 records test-only source/capture/route observers and related fixtures.
  Its final candidate hash was `fab53f41cba94da6ada8850ae99b4ab03a7bfce46ff8f71306dc1b77ade73cb5`.
  Its final reviewed Cargo run had 47 passed, four failed, and two ignored;
  it does not authenticate the later R106 bytes.
- R105 retained the R104 hash and made no Rust edit.
- R106 added the test
  `r106_named_result_function_is_captured_freshened_and_consumed` (the R107
  diff places its addition at current line 2968). R106 records that stripping
  this block from the candidate gave
  `0c0f9ccd62eb274c5b603e4d9b37c76cc8ae52e6a95a3346f81349da49ef26d4`, not the
  R105 hash `fab53f41...`. Its author says generic, unscoped test-source/`Arc`
  spelling replacements may have matched pre-existing test code outside the
  new block. The R106 test was not run.
- R107's independent review accepted the classification that the complete
  pre-R106 file was not recovered and that the current bytes are uncertain.

## Exact unresolved attribution

The immutable baseline makes every changed byte visible, but the allowed
records do not contain R106 revision 1's complete candidate bytes or a
machine-applicable patch for its generic replacements. R104 and R105 preserve
only the pre-R106 SHA-256, not the complete file bytes. Consequently the
R106 block-removal hash proves a mismatch but does not identify which
outside-block byte ranges were changed by which replacement. The current Git
diff also includes the already recorded R98/R104 changes, so it cannot by
itself assign those outside-block edits to R106. I cannot attribute every
current difference to a specific transformation or reconstruct an exact
pre-R106 artifact from the evidence in this lease.

The precise missing artifact is an authenticated complete R106 revision-1
source snapshot or its exact edit patch with preimage and replacement for each
unscoped operation. Without it, the R106 outside-block region(s) remain
unattributed. No guessed reverse edit or restored source is claimed.

## Commands and receipts

Read-only command forms run (the multi-file reads were parallel `cat` calls):

```text
cat tasks/agent-loop/sprints/effect-permission-effect-baseline-recovery-20261101-r109.md
rg --files tasks/agent-loop/inbox tasks/agent-loop/history tasks/agent-loop/sprints | rg 'effect-permission-(candidate|.*r9[8]|.*r10[4-7]|.*r98|.*r104|.*r105|.*r106|.*r107)'
cat tasks/agent-loop/inbox/effect-permission-rust-observer-compile-repair-source.md
cat tasks/agent-loop/history/effect-permission-rust-observer-compile-repair-20261101-r98-outcome.md
cat tasks/agent-loop/inbox/effect-permission-source-causality-r104-source.md
cat tasks/agent-loop/history/effect-permission-source-causality-20261101-r104-outcome.md
cat tasks/agent-loop/inbox/effect-permission-source-contract-r105-source.md
cat tasks/agent-loop/history/effect-permission-source-contract-20261101-r105-outcome.md
cat tasks/agent-loop/inbox/effect-permission-source-admission-r106.md
cat tasks/agent-loop/history/effect-permission-source-admission-20261101-r106-outcome.md
cat tasks/agent-loop/inbox/effect-permission-baseline-reconstruction-r107.md
cat tasks/agent-loop/history/effect-permission-baseline-reconstruction-20261101-r107-outcome.md
sha256sum crates/yu-solver/src/candidate_effect.rs
git show fd97f480fd1090f686907a44072ba736649ac5e5:crates/yu-solver/src/candidate_effect.rs | sha256sum
git show d19315503f911c615d4d3a9ab9329146f757acbf:crates/yu-solver/src/candidate_effect.rs | sha256sum
git show d177c46ec61fcadd70a3d587c2f8934f6bc91f46:crates/yu-solver/src/candidate_effect.rs | sha256sum
git show 54526ec9514b7065c7d7460702e9d6e2ecbc0842:crates/yu-solver/src/candidate_effect.rs | sha256sum
git rev-parse d177c46ec61fcadd70a3d587c2f8934f6bc91f46:crates/yu-solver/src/candidate_effect.rs
git diff --numstat d177c46ec61fcadd70a3d587c2f8934f6bc91f46 -- crates/yu-solver/src/candidate_effect.rs
git diff --stat d177c46ec61fcadd70a3d587c2f8934f6bc91f46 -- crates/yu-solver/src/candidate_effect.rs
git diff --unified=0 d177c46ec61fcadd70a3d587c2f8934f6bc91f46 -- crates/yu-solver/src/candidate_effect.rs | rg '^(diff --git|@@|\\+[^+].*(#\\[test\\]|fn |RowKey|effect_|source_|formal_|support_|capture_|fresh_|Candidate))'
git diff --unified=2 d177c46ec61fcadd70a3d587c2f8934f6bc91f46 -- crates/yu-solver/src/candidate_effect.rs | rg '^(@@|-[^-])'
git diff --unified=4 d177c46ec61fcadd70a3d587c2f8934f6bc91f46 -- crates/yu-solver/src/candidate_effect.rs | rg '^@@'
git diff --unified=4 d177c46ec61fcadd70a3d587c2f8934f6bc91f46 -- crates/yu-solver/src/candidate_effect.rs | sed -n '/@@ -2802/,/@@ -3100/p'
```

The baseline SHA matched in all four named commits; the live SHA matched the
R107/R106 pin; Git reported `1144 36` and `1 file changed, 1144 insertions(+),
36 deletions(-)`. The R106 block-removal result is reused from the independently
reviewed R107 handoff/outcome; it was not recomputed because the allowed
assignment prohibits source materialization and scratch artifacts. No Cargo,
build, test, compiler, checkout, worktree, copy, cache, environment, Git
mutation, staging, or push command was run. No quarantined path was accessed.

All reads and commands completed within the 300-second assignment bound; exact
active runtime timing is unavailable. Changed path: this sole leased handoff.
Generated or disposable scratch: none. Source path remains untouched. Author
writes stop after freezing this revision 1; independent review is pending.

## Boundary and next related step

This establishes an authenticated complete baseline and a byte-comparable
current diff. It does not establish exact R106 transformation provenance,
source correctness, compilation, a theorem, source/native correspondence, or
permission to integrate the live candidate. The next related step is a fresh
read-only independent review of this handoff and its exact Git/hash receipts.
If exact R106 attribution is required, Luna needs a separately authorized
recovery source that contains the missing complete snapshot or edit patch.
