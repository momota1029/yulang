# R190 result — resumed suffix expired-Grant test alignment

Status: RESULT, provisional test-contract correction; no runtime semantic change.
Contract SHA-256: `653d390205286766945ae721be99e07f2e9614eee32ad4e40d890b93f200a2aa`.
Baseline: `f95c0ec439fe69385cedc5e2bbe99a5329560fad`.

## Change and evidence

The positive fixture and the existing fresh-owner guard are source-equivalent
for event-1 handler eligibility. Kept the guard's fresh-owner expiration and
changed the duplicate fixture to require `Unavailable(HandlerEvidence)` at the
inner Catch range `87..123`. This confirms the saved suffix resumes far enough
to request `other 23` at that Catch; it does not falsely report that the suffix
was dropped. The test that changes only the outer arm remains and still checks
that the original unmatched `tick` request and nonempty suffix are exposed.

Only `tools/inference-playground/tests/runtime_unmatched.rs` changed. No runtime
code, Yulang2 sample output, solver behavior, or Grant condition changed. The
test now imports `RuntimeUnavailable` and names the resumed fresh-owner outcome
directly.

Checks:

- `RUSTC_WRAPPER= cargo test -q -p yu-playground --test runtime_unmatched --test runtime_resume` — passed (1 unmatched test, 19 resume tests).
- `RUSTC_WRAPPER= cargo test -q -p yu-playground` — passed; all package test binaries completed with zero failures.
- `python3 tools/agent_sprint.py check` and `git diff --check` — passed.

Cargo emitted existing warnings from dirty solver/HIR worktree dependencies;
those files were outside this sprint's lease and were preserved. No independent
review was available under the solo-worker constraint. Raw continuation source
semantics remain OPEN because the reviewed receiving theorem excludes raw
Resume. Parent/A/B/source-native/production remain OPEN; this test correction
does not close them. Charged 180s of a fresh 600s cap; 420s unspent, no
carryover. All writes stopped.
