# Source-owned Value entry effect flow

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Baseline: `7bb417ea45a651071ff87da7f7d38d81a2a93879`
Status: bounded implementation integrated; focused verification/review complete
Authority: charter §§17–18, 21–24 and active Simple-sub legacy withdrawal
Mode: M2; semantic/regression reviews and fresh narrow delta reviews
Measurement budget consumed: zero timing samples / zero benchmark processes

## Dependency removed

Candidate source lambdas previously constructed a closed-empty argument-effect
port. Normal Function decomposition consequently demanded argument evaluation
purity. This rejected actual effectful arguments to unused, identity and aliased
Value parameters. It was an early local admission requirement contrary to the
approved source-owned entry behavior.

The source lambda now creates entry and invocation rows at its actual formal
level, generating `entry <= invocation` and `bodyE <= invocation`. Apply's normal
Function decomposition supplies `argumentE <= entry`. No generic propagation
shape switch, skipped comparison, solved-effect patch or global purity exception
is added. Parameter lookup and lambda construction retain exact pure facts.
Graph capture/use-time freshening and level/extrusion/intrusion transport the
ordinary rows. The owning recipes count their two additional effect facts.

Cost is two checked rows and two effect edges per candidate source lambda;
ordinary provenance and route transactions own admission and rollback. Historic
non-graph constructors retain their actual owner until default migration.

## Evidence and review

See the [integration gate](2026-10-10-value-entry-effect-integration-gate.md) for
initial failures, accepted test-oracle/coverage findings, batched repair and
pre-write adjudication of the old EmptyEffect port expectation. Fresh semantic
and regression delta reviews found no findings. Test traversal remains rooted
at the chosen invocation and includes Support allowed/tail and both stored bound
orientations; the pure sibling stays separate. Result fibers exclude the wrong
primitive and Functions. Real source levels, recursive/local use, a later
explicitly test-supplied lower, initial publication failure and partial-edge
rollback/retry are covered. The later lower is not a runtime execution witness.

Primary checks (all `RUSTC_WRAPPER=`, `timeout 180`, `-j 2 --offline`, tests use
`-- --test-threads=1`):

- `cargo test -p yu-solver --features shadow-f5,shadow-apply-candidate --lib value_entry_effect_tests`: 5 pass.
- Same command with `--test candidate_value_entry_effect`: 2 pass.
- Same features with `--test candidate_operation_source --test candidate_effect_annotation --test candidate_unit_source --test simple_sub_local_source_retirement --test candidate_lifecycle_retirement --test shadow_apply_candidate`: 41 pass.
- Same features with `--lib candidate_intrusion`: 5 pass.
- Same features with `--lib candidate_lifecycle_retirement`: 7 pass.
- `cargo check -p yu-solver --all-targets --all-features`: pass.
- `cargo check --workspace --all-features`: pass.
- `cargo check -p yu-solver`: pass.

An initial matrix command used three nonexistent target names; Cargo rejected
it before running tests. The corrected explicit target matrix is listed above.
The initial new oracle pilot had one false negative; the later repaired five-test
run supersedes it without weakening the asserted behavior. Historical graph
Call tests initially failed only their old EmptyEffect port expectation; final
replacement check is recorded at closure below. No warnings were observed.

## Genuine remaining requirements

This removes candidate source entry's early purity requirement; it does not
close a proof node. Whole-binding annotation publication and operation signatures
still require authentic provider entry-role transport. Omitted annotation effect
defaults are not globally changed, nor may roles be inferred from solved ports.
Native execution consumers, formal negative attachment/filter construction,
independent owned public schemes, default `yulang3` cutover and complete Call,
effect hygiene, soundness and principality remain open.

Formal-filter research commit `9d7967c3a` remains conditional. Independent review
found an omitted bound-insertion filter erasure; repair is active on its separate
research lease. Agreement of supplied transition models is not source hygiene.

## Final historical observer closure

`cargo test -p yu-solver --features shadow-f5,shadow-apply-candidate --lib candidate_graph_call`
(with the same primary command controls) passes both tests. Fresh conformance
delta review finds no findings. All remaining historical assertions and names
are unchanged. Total: 62 distinct focused tests pass, zero benchmark processes
or timing samples. Shared task, research queue, authority implementation status
and design index are synchronized for this bounded gate.
