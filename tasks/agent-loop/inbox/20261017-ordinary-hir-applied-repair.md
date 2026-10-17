# Ordinary HIR applied-conformance repair: implementation handoff

- Sprint `ordinary-hir-applied-conformance-repair-20261017`, rev7, SHA-256
  `5572d93a543c49780c1275fea3a4450695f2c997e3944e18f5ba8f67194f5960`.
  Handoff revision 22 (Luna's HIR recovery rerun); failed candidate
  baseline `4f4dcb7b9`; original theorem
  conditions closed: 0. Parent claims, quantifiers, source domain, and
  source/native correspondence remain unchanged and OPEN.
- Adopted grammar rev4 SHA-256
  `2e61e2acb1a8981bb78592accc48207a24a5cc4c75278e100f63eb960acfeea3`; adopted
  resource correction SHA-256
  `e8b53a773675ba54f0cb5dcc4d62a993e8dd16954e0c92c58fdfc80c620d411e`.
  Plan SHA-256 `45c4cebfc6b5f35cf2f081db61959558721757f6a3a3f802ae310181f5ea4dc3`,
  invariants SHA-256 `1f3afae18e36ca0abf5a9be1fbf2d1220fad0836a0cce3c370e6cce15a027a28`,
  architect CLEAN receipt SHA-256
  `635cd68b611d652f4d6760026888945518423b8be69729560418807d9fbbc339`.
- Role: implementation lane `/root/ordinary_hir_application_implementation`,
  current session. Requested `gpt-6-luna`/high; observed model/effort UNKNOWN.
  No descendants. Active work estimated ~950s of 1110s; writes STOPPED at this
  receipt. Luna remains sole integrator.

## Outcome and source correspondence

Candidate implementation repairs the seven applied findings. `lib.rs` now
carries `AssociationProvenance` with the existing `HirExpr` from the same
`ChainParser` constructors: `value`, nested collection, and structural
continuation retain the actual owned `SyntaxNode`; continuation child zero
remains the prior left expression. Public `HirExpr` is unchanged. Ordinary
admission consumes this paired product, verifies shape agreement, and fetches
keys only from the exact source-node map. Kind/range lookup and the second CST
association walk are removed.

Preflight preserves refusal/recovery gates and borrowed causal errors, rejects
comma/separator punctuation on the actual direct CallTail/Group node before
resolving operands, and stages atom events in source preorder. `lower_plan`
emits duplicate-definition first, then assigns dense final IDs to staged
operand errors at the existing semantic-error seam. Pending admission stores
its checked owning item index; finalization validates that slot/root and visits
it once, then recomputes `evaluation_class` from the replaced final value.
Identity stage and module remain unpublished on any failure.

Apply descendant errors are written in callee-then-argument order into one
exact-sized, fallibly allocated boxed list per Apply; Group forwards by walking
only its Group chain and does not materialize an error list. Counts/bytes,
child sizes, item index conversions and occurrence ordinals are checked.
Association provenance/child vectors reserve fallibly; Apply operand slices and
error slices use exact fallible global allocations. Existing unrelated parser,
carrier, module/container and spelling allocations were not relabeled as
fallible. Known unchanged association allocations still include operator power
`to_vec`, operator/token spelling `to_owned`, and public whole-file chain
collection; existing recursive parser/Box depth is not a universal termination
claim.

The vertical remains ordinary `lower_module` plus the existing feature-gated
`CandidateInference` observations. It does not establish standard inference:
`ConstraintBatch::collect`/`collect_mode` remains the first open standard
consumer and still rejects Apply/Group. No semantic Call, source T/native
adequacy, F1/FK1, N-Transport, soundness, principality, termination, or parent
theorem result is claimed.

## Authored falsifiers and resource counts

Regression sources cover causal recovery/refusal without child diagnostics;
comma-bearing CallTail and Group refusal; duplicate-before-operand event order
and final dense IDs; final classes for atom, Apply, Group and Lambda bodies;
exact parse-owned Group/ML/CallTail and distinct repeated-text callee/argument
keys; 64 simple bindings with a counter asserting exactly 64 indexed owning-item
visits; and grouped unresolved diagnostics with ordered IDs and exact keys.
Identity-root collision coverage is retained. These assertions are authored,
not run.

For the ordinary unresolved left spine at `m=2`: `V=5` (three atoms, two
Apply), `E=3`, `R=5`, final reference storage `20` bytes (`5*sizeof(HirErrorId)`),
and two actual nonempty Apply-list allocations. Clean same shape has `V=5`,
`E=0`, `R=0`, zero stored bytes and zero nonempty list allocations. Two Group
wrappers around the unresolved spine add two V, keep `E=3`, `R=5`, 20 final
bytes and exactly two list allocations. The 64-binding counter is source-level
test instrumentation and has not been executed.

## Paths, hashes and checks

Changed authored paths:

```text
crates/yu-hir/src/lib.rs a50d7b70c76906e009c0a7f7ae74c29f485d6e65365e0f29c2c7e0dc8b481cee
crates/yu-hir/src/module.rs 60e91c9a51394b04af42b3ec7c284062b34fcd9faa4ea79c35b4ae58aaf460ed
crates/yu-hir/tests/ordinary_application_admission.rs dd6c2ac5f5e8b50e37637a84e3f7427a1f628cd0f8edcaa2803775ab702ba972
```

Other leased paths are unchanged at the frozen input pins:
`source_identity.rs` `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3`;
`shadow.rs` `460c813cb0d2e21565df011b1d816abbc2b180cef13797a1b7b453e9ee413f66`;
`research_accepted_call_vertical.rs` `9c3dea05d11c49bae09520d5f6fe27430f1706185232daf2cf8e8d801a42d71a`.
The handoff is an exact leased path. Luna concurrently modified
`tasks/agent-loop/current.json`; this worker did not edit it. No
scratch/generated paths were created.

After author STOP, Luna ran `git diff --check` successfully (exit 0). No Cargo,
tests, build, compiler/format probe or execution probe was run; those remain
held for sequential independent applied reviews and regression pre-run
clearance. Static source inspection only; the producer cannot self-certify.
The fresh compiler review is recorded in
`notes/progress/2026-10-17-ordinary-hir-repair-applied-compiler-review.md`, SHA
`2395d3ca4abd65b5c4a530f691cef5cb0b4688e8ec91913b255c48625b117191`. It
identified one MINOR: `module.rs` merged `append_stage` before validating
owning item index/kind/root and checked counter arithmetic. The narrow repair
is now applied. In frozen `module.rs` SHA-256
`60e91c9a51394b04af42b3ec7c284062b34fcd9faa4ea79c35b4ae58aaf460ed`, the
saved item index, binding kind, exact empty-error placeholder/root and checked
visit-count successor are validated before `append_stage`; replacement after
merge has no fallible validation or arithmetic. The implementer stopped after
about 24s of the 30s cap. Post-STOP `git diff --check` passed. No tests, builds
or probes ran. Fresh independent compiler delta review STOPPED CLEAN; receipt
`notes/progress/2026-10-17-ordinary-hir-repair-compiler-delta-review.md`, SHA
`7976bdab264e72ce197cf923e0a0cabfac3f1b1646e38e04402b9429973824f8`. It found
no BLOCKING, major or minor issue and confirmed the prior seven fixes remain.
Repair and delta-review charges are 24s and 30s from reserve120, leaving 66s
reserve. No other code/test path is reopened.

Fresh spec review STOPPED with one MAJOR execution-coverage gap, not a code/spec
conflict: the two integration-target Cargo commands do not execute module.rs
unit falsifiers for conflicting roots, final private classification, or the
64-binding indexed-finalization count. Receipt:
`notes/progress/2026-10-17-ordinary-hir-repair-spec-review.md`, SHA-256
`155ecb301e885aa3faf7c8a1296f6fe0e354f4aed8667b6d3286d8aa7913ad7f`. Luna
adjudicated this as an internal execution-scope correction. Sprint rev5 adds
exactly one focused command,
`cargo test -p yu-hir --features shadow --lib module::tests::`, with a 45s cap;
the two original integration commands remain unchanged and exact-once. The
final architect review is CLEAN: receipt
`notes/progress/2026-10-17-ordinary-hir-repair-final-architect-review.md`. It
confirmed the three-test filter, all pins, atomic finalization, and exact budget
`180+240+285+6=711`; actual test discovery/run remains pending. Fresh pre-run regression review STOPPED CLEAN; receipt
`notes/progress/2026-10-17-ordinary-hir-repair-regression-prerun-review.md`.
It verified all pins, the 8-test unit filter (including the three falsifiers),
nine HIR integration tests, and one gated solver vertical without any execution
claim. It preserved the standard consumer boundary and no-expectation-change
rule. Runtime discovery/results remain pending; post-run review is mandatory.
The rev5 resource table charges each command cap explicitly: 285s total for
unit45+integration120+integration120, leaving final architect180, regression240
and reserve6 within 711s. Cargo.lock and root/member manifests are frozen by
the rev5 hash pins. Timeout,
compile failure, zero named falsifiers, or any assertion failure stops with no
retry/filter substitution. Assertions are authored but no tests have run. Parent
theorem gates remain OPEN.

The focused unit command was then run exactly once and failed before test
discovery with E0308 in a `lib.rs` unit-test match (`AssociatedExpr` matched
as `HirExpr::Error`). Receipt `notes/progress/2026-10-17-ordinary-hir-repair-unit-run-failure.md`. Per rev5, execution stopped immediately: neither integration command ran; no retry or edit occurred. No named falsifier executed. Selector approved a rev6 test-only repair: change the assertion match to `expression.hir`, preserving its expected error shape; exact code lease `crates/yu-hir/src/lib.rs` plus this handoff, cap30s. Then fresh compiler delta review cap30s. One post-repair unit invocation is explicitly authorized only after CLEAN; integration caps are90s each. No further retry follows. All theorem gates remain OPEN.
Post-run regression review remains required. Proof/source TODO
`HIR-APP-PARENT-1` remains with the standard solver/source/native owners; first
missing consumer is
`ConstraintBatch::collect`/`collect_mode`. Worker STOPPED, no unresolved child
leases.

## Rev6 focused-unit compile repair — handoff revision 14

Assignment `/root/ordinary_hir_unit_test_match_repair`; requested model/effort
`gpt-6-luna`/high, observed model/effort UNKNOWN. Exact leased paths only:
`crates/yu-hir/src/lib.rs` and this handoff. The single test-only edit changes
the `direct_structured_invalid_item_retains_its_nested_recovery` assertion to
match `expression.hir` (the `AssociatedExpr` payload). Its expected outer
`HirExpr::Error { kind: SyntaxKind::Invalid, ... }`, nested
`HirExpr::Error { kind: SyntaxKind::Missing, children: [] }`, cursor assertion,
and all other behavior remain unchanged.

The first focused unit invocation's E0308 is addressed at its source. No tests,
builds, Cargo commands, compiler/probes, formatter, Git, network access, or
descendants were used by this author. No scratch/generated paths were created.
Source SHA-256 is `cf0a2d537df793986509175fbde2785731ac28f4bc3f2024f4f0fbca2127c5ed`;
the final handoff SHA-256 is supplied in the frozen worker message. Writes
STOPPED; fresh independent compiler delta review of this exact edit is required
before Luna may use the single post-repair unit invocation.


## Rev6 compiler delta adjudication — handoff revision 15

Fresh compiler delta review STOPPED CLEAN; receipt
`notes/progress/2026-10-17-ordinary-hir-unit-compile-repair-delta-review.md`.
The only edit changes the test match to `expression.hir`; expected Invalid/Missing
error shape and cursor assertion are unchanged. Exact pins match. No tests ran.
Luna adjudicates CLEAN. The single post-repair focused unit command is now
authorized once (45s cap); HIR and solver integration commands remain gated on
its success and discovery of all three named falsifiers. No further unit run or
implicit retry is authorized.


## Rev6 focused-unit execution — handoff revision 16

After the fresh CLEAN compiler delta review, Luna ran the single authorized
post-repair command once: `cargo test -p yu-hir --features shadow --lib
module::tests::`. Exit0 in 4.30s: 8 passed, 0 failed, 0 ignored, 122 filtered.
The required root-collision, final-classification and 64-item indexed-finalization
falsifiers all ran and passed. Five additional module tests passed. Warnings were
limited to unread Token/Synthetic provenance payloads and unused
`replace_admission_root`; no warning was promoted to error. Full receipt:
`notes/progress/2026-10-17-ordinary-hir-repair-unit-run.md`.

The one amended unit invocation is consumed; no further HIR unit run is allowed.
Rev6 now authorizes the first integration target once (<=90s); on success, the
solver vertical once (<=90s), then independent post-run regression review
(<=90s). Any failure/timeout stops later commands. Parent theorem gates remain
OPEN; original conditions closed: 0.


## Rev6 HIR integration result — handoff revision 17

After the focused module unit filter passed8/8, Luna ran the HIR integration
target once: `cargo test -p yu-hir --features shadow --test
ordinary_application_admission`. Exit101 after2.315s: 8 passed, 1 failed.
`unsupported_and_recovery_bodies_keep_the_whole_body_refusal` failed at
`ordinary_application_admission.rs:326`: `recovered.errors()` did not contain
`UnsupportedExpression`. Full receipt:
`notes/progress/2026-10-17-ordinary-hir-repair-hir-integration-failure.md`.

Rev6 stops the sequence on assertion failure. Solver vertical was not run; no
retry or expectation change occurred. A fresh independent post-run regression
review is next and will adjudicate this exact failure against the adopted
refusal/recovery contract. All parent theorem gates remain OPEN; original
conditions closed: 0.


## Rev7 recovery expectation review route — handoff revision 18

The independent post-run regression review is frozen at
`notes/progress/2026-10-17-ordinary-hir-repair-hir-failure-review.md`, SHA
`c9ea17dc6570f3cb2ffe9b7f871534c17c956dc80372e00f602fb5346b57a22a`. It found
that `has_recovery` returns existing causal Error before UnsupportedExpression
fallback, matching adopted §§3–4; the test's module-wide unsupported assertion
failed and its inherited-kind assertion did not run. This is not yet an approved
expectation edit. Fresh spec adjudication (40s) compares §2's broader wording
against §§3–4 and must state exact binding-specific expected records. If CLEAN
on this scoped reading, a test-only edit may replace the inconsistent module-wide
check with causal-ID/attachment/kind checks on `broken`, preserving no Apply,
nonempty exact causes and no hidden unresolved operand. Delta review (30s) must
be CLEAN before one HIR integration rerun (45s); solver integration (45s) only
on HIR PASS; post-run review cap30s. Budget after the charged coordination is
220s exactly. No source behavior or expectations changed yet; no solver command
ran. Original theorem conditions remain OPEN.


## Rev7 spec adjudication — handoff revision 19

Fresh spec review confirms the line326 module-wide `UnsupportedExpression`
expectation is inconsistent with adopted recovery semantics, not evidence for a
production source change. `has_recovery` preserves each binding's causal
`ResolvedExpr::Error` before structural projection. Exact adjudication receipt:
`notes/progress/2026-10-17-ordinary-hir-recovery-expectation-spec-review.md`. For
`broken`, every Error ID must resolve to an inherited recovery record attached
to `Value(broken.id())`; its ordered IDs must equal that binding's complete
inherited causal records with no loss/duplication/substitution. Preserve no-Apply,
nonempty causal IDs, and no-UnresolvedName; remove only the contradictory
module-wide synthetic UnsupportedExpression expectation and make the inherited
kind check execute on `broken`'s own IDs.

Luna grants the conditional rev7 writer lease only for
`crates/yu-hir/tests/ordinary_application_admission.rs` and this handoff, cap30s.
No source or other test changes. Fresh regression delta review <=30s is required
before one HIR integration rerun <=45s. On PASS, run held solver vertical once
<=45s; then fresh post-run review <=30s. Any failure or cap ends this candidate
partial; no retry.

## Rev7 test-only recovery expectation repair — handoff revision 20

Assignment `/root/ordinary_hir_recovery_expectation_repair`; requested model/effort
`gpt-6-luna`/high, observed model/effort UNKNOWN; cap30s. Exact leased paths only:
`crates/yu-hir/tests/ordinary_application_admission.rs` and this handoff.
Removed only the contradictory module-wide `UnsupportedExpression` assertion
from the recovery-bearing `broken` case. The test now resolves every causal ID
from `broken.value()` to an authoritative module error, checks every record is
an inherited recovery kind attached to `Value(broken.id())`, and checks the
ordered IDs equal the complete inherited record sequence attached to that
binding. This equality also rejects missing, duplicated, substituted, or extra
records. Existing no-Apply, nonempty-causal-ID, and no-UnresolvedName assertions
remain. The inherited-kind check now executes on `broken`'s own causal IDs.

No production source or other test path changed. No tests, builds, Cargo,
probes, formatter, Git, network, descendants, or scratch/generated paths were
used. Writes STOPPED. Fresh regression delta review <=30s is required before the
single HIR integration invocation <=45s; the solver vertical remains gated on
HIR PASS. This is test expectation evidence only and closes no parent theorem
condition.

## Rev7 recovery expectation delta review — handoff revision 21

Fresh independent regression delta review is CLEAN. Receipt:
`notes/progress/2026-10-17-ordinary-hir-recovery-expectation-delta-review.md`.
It confirms the exact ordered causal-ID relation is checked against inherited
records attached to `Value(broken.id())`, and the no-Apply, nonempty-ID,
no-UnresolvedName, and unsupported-sibling assertions remain. No source, API,
or diagnostic behavior changed. HIR integration is now authorized exactly once
with a 45s cap. Run the held solver vertical exactly once only if HIR passes;
then obtain the required post-run review. Any failure or timeout stops the
sequence without retry. All original theorem conditions remain OPEN.

## Rev7 HIR integration rerun — handoff revision 22

The post-review HIR command ran exactly once and passed: exit0 in 1.444s,
9 passed, 0 failed. The repaired recovery/refusal test executed successfully;
all eight sibling tests passed. Three existing dead-code warnings remain and
did not affect compilation or execution. Exact receipt:
`notes/progress/2026-10-17-ordinary-hir-recovery-expectation-rerun.md`.
The held solver vertical is now authorized exactly once with a 45s cap; on
completion, obtain the required post-run review. Original theorem conditions
remain OPEN; HIR candidate regression evidence closes none.
