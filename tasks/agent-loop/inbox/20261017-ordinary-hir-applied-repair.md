# Ordinary HIR applied-conformance repair: implementation handoff

- Sprint `ordinary-hir-applied-conformance-repair-20261017`, rev5, SHA-256
  `5c63c3829cd6275523b1799e0286837518e9fd7dd0213c13f3171d9d7b7a6125`.
  Handoff revision 9 (Luna's post-coverage-amendment reconciliation); failed candidate
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
the two original integration commands remain unchanged and exact-once. A fresh
architect and pre-run regression review must clear the three-command map.
The rev5 resource table charges each command cap explicitly: 285s total for
unit45+integration120+integration120, leaving final architect180, regression240
and reserve6 within 711s. Cargo.lock and root/member manifests are frozen by
the rev5 hash pins. Timeout,
compile failure, zero named falsifiers, or any assertion failure stops with no
retry/filter substitution. Assertions are authored but no tests have run. Parent
theorem gates remain OPEN.

Next owner: Luna runs the final architect review, then pre-run regression
clearance; only then the focused unit command followed by the two original
integration commands, sequentially. Post-run regression review remains required. Proof/source TODO
`HIR-APP-PARENT-1` remains with the standard solver/source/native owners; first
missing consumer is
`ConstraintBatch::collect`/`collect_mode`. Worker STOPPED, no unresolved child
leases.
