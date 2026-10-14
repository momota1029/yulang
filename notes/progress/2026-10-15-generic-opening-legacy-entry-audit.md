# Generic operation-arm opening: direct and legacy entry audit

Date: 2026-10-15
Status: frozen, unreviewed research-only source characterization
Role/method: researcher; static caller/entrypoint correspondence
Baseline: `research/simple-sub-intrusion`, `427d1ff5daab866fa7d89cb513a077063cc6454d`
Exclusive write lease: this file only
Authority: redesign charter §§19–20; operation-instance binding package
§§2–4,7–9; top-level inference principles §§1–4. The operation package is
Draft and supplies no implementation authorization. Preserve the selected
`sink::put` rejection and the joint A/B/J/profiles/K,D request package.

## Result and claim boundary

There is a concrete **private collection/session route without source
preflight** into `candidate_catch_operation`. Existing unit-test consumers use
that route. Its constructor can materialize an operation-local signature
variable as an ordinary flexible value row; it does not implement the selected
rigid opening or establish correspondence to the operation-use witness.
Therefore the earlier audit's preflight-based exclusion must retain its explicit
`CandidateInference::solve` hypothesis. It is not an all-internal-path exclusion.

This is static reachability and constructor characterization, not executed
generic-handler acceptance or a source-qualified counterexample to §§19–20.
No generic fixture was run through the alternate route. The constructor's lack
of a monomorphic guard is not evidence that the complete private solve succeeds,
nor that this route is externally available in production.

## Direct owners and entry inventory

Line locators below refer exclusively to the pinned baseline, not the historical
baseline recorded inside the starting audit.

| Route/owner | Actual gate and consumer | Classification and limit |
|---|---|---|
| `shadow_apply.rs:191–225`, `CandidateInference::solve` | Source preflight at 204; collection with `(true,true)` at 222; private candidate session and `run_candidate` | Public candidate API behind `shadow-apply-candidate`. Preflight excludes local value/effect signature variables, and also requires resolution, one payload, Function shape, no outer signature computation row, and supported used-field variance. This row is a dependency on the previous audit, not a new all-path result. |
| `lib.rs:898–915`, `ConstraintBatch::collect` | `(false,false)` through `collect_mode`; `SolvedModule::solve` at 17691 starts ordinary `try_new`, then `run` | Public production solver route. It does not enter the LocalSource candidate emitter, graph startup, or operation-arm constructor. Monomorphic-signature preflight is not its gate. Its closed-body collection at 1028–1088 marks unsupported/error bodies separately; this is not proper uniform generic-arm checking. |
| `lib.rs:17696–17701`, `SolvedModule::solve_with_shadow_fresh_capture` | Same ordinary private startup, adding optional retained current-solver row evidence | Public legacy shadow evidence route. It does not start the candidate graph or change the supplied public collection flags. No generic arm opening follows from fresh-capture evidence. |
| `shadow_apply.rs:631–677`, `CandidateValueObservation::solve` | Legacy local/expression preflight; `collect_mode(hir,true)` fixes graph effects to false | Public value-shadow route. It uses legacy `ResolvedExpr`/shadow-local emission, not LocalSource operation/catch actions. `preflight_expression:907–975` rejects unsupported expression forms; `emit_candidate_expression:1390–1401` likewise rejects its remaining unsupported forms. |
| `lib.rs:910–915,1133–1145`, private `collect_candidate_mode(hir,true,true)` | Obtains actual `hir.local_source(root)` and directly calls `emit_candidate_source`; **no call to source preflight** | Genuine private alternate entry. The method and batch fields are private, so this flag choice is not exposed by `ConstraintBatch::collect`. Existing actual users are private/unit-test consumers plus the preflighted public candidate wrapper. |
| `lib.rs:10157–10161`, private `try_new_candidate` | Asserts graph-effects mode, calls `try_new`, then `start_candidate_graph` | No signature/preflight check here. Test helpers also call `try_new` followed by explicit graph startup, e.g. `candidate_effect.rs:1833–1838`. |
| `lib.rs:10359–10393`; `candidate_scheme.rs:906–910`; `candidate_source.rs:777–808,817–907` | `execute` drives loose actions and SCC roots; root schedules call `begin_candidate_source`, `drive_candidate_source`, then `execute_candidate_action` | Actual operation-arm consumer path, not an unused helper chain. Source schedules remain private; no admission check is added by this driver. |
| `candidate_source.rs:721–742`, `candidate_legacy_actions` | Emits only Candidate, Lambda, Module and Fact actions from legacy recipes | This fallback has no CatchOperation producer. It is used when source is absent, so it cannot independently reconstruct the selected arm package. |

`git grep` over committed `crates`, `lib`, and `tools` found exactly the
`candidate_catch_operation` definition and its one direct call,
`candidate_source.rs:901`. The latter consumes `Action::CatchOperation`.
The only named CatchOperation construction found in that search is
`candidate_source.rs:456`, under `Work::CatchArms`. These helpers are reachable;
they are not correctly classified as dead merely because the generic public
wrapper preflights them away. No direct unit-test call to
`candidate_catch_operation` was found in this bounded inventory.

The signature materializers are private to `candidate_effect.rs`.
`candidate_signature_value` has external-to-self calls from operation use
(799), catch arm (824–825,831–832), local annotation (1217,1222), and the
annotation pair (1308,1318), plus recursive Function-child calls (1478,1481).
`candidate_signature_effect` has calls from formal effect ports (1131–1132),
annotation computation effects (1404), and Function-child signature
materialization (1484,1498). Annotation/formal contexts have their own scope
and row restrictions; they do not become operation-arm elimination merely
because they share a materializer. In particular, `monomorphic_signature` is
not a universal materialization gate.

## Derivation of the private alternate path

Explicit premises:

1. Build with `shadow-apply-candidate`, inside the solver crate's private scope.
2. Supply an authentic LocalSource binding with a resolved Function operation
   signature and one valid payload pattern, and valid source identities.
3. Use `collect_candidate_mode(hir,true,true)` directly, then initialize the
   candidate graph and drive that root's source schedule.
4. All earlier required allocations, identities and solver actions complete;
   this static argument is conditional on reaching the identified action.

Then `lib.rs:1133–1145` calls `emit_candidate_source` without preflight.
Its entry at `candidate_source.rs:246` retains source and allocates positions;
`Work::CatchArms:425–460` retains lexical payload/continuation positions,
prepares primitives, and appends CatchOperation. It visits the actual body
after installing binders. The schedule is installed and marked active at
710–714. SCC execution reaches the action dispatcher at 901 and calls
`candidate_catch_operation`.

The actual unit-test route is exhibited by
`shadow_apply.rs:1697–1700`: private collection, candidate startup and
`session.execute()`. A second private consumer at 1720–1740 executes a source
call schedule. These tests concern other source constructs, so they establish
an existing consumer route, not observed execution of a generic catch.

At `candidate_effect.rs:806–866`, the constructor checks the outer value is
a Function and uses a **new arm-local map** for A and B. It neither calls
`monomorphic_signature` nor receives the operation-use map. For a used payload,
both polar A ports materialize through that map (824–825); for a used
continuation, both B ports do likewise (831–832). A signature Variable in an
Operation context uses or allocates `fresh_value_at_level(level)` at
1451–1465. Ordinary allocation at `lib.rs:10175–10196` records Fresh origin
and `non_generic:false`; the inspected constructor supplies no rigid-opening
certificate or permission restriction. Nested effect variables similarly use
a fresh flexible effect row at `candidate_effect.rs:1582–1593`; variance and
row-cardinality restrictions still apply at 1575–1580.

This provides shared A/B row identity **within the arm**. It does not identify
that map with the separately allocated operation-use map at 785–805. The
constructor receives the original scrutinee endpoint/effect, declaration,
owner and occurrence; it does not receive a retained request-local substitution
or packet certificate. The raw continuation returns the original scrutinee
value and a provisional conservative full-S effect bound (833–859), with
fresh entry/return effect rows. This is not evidence of exact dependent J,
joint K,D disposition, or a uniform rigid opening whose proof can be specialized
at the original use witness. Allocated row identity may preserve graph sharing;
dropping the scratch maps alone does not prove sharing loss.

Arm-body constraints have a real independent owner: ordinary Apply creates
the candidate relation at `candidate_source.rs:606` onward, using the lexical
CatchBinder endpoints installed above. Catch result/effect consumers at
525–531 connect each actual body endpoint/effect to the catch output. Body
annotation actions use their ordinary scoped annotation constructors. There
is no second monomorphic gate at action dispatch. Whether solving these
constraints accepts a particular generic source is outside this static pass.

## Smallest discriminating source seam

Reuse the existing committed fixture at
`crates/yu-solver/tests/candidate_operation_catch.rs:74–85`:

```yulang
act echo:
    our send: 'a -> 'a
my result = catch echo::send 1 { echo::send(x), k -> k x, v -> v }
```

Its public candidate assertion expects Unsupported and was read, not run.
The private path above offers a discriminating construction experiment for a
separately authorized future packet: preserve the same HIR and inspect the
CatchOperation-generated rows and body constraints without public preflight.
Do not interpret private success as generic semantic conformance. In particular,
`sink::put` with `checked:int=x` remains rejected by source authority even if
flexible private materialization can satisfy a caller-specific constraint.
Neither fixture acceptance nor a minimized sink counterexample was established
here.

## Coverage, independence and resource limits

This is source/artifact evidence. The oracle is committed constructor and
consumer code, compared against separately supplied selected semantics; there
is no checker that assumes those rules. The authority premises are shared with
the proof lane, so this is complementary production correspondence, not an
independent review of its constructive theorem. No synthetic transition rules,
mutations, seeds, random ranges, executable oracle or measurement samples were
used.

Commands used: `git rev-parse HEAD`, `git branch --show-current`, pinned
`git show 427d1ff5d:<path>` with `sed`/`rg` locators, and bounded `git grep -n`
for constructor/action/entrypoint names. Searches covered committed `crates`,
`lib`, `tools`; external-caller search additionally covered tracked paths while
excluding notes/tasks/questions/rules/tools and the solver test trees.
Broad locator outputs were sometimes capped with `head`; those capped inventories
are not exhaustive absence evidence. The decisive constructor/action searches
and named entry bodies were inspected directly. An attempted read of
`crates/yu-solver/src/candidate_value.rs` failed because that path does not exist
at the baseline; emission owners were then located in `shadow_apply.rs`.

Read owning paths: solver lib.rs, candidate_source.rs, candidate_effect.rs,
candidate_scheme.rs, shadow_apply.rs; HIR module.rs, module/local_source.rs,
shadow.rs; the operation-catch fixture and the starting audit. Governing sections
were read from pinned design bytes. No full compiler traversal, arbitrary source
parser run, imported-family audit, F5 metatheory, rollback/replay closure,
generic generalization/lifecycle, exact Call/hygiene proof or dynamic consumer
experiment was performed. Zero Cargo/build/test/probe/measurement processes;
one static leaf within its 15-minute allocation, stopped after the first concrete
private alternate construction/consumer route. Peak CPU/RAM and exact elapsed
time were not measured. Hash/integrity Python commands are bookkeeping only.

The initial HEAD matched the baseline. Before writing, HEAD had moved to
`b2c10cfe3413661759a4a7d18e57504a73e2e508`; all listed compiler and design
dependencies still matched pinned bytes. The starting audit changed at current
HEAD to SHA-256 `773e4166f202e38e8f131201425257202db363548b98cac8be704c8594546e1d`;
only its pinned older bytes were interpreted here. No dependency was edited
by this leaf. This file is frozen before submission and has no independent review.

Recommended next action: hand the private CatchOperation construction seam to
the main proof/source coordinator to account for its flexible arm map versus
the required rigid/request-linked opening. Keep the parent generic opening,
source correspondence and implementation gates OPEN; a runtime discriminator
requires a separately authorized packet.

## Frozen dependency hashes (SHA-256 at the baseline)

```text
a261db48f0986ed2f03a26a6506e5179793bc992708f8e26c90a2aa383c6e492 notes/progress/2026-10-15-generic-opening-source-audit.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed notes/design/2026-09-29-scc-intrusion-redesign-charter.md
1eb2cbdb49368b0839d839d6a5e72698bb06252813b00200098e70371645c7c9 notes/design/2026-10-02-operation-instance-binding-package.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81 notes/design/2026-10-11-yulang-inference-top-level-principles.md
e902da1c9a7f0fb4dcd806c87563d1ae46d35bbb999e69b7fee51c3c0f6e4bf5 crates/yu-solver/src/lib.rs
3a1ad7155d784c1ff0234dc7815f0d49618bff307a6564c0646cf8e510a248c4 crates/yu-solver/src/candidate_source.rs
f414efa7efdb17644f4dfa6b0bba621c1bb7cccd0f83735c33a0acb875da6b91 crates/yu-solver/src/candidate_effect.rs
c8ef7cc472f0dcb60d793c6f9b4f6ba1aefb76f919ff2a3ce9310f85eb647dcd crates/yu-solver/src/candidate_scheme.rs
3db7eb04045391ceb939612226ea87e7bac6c035f3c2d4c210a8d3d4fd641831 crates/yu-solver/src/shadow_apply.rs
2fd2114389a595721c0b7631b5fdf602ccfbc024df7db144649eae05f681f133 crates/yu-hir/src/module.rs
afc91346af535529f973421bdbe2a43520c98946097cae545e4ae1a665146074 crates/yu-hir/src/module/local_source.rs
f38a77eb827fbc69560184eb192009a37c16595705472ee617b96ec0e31c5fd6 crates/yu-hir/src/shadow.rs
8c580da56de25c76146073919840f6d15dec3b11a53c0787309a082dc59e5484 crates/yu-solver/tests/candidate_operation_catch.rs
```

## Commit packet

- Exact leased path: `notes/progress/2026-10-15-generic-opening-legacy-entry-audit.md`.
- Baseline: `427d1ff5daab866fa7d89cb513a077063cc6454d`.
- Dependency changes by this worker: none. Concurrent seed-audit hash change
  is recorded above; compiler/design dependencies matched the pinned baseline.
- Claim/review status: bounded static characterization; frozen; unreviewed;
  no theorem closure, source acceptance result or implementation authority.
- Checks already run: pinned caller/entrypoint and constructor inspection,
  thirteen dependency SHA-256/equality checks, branch/baseline recheck, artifact
  whitespace/fence/final-newline integrity. No builds/tests/probes/measurements.
- Proposed checkpoint message: `research: map generic operation-arm private and legacy entries`.
- Shared deltas intentionally left to primary/curator: link this private bypass
  seam from `tasks/current.md`, `tasks/research-lab.md` and the relevant theory
  correspondence record; retain the original public-preflight hypothesis and
  all parent OPEN statuses. No shared records, authority, questions, compiler
  files or Git state were modified by this worker.
