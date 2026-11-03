# R310 native Replay ownership — frozen handoff r1

Sprint: `source-ei-formation-r310`, contract SHA-256
`796d0cd12c86bca625fd9aa4870650690ef5e14c744aea0126474294cf3a26eb`.
Baseline: `defcb6a9d`. Assignment/handoff ID: `R310-NATIVE`, revision 1.
Parent is the only Git integrator.

## Runtime, lease, and budget

Requested lane: `gpt-6-luna` / high per the fixed contract. Effective model,
effort, worker runtime ID, session, and launch receipt were not exposed to this
worker and remain UNKNOWN. Exact repository write leases: this file and
`crates/yu-solver/src/shadow_apply.rs`; exact scratch lease:
`/tmp/yulang-r310-native/`. No other paths were written. No Git operation or
child process was used. The focused offline Cargo work, including the initial
probe and final cached check, used under 180 seconds of the 1800-second bound.
Writes stop after this frozen revision.

## Outcome and parent/source/native correspondence

Outcome class: `source-native-evidence` with a test-only implementation
contribution. The new `#[cfg(test)]` regression starts from the same authentic
HIR parse/lowering and candidate solver execution for
`my id x = x; my answer = id (id 1)`. It walks the retained `LocalSource` for
`answer`, selects its actual outer Apply, actual Group argument, inner Apply,
and their actual callee source occurrences. It joins these exact occurrences to
the candidate's source Call records.

The test reads the complete same-context relation pairs and dependency records
from the retained effect-algebra `State`. For each Replay it checks both ordered
`BoundKey`s against retained pair membership. It respects
`BoundKey(owner, Positive, item)` as `item <: owner`, verifies the actual Call
callee's `TermView::LiveVariable` row is the positive Replay lower bound owner,
and matches the upper endpoint to that Call's exact negative-function demand
Term. The lower parent is then traced backwards through its own retained Replay
to the direct value-slot-0 drain for that Call's actual callee source occurrence
and a matching `FreshUse` admission. This recovered the previously omitted
source owners for both off-spine parents; a forward closure from the Call seed
alone did not contain them.

The same graph evidence connects the inner Call's retained
`FunctionPort(Result, Preserve)` child to its native result row, through the
argument Replay, to the direct source Group relation. The Group result then
joins the outer Call's actual `FunctionPort(Argument, Swap)` child in a retained
Replay. The outer source Call's argument `TermView` row matches that port pair.
The test rejects an absent/phantom parent, a mutated endpoint, swapping the two
source Calls, and deleting the Group edge. These checks use source occurrence,
Cause/Origin, full native Terms, typed pairs, ordered dependency inputs, and
bound admissions; they do not use `source_provider_observation`'s forward
reachable dependency list as backward ancestry.

This establishes one concrete source → generated constraints → candidate
propagation → typed native port path. It does not close the original EI / R159
proof, establish whole-language Call semantics, generalize the bridge, or
authorize production promotion. No production API, natural inference,
source domain, diagnostics, or semantic behavior changed. No Simple-sub bypass
was restored.

## Focused check and evidence

Final command (exit 0):

```text
CARGO_TARGET_DIR=/tmp/yulang-r310-native cargo test --locked --offline \
  -p yu-solver --features shadow-apply-candidate --lib \
  r310_nested_call_replay_has_source_owned_parents_and_group_path -- --nocapture

running 1 test
...r310_nested_call_replay_has_source_owned_parents_and_group_path ... ok
1 passed; 0 failed; 833 filtered out
```

Final log: `/tmp/yulang-r310-native/focused-final.log`, SHA-256
`342b11ceadade1c21750028cf3a21bbaba7dc55212712bc194d5065e5ed2639a`.
The first strengthened attempt failed because the observer selected a direct
effect-slot Origin instead of the exact value slot 0. That failure exposed the
need to key source ownership by the exact Cause slot; the corrected test now
selects slot 0 and passes. The initial compile also caught a private enum path
error, corrected before the final check. The first R309 forward-only checker
was rejected in its R2 handoff; no generic forward-reachability claim is reused
as ancestry here.

Direct dependency hashes at freeze:

- `crates/yu-solver/src/shadow_apply.rs`: SHA-256
  `7554db04c46281c579ef7f6267df85cc4ae83a505c81d79aaba5080a9c9bc00c`;
  baseline source before this packet was
  `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5`.
- `crates/yu-solver/src/candidate_context.rs`: `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`.
- `crates/yu-solver/src/candidate_call.rs`:
  `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f`.
- `crates/yu-solver/src/candidate_effect.rs`:
  `aeea54f55922cc6f15837a4533e63d21523ef88abfcd604b503b80cfd11bc20b`.
- `crates/yu-solver/src/candidate_source.rs`:
  `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`.
- `crates/yu-hir/src/module/local_source.rs`:
  `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1`.
- `crates/yu-solver/Cargo.toml`:
  `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`.
- `Cargo.lock`:
  `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`.

## Remaining premises and owner TODOs

- `R309-EI-OWNER` remains open with the proof/source owner: original typed EI
  operand construction and source-owned `q_c` registration must be supplied
  under authentic source scope; reconstructed operands or absent authoritative
  clause registration falsify it.
- `R309-NATIVE-LEAN-SERIALIZATION` remains open with the source/native bridge
  owner: provide a checked general export that preserves the actual native
  causes, Terms, typed FunctionPort direction, both Replay parents, their bound
  admissions/owners, source identity, and completeness. Falsify with lost
  polarity/parent/source identity, a truncated input accepted as complete, or
  an invented edge.

The local selected source owners are established only for this fixture. The
source Call → owner-parent reconstruction still needs independent review and a
general checked bridge before application to R159.

## Frozen artifact and hygiene

Artifact paths in this lease: `crates/yu-solver/src/shadow_apply.rs` and this
handoff only. Scratch outputs under `/tmp/yulang-r310-native/` include
`focused.log`, `focused1.log` through `focused4.log`, `focused-final.log`,
`probe.log`, `probe2.log`, Cargo target products, and intermediate build output;
all are disposable after primary review. The borrowed `/tmp/r309-result-flow/`
and `/tmp/yulang-r309-native/` evidence predates this assignment and was not
modified. Independent fresh review is pending. This handoff is not self-review,
theorem closure, or production approval.

## Revision 2 — independent-review causal certificate repair (2026-11-03)

This sequential revision follows Luna's acknowledged R1 review and repair
request. R1 bytes and its original artifact/log hashes remain preserved above.
The independent reviewer found that R1 only matched the `FreshUse` cause variant,
did not check its payload, did not compose Replay child pairs from both ordered
items, and did not actually rewire the source joins.

The R2 checker now authenticates each FreshUse route by exact callee occurrence
and retained context-use ID; finds the unique provider `FreshRoute` captured
bound with the same source relation and `source_bound`; checks its captured
`EvidenceSnapshot` is the exact imported antecedent; reconstructs the mapped
owner row and function item and checks that pair against the target bound; and
requires the matching `Dependency::Transport` child, parent, use-origin, from,
to, and FreshUse reason. It then calls the retained FreshUse admission/emission
checker with the full antecedent/source-bound/use-origin/mapped-relation/target
bound tuple. An admission variant or equal pair alone is insufficient.

For every selected Replay, R2 checks that both exact bound parents occur in
this `State` with their bound-derived typed pairs, share the same owner, use
positive lower and negative upper polarity, and produce the child pair from the
ordered lower/upper items. It validates all participating context IDs by
traversing their retained context payloads. Source fact and origin observations
must both be complete and include exact value slot 0; an explicit zero-row cap
is rejected as incomplete.

The test performs post-solve graph mutations and restores each dependency after
asserting rejection: FreshUse Transport parent to `RelationId(u32::MAX)`;
terminal Replay child to MAX; both Replay parents to MAX; inner-to-outer Call
Replay rewiring; removal of the Group Replay edge; and Result/Preserve and
Argument/Swap FunctionPort parents to MAX. It also calls the exact emission
checker with mutated antecedent, use-origin, and mapped-relation values and
requires failure. A direct invalid `ContextId(MAX)` traversal is rejected.

Mutation coverage boundary: the existing leased test hook can replace
`Dependency` records but cannot mutate a stored `BoundAdmissionCause` or every
relation's stored context ID. So this assignment does not claim an in-place
mutation of those two stored fields. Their mutated values are rejected through
the exact admission/emission and context-payload checks; Luna's independent
referee is rerunning its post-solve state mutations against the frozen R2
artifact. The subsequent R2 referee report rejected R2: five mutations
(FreshUse parents/payload and all contexts) were rejected, but a valid
different-snapshot antecedent substitution still passed all six FreshUse
admissions. The reviewer also found an unselected terminal-child mutation;
that branch was adjudicated outside this selected source chain's scope. R3
adds the exact captured-snapshot/admission-antecedent equality for the blocking
case.

R2 focused check (exit 0):

```text
CARGO_TARGET_DIR=/tmp/yulang-r310-native cargo test --locked --offline \
  -p yu-solver --features shadow-apply-candidate --lib \
  r310_nested_call_replay_has_source_owned_parents_and_group_path -- --nocapture

running 1 test
...r310_nested_call_replay_has_source_owned_parents_and_group_path ... ok
1 passed; 0 failed; 833 filtered out
```

R2 artifact `crates/yu-solver/src/shadow_apply.rs` SHA-256:
`ac141d23ccd24919462810a34433398989f92292eebf5da228a625ec72d3ba3d`.
R2 log `/tmp/yulang-r310-native/rev2-focused-final.log` SHA-256:
`e44a034702304a401d7ba0c7531bb5370b17afe5f9ee19da5c00bf17c352b7a4`.
`git diff --check` passes. Total observed Cargo work remains below 240 seconds
of the 1800-second bound. Requested/observed runtime fields remain as stated
in R1; no production behavior changed.

R2 disposable scratch also includes `rev2-focused1.log`, `rev2-focused2.log`,
and `rev2-focused-final.log`, plus the already listed R1 probes/logs and Cargo
target products under `/tmp/yulang-r310-native/`. Exact repository artifact
leases remain `crates/yu-solver/src/shadow_apply.rs` and this handoff only.

## Revision 3 — same-validator mutation checks and antecedent join (2026-11-03)

R2 independent review rejected the stored FreshUse admission when its
`antecedent` was changed to another valid imported snapshot: the R2 checker did
not join that field back to the snapshot selected by the exact captured source
bound. R3 adds the direct equality
`imported_snapshot == admission.antecedent` before checking the retained
FreshUse emission. The independently reported terminal Replay child mutation
that targeted an unselected child was not a scoped failure; R3 mutates the
selected inner Call Replay child used by this source chain.

R3 factors the complete source-to-native-chain check into one test-local
validator. The positive graph must pass it first. Each actual retained graph
mutation is then applied, the same validator must panic/reject, the original
edge is restored, and the same validator must pass again. This now covers the
FreshUse Transport parent, selected inner Call Replay child and both Replay
parents, inner-to-outer Call rewire, actual Group edge removal, Result/Preserve
parent, and Argument/Swap parent. The focused run passed; expected caught
validator panics are printed because the command uses `--nocapture`.

The retained context checks establish only that each selected relation's
context ID resolves and its payload traverses successfully. They do not prove
context equality or context composition between child and parents. The
test-hook lease still cannot mutate a stored `BoundAdmissionCause` or rewrite
every stored relation context in place. The explicit antecedent equality now
rejects the R2 valid-snapshot substitution by construction, but the separate
post-solve state-mutant remains for the referee to rerun against this frozen
revision. No claim is made that the R2 reviewer has accepted R3.

R3 focused check (exit 0):

```text
CARGO_TARGET_DIR=/tmp/yulang-r310-native cargo test --locked --offline \
  -p yu-solver --features shadow-apply-candidate --lib \
  r310_nested_call_replay_has_source_owned_parents_and_group_path -- --nocapture

running 1 test
...r310_nested_call_replay_has_source_owned_parents_and_group_path ... ok
1 passed; 0 failed; 833 filtered out
```

The focused test emitted existing crate warnings; no new test-local unused
evidence bindings remain. The exact output log is
`/tmp/yulang-r310-native/rev3-focused-final.log`. SHA-256 values at R3 freeze:

- `crates/yu-solver/src/shadow_apply.rs`: `2dc12b5a9ec6f11a062b3257c5f3eb04be9686ae306de7ebaab0f1de5cdd5717`.
- This handoff: its final digest is sent with the freeze receipt to Luna.
- Focused log: `403e9859885bf0845021d3ed93366dff481de9ba263b82325f49325397b24e89`.

R3 adds no path beyond the existing source and handoff leases. Scratch outputs
remain under `/tmp/yulang-r310-native/`, including Cargo target products and
the named R1/R2/R3 logs. The result remains one fixture-level source/native
evidence contribution, not proof closure, general Call semantics, or production
approval. Requested model/effort remains Luna/high; observed runtime/model
identity remains UNKNOWN.
