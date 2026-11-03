# R311 native source/replay export — frozen handoff r1

Sprint: `source-contract-resolution-r311`, contract SHA-256
`0ee7472447c13fd586e0afb80101b2b33c5eef8bfd9c852016fa39e959b891c3`.
Baseline: `2ebaa41d4`. Assignment/handoff ID: `R311-NATIVE`, revision 1.
Parent gate: unchanged source Union catalogue and child/result correspondence
applied to R159. This handoff supplies only finite same-HIR source/native
evidence; it does not close EI, R159, or whole-language correctness.

## Runtime, lease, and budget

Requested model/effort: `gpt-6-luna` / high per the fixed sprint contract.
Observed model, effort, runtime session, and launch receipt were not exposed to
this worker and remain UNKNOWN. Worker identity: `/root/r311_replay_export`.
Exact repository write leases: `crates/yu-solver/src/shadow_apply.rs` and this
file. Exact scratch lease: `/tmp/yulang-r311-native/`. No other paths were
written. No Git operation or child agent was used. The assignment cap is 1800
seconds; active seconds were not instrumented, but work remained within the cap.

## Outcome and source/native correspondence

Outcome class: `source-native-evidence` with a test-only serialization
contribution. The existing R310 R3 test remains the gate: it parses and lowers
`my id x = x; my answer = id (id 1)`, reads actual `LocalSource` Apply/Group
nodes and callee occurrences from one lowered HIR artifact, joins them to
source Call records, and runs its complete ownership validator before emitting
the Lean-readable block.

The block exports five exact HIR occurrence ordinals with their source-role
seed relations; four selected actual Replay child/lower/upper tuples with both
ordered typed `BoundKey`s and the actual context IDs; the retained
`FunctionPort(Result, Preserve)` and `FunctionPort(Argument, Swap)` records
with their typed native pairs, source ordinals and parent/child relations; and
the validated FreshUse antecedent, use origin, source bound, mapped relation,
and exact callee occurrence. Bound and pair renderings retain the native
`TermArenaBrand` and term index, endpoint kind, and polarity. This fixture has
context ID 0 for every selected node; no non-identity context claim is made.

The serialized artifact is `/tmp/yulang-r311-native/evidence.lean`. Lean
checks its source/edge/port counts and verifies that every exported source,
Replay, FunctionPort, and FreshUse mapped-relation reference resolves in the
exported relation inventory. These checks consume one finite validated fixture;
they do not establish the Rust validator's soundness, EI membership, general
source/native correspondence, or R159.

The source-to-native path shown is:

`actual LocalSource Apply/Group occurrences -> candidate source Calls and direct slot-0 origins -> generated ordered Replay/FunctionPort dependencies -> retained candidate context and native typed pairs -> Lean-readable finite data`.

There is no new runtime consumer or execution behavior downstream of this
test-only export. No production API, inference behavior, source domain,
diagnostics, expectations, semantics, or Simple-sub bypass changed.

## Checks and frozen artifacts

Focused locked offline Cargo command (exit 0):

```text
CARGO_TARGET_DIR=/tmp/yulang-r311-native/target cargo test --locked --offline \
  -p yu-solver --features shadow-apply-candidate --lib \
  r310_nested_call_replay_has_source_owned_parents_and_group_path -- --nocapture

1 passed; 0 failed; 0 ignored; 0 measured; 833 filtered out
```

Generated artifact check (exit 0):

```text
lean /tmp/yulang-r311-native/evidence.lean
```

Lean selected `leanprover/lean4:v4.35.0`; stdout/stderr log:
`/tmp/yulang-r311-native/lean-check.log`, SHA-256
`ef8153ace4cde3f6f4f120ff4e4e1c42021a3860dfa8e95d1a59f177586507f2`.
The tool emitted only its existing notice that it could not query the latest
release and used the installed v4.35.0.

Frozen hashes:

- `crates/yu-solver/src/shadow_apply.rs`:
  `e805704be5deb83203159e74e8d6bff9ef337d693b320d510a12c19c73c3f5b6`.
- `tasks/agent-loop/sprints/source-contract-resolution-r311.md`:
  `0ee7472447c13fd586e0afb80101b2b33c5eef8bfd9c852016fa39e959b891c3`.
- R310 R3 source/native handoff:
  `83656509ca625b901f6177aaaed1d66b8b5ae5dd6a8212f72e57f0cb144a7eb9`.
- `crates/yu-solver/src/candidate_context.rs`:
  `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`.
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
- Cargo log: `/tmp/yulang-r311-native/focused.log`, SHA-256
  `3dcb292a2d02a1b43fa817261f677a4c248f4af6fa3b401f53424d52df031522`.
- Lean artifact: `/tmp/yulang-r311-native/evidence.lean`, SHA-256
  `63e5ada2bb1049af14a08672381ebf6e75b12569e2e06ad73e668258f9a88314`.

`git diff --check -- crates/yu-solver/src/shadow_apply.rs` passed.

## Prior evidence, limits, and next step

Reused R310 R3's complete same-HIR validator, actual source occurrence joins,
typed ordered Replay checks, FreshUse antecedent-to-captured-snapshot check,
FunctionPort owner checks, Group edge and mutation controls. R310's reported
gap—no Lean-readable export—motivated this addition. No R309 forward-only
reachability result was reused as parent ancestry. The new Lean checks validate
only the data inventory and reference closure; the Rust validator remains the
source of the finite evidence and still needs independent review on these exact
bytes.

Exact remaining premise and owner: the proof/source owner must construct
original typed EI operands and source-owned `q_c` registration; the source/native
owner still needs a general checked bridge and independent review before any
application to unchanged R159. This packet neither supplies nor assumes those
premises. No provisional production instrumentation was added. The test-only
serializer is reversible; Luna owns any future removal or promotion decision.

Disposable scratch under the exact `/tmp/yulang-r311-native/` lease:
`target/`, `focused.log`, `evidence.lean`, and `lean-check.log`. The Cargo target
products and captured output are disposable after primary review.

Next related step inside the envelope: freeze these bytes and have Luna assign a
fresh independent source/native reviewer to attack identity preservation,
endpoint/polarity retention, edge/reference completeness, antecedent/source
binding, and the Lean checks' limited scope. No source-domain, semantic, or
lease expansion is requested. Writes stop after this revision.

## Revision 2 — independent-review repair

This sequential revision follows Luna's acknowledgement of R1 and the completed
independent preliminary review. R1 bytes and its original hashes remain above.
Assignment/handoff ID remains `R311-NATIVE`, revision 2; baseline remains
`2ebaa41d4`; the fixed contract hash remains
`0ee7472447c13fd586e0afb80101b2b33c5eef8bfd9c852016fa39e959b891c3`.

The reviewer found that R1 used an incorrect hardcoded file label, omitted the
HIR/definition owner from occurrence ordinals, and derived `relationIds` from
the very edge references whose membership it checked. R2 replaces those
representations. The source key now comes from the actual definition's module
FileKey (`candidate-tuple-source/tuple.yu`), `DefId` spelling and same-name
ordinal, source revision, and exact source text. Rust checks that the definition
root and each exported occurrence belong to the exact HIR artifact used by the
existing validator, and the source Call and FreshUse route joins use those
actual occurrence handles. The private `HirArtifactToken` remains opaque: the
source key is stable provenance for this artifact, not equality with that
runtime token and not a cross-run uniqueness promise.

All emitted native relation, context, captured-evidence, imported-evidence,
and use-origin references carry an explicit per-export session namespace and a
kind. Native term endpoints preserve the actual `TermArenaBrand` debug identity
and term index; row and effect endpoint indexes also carry the export session.
The session counter is local to the process and is not promised unique across
processes or runs. The artifact makes no cross-run joins.

The Lean artifact independently consumes the complete indexed retained relation
inventory enumerated from `State.observed_relations()`, with each actual typed
pair and context ID. It separately contains every captured route-bound evidence
snapshot and its imported-ID remap. The selected Replay records are serialized
from the actual dependencies. Lean checks their session-scoped child/lower/
upper references against that inventory; verifies the retained lower/upper
pairs against the signed bound inputs; requires positive lower and negative
upper polarity with a shared owner; and checks the child's typed pair against
the ordered bound items. FunctionPort rows retain the actual child pair and
parent. FreshUse checks connect the exact captured snapshot and imported
antecedent to its source bound/relation/context and connect the mapped relation
to its target bound.

R2 also adds Lean negative controls for foreign-session and missing relation
IDs, a foreign-session source occurrence join, a polarity mutation, a removed
Replay parent row, and removal of the FreshUse snapshot. The R310 Rust validator
still runs before serialization and retains its own source-observation
truncation check and post-solve mutation controls. These checks establish only
the finite artifact's internal correspondence and the tested validator gates;
they do not prove the serializer generally correct, close EI or R159, or
establish whole-language source/native correctness.

R2 source/native behavior remains the same concrete fixture path from actual
HIR Apply/Group and callee occurrences through generated constraints,
propagation, retained Replay and FunctionPort records, and typed native
relation pairs. No execution consumer, production API, inference behavior,
diagnostic, expectation, source domain, or semantic change was introduced.
No nonidentity context was present; all selected fixture contexts remain
identity context 0.

Final focused locked offline Cargo check (exit 0):

```text
CARGO_TARGET_DIR=/tmp/yulang-r311-native/target cargo test --locked --offline \
  -p yu-solver --features shadow-apply-candidate --lib \
  r310_nested_call_replay_has_source_owned_parents_and_group_path -- --nocapture

1 passed; 0 failed; 0 ignored; 0 measured; 833 filtered out
```

Final generated Lean check (exit 0):

```text
lean /tmp/yulang-r311-native/evidence-r2.lean
```

Lean used installed `leanprover/lean4:v4.35.0`; it emitted only the notice that
the latest release query failed and the installed version was used. Final R2
hashes:

- `crates/yu-solver/src/shadow_apply.rs`:
  `396212ca2df076634767fec253af8bc77604f2e0ed8558291be42d0175101a2a`.
- Cargo output `/tmp/yulang-r311-native/r2-focused.log`:
  `12fbbb6e742f733ebb4425a935aaa79074755bb1d244882cf69bc72bd7682775`.
- Lean input `/tmp/yulang-r311-native/evidence-r2.lean`:
  `2de6bd53569032621381d03ae82576ceb2adf6de5c3cccb3fd331ac53ceb5186`.
- Lean output `/tmp/yulang-r311-native/r2-lean-check.log`:
  `ef8153ace4cde3f6f4f120ff4e4e1c42021a3860dfa8e95d1a59f177586507f2`.
- Frozen direct dependency hashes remain as listed in R1 and were rechecked:
  `candidate_context.rs` `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`,
  `candidate_call.rs` `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f`,
  `candidate_effect.rs` `aeea54f55922cc6f15837a4533e63d21523ef88abfcd604b503b80cfd11bc20b`,
  `candidate_source.rs` `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`,
  `local_source.rs` `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1`,
  `yu-solver/Cargo.toml` `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`,
  and `Cargo.lock` `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`.

The R1 review failures are repaired in this revision; independent review of the
R2 bytes is still required. Mathematical EI/R159 and general source/native
parents remain open with their existing owners. The exact scratch lease now
contains `target/`, `focused.log`, `evidence.lean`, `lean-check.log`,
`r2-focused.log`, `evidence-r2.lean`, and `r2-lean-check.log`; all are
disposable after primary review. No new repository path is used. Next step:
Luna freezes this R2 revision and assigns a fresh reviewer to attack the
relation inventory, snapshot pairing, source owner/session boundaries, signed
composition, and negative controls. Writes stop after R2 freeze.
