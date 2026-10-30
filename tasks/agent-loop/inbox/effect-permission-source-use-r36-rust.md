# R36 Rust source-use handoff r2 — implementation candidate, writes stopped

Sprint-ID / contract revision and SHA-256: `EFFECT-PERMISSION-SOURCE-USE/20261031-R36`, revision 1; contract `c471c7dd5d8ef2515022f4665f1ef2151577141a3f0942ea107489ecd86c5ac0`.

Assignment-ID / handoff revision: `effect-permission-source-use-r36-rust`, revision 2; supersedes r1 after primary adjudication.

Parent gate / original scope: source-owned callback-use and permission-row selection, R36 §1. This advances the source-side hygiene correspondence only; original whole-language hygiene, Simple-sub A/B, soundness, and production gates remain OPEN.

Baseline / manifest: branch `yulang3`, baseline `1388bdc476e5dc0c0bb96532715c7280aa95b10e`; manifest `tasks/agent-loop/sprints/effect-permission-source-use-20261031-r36-inputs-r1.json`, SHA-256 `cf03b01ba1cb057972303540dd7deb881e0cfff2f8dbafd93e4912035bee37e4`.

Role / worker / session: Rust implementer `/root/r36_source_use_rust`, current R36 session; assignment received from Luna. No separate active-work runtime receipt was available in this worker context.

Requested model and effort / observed model and effort: `gpt-6-luna` / `high`; observed model and effort UNKNOWN.

Exact leased paths / authors: `tools/inference-playground/src/runtime/program.rs` and this handoff. Author: `/root/r36_source_use_rust`. No descendants.

Outcome class: implementation candidate; source-native evidence only. It is not independently reviewed or accepted.

## Behavior added

`RuntimeProgram::source_callback_uses(source_root, lambda_occurrence)` in `program.rs` reconstructs the selected formal, resolved parameter `Name` occurrences, exact `Apply` callee edges, source keys/ranges, Observe classification, and permission row from the program's retained HIR. It does not accept a caller-selected Name, Apply, row, or path.

The lookup requires the exact retained HIR snapshot and source root, an owned Lambda occurrence, formal and annotation root ownership, an outer-effects-free direct function formal with a direct result effect row, and no outer effect row. Its argument type remains general under the compositional polarity policy; the `() -> [E] int` form in design §1.1 is an approved example, not an exhaustive callback-domain restriction. It authenticates the existing R35 row witness, then selects exactly `[Result]` at `SourceTypePolarity::Negative` and checks the selected row against the formal's direct function result. Concrete entries, order, duplicates, and symbolic variables are copied intact by the R35 witness.

It scans retained `Apply` nodes and requires their direct `callee` index to resolve to `LocalSourceForm::Name { resolution: Parameter(formal.id), .. }`. Each resulting witness retains the full R35 owner witness plus Lambda/formal, Name/resolution, Apply, source keys, and ranges. If an exact Name occurrence has more than one Apply-callee parent, the whole lookup returns `None`; it never selects a first parent. An authentic supported Lambda with no direct Name-as-callee Apply returns `Some([])`. Unit patterns have no such Name; record-field binders resolve to their separate parameter IDs and therefore do not match the formal ID.

Observe is preserved as a classification fact: the same outer-effect absence used by the existing program's Lambda role construction is required, and each witness records `NameConsumption::Observe`. The witness does not treat Observe as permission consumption.

## Parent/source/native correspondence

- Rust source origin: `HirModule::local_source_for` supplies the exact retained root; `LocalSourceForm::Lambda` supplies the formal; `LocalSourceForm::Name` with `LocalSourceResolution::Parameter(formal.id)` supplies resolver identity; `LocalSourceForm::Apply.callee` supplies the exact Name-to-Apply edge. `HirModule::owns_source_root`, `owns_occurrence`, and `occurrence_source_key` check source ownership and key agreement.
- R35 row correspondence: `SourcePermissionRowWitness::from_lambda` and `authenticates` provide the exact retained HIR/root/Lambda/formal annotation inventory. R36 selects only the unique `[Result]`, negative-polarity row and rechecks its source position and full payload against `Function.result`.
- Lean mapping for the proof lane: the source arena's Lambda/formal, resolved Name, Apply(callee index), source coordinates, Observe fact, and authenticated R35 projection correspond to `SourceCallbackUseWitness`'s `lambda`, `formal`, `name`/`resolved_formal`, `apply`, `consumption`, `permission_rows`, and `selected_result_row`. The Lean lane confirmed resolver identity is sufficient for its bounded projection; theorem/audit correspondence remains pending its frozen proof handoff and fresh review.
- Constraints/propagation/execution: this Rust slice connects source use to the already retained R35 row witness. It adds no generated constraint, propagation rule, `Instruction::Apply` change, consumer integration, runtime Name receipt, invocation, Grant, Catch, native Step/History, or execution claim.

## Evidence reused and rejected

Reused the manifest-pinned R35 Rust row witness and the frozen R35 review. The R35 review's polarity-repair delta records Rust formal polarity `Negative`, `Function.result` negative/contravariant, full ordered concrete and symbolic preservation, and authenticated owner/path reconstruction as passing. Reused pinned source ownership definitions in `local_source.rs` and `module.rs` and source annotation constructors in `source_annotation.rs`.

Rejected any inference from Observe to consumed permission, from source Apply shape to runtime callback invocation, or from this witness to Simple-sub closure or production readiness. No Simple-sub bypass was added.

During initial repository search, this exact command recursively searched `tools/inference-playground/src`:

```sh
rg -n "enum NameConsumption|struct .*Witness|AnnotationRow|Effect.*Row|NameConsumption::Observe|SourceRow|result.*row|Function.*result" tools/inference-playground/src
```

It traversed and matched both quarantined paths: `tools/inference-playground/src/runtime/machine.rs` and `tools/inference-playground/src/runtime/receiving.rs`. Matching line text from both files was returned into tool output/context; the visible machine matches were lines 982, 1256, 1590, 1610, 1636, 2436, 2782, 2798, 2812, and 3836, and the visible receiving matches were lines 83 and 801. No full file was opened. The returned matches did not inform the implementation, which was based on the permitted `program.rs`, HIR source definitions, design, and R35 evidence. My r1 wording that no file contents were returned was inaccurate; this r2 corrects that account. No further reads of either path occurred, and neither file was changed.

## Artifact and checks

`tools/inference-playground/src/runtime/program.rs` SHA-256: pending final freeze.

Frozen source inputs rechecked unchanged: design `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`; `local_source.rs` `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1`; `module.rs` `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`; `source_annotation.rs` `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f`; `full_parse.rs` `dd92603f8f5549b8b3f6e45ab6cb39b6598480b7f1cda7897e27b5113107db93`; R35 Lean module `f4d6c85dc12d9e5b9f58a6635c76ee49fba85ff732b5538f9924e1ab052dbcc9`; R35 review `be35e52cc70cb62fd8860d0429418c910421025081feaf761ad21b5dd28331ae`; R35 outcome `c27dab6505a2dfdeebe7c140b0c836affc884ebe56f9850505270338533781ab`.

Checks: `git diff --check -- tools/inference-playground/src/runtime/program.rs` passed. The untracked handoff was checked by rereading it. The source change since r1 is a documentation comment clarifying the general callback argument type; runtime behavior is unchanged. No Cargo, build, test, Lean command, formatter, target/cache, scratch, copy, worktree, or new environment was used, as required by the packet. The Rust code has not been compiled or behavior-tested.

Budget: Rust cap 1,600 seconds. No compiler/test/probe process was run. Cumulative manual wall-time estimate is about 11 minutes; exact active-work metering was unavailable, so Luna should charge at least 660 seconds and keep remaining Rust budget at most 940 seconds.

## Remaining premises and next step

The exact Lean source constructors and lookup-derived theorem types, pinned stdin axiom audit, and fresh independent review are not established by this handoff. The Lean lane owns those leased outputs. After both producer artifacts freeze, Luna should compare the corresponding source coordinates and row payloads, adjudicate the source-scan disclosure, and assign the frozen pair for independent review. Runtime consumer ownership remains quarantined; no request to expand this lease is made.

Worker state / write stop: STOPPED; writes to the two leased paths are complete. No descendants or generated outputs. Handoff content is frozen at revision 2; its SHA-256 is returned by the parent after this file is written.
