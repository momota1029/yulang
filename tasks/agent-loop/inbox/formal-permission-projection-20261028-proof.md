# FORMAL-PERMISSION-PROJECTION proof handoff

- Sprint: `FORMAL-PERMISSION-PROJECTION-20261028/r1`; frozen contract SHA-256 `3d7230480fd223028c076a70ea948e80f9857af64fddaad05d25fb0944a14be9`.
- Assignment `/root/formal_permission_projection_proof`; handoff revision **1**. Baseline supplied by primary: `aa33dd79f5166dcd22174ab6403d56c3e5fe2f10`. No Git command ran.
- Role: bounded leaf; sole author this worker; no descendants. Requested registered `lean_prover`; effective model/effort metadata UNKNOWN. Current runtime launch is the primary's NEW_TASK, not a status-row inference.
- Outcome: **constructed but unchecked final module; verification INCOMPLETE; parent OPEN**. No source-qualified Rust counterexample and no independent review claimed.

## Original source and exact remaining premise

Original whole-language obligation: `docs/yulang-whole-proof-closure-ja.md` §§1, 3, 4, including every original source constructor, effects/profiles, scopes, shared witnesses and native correspondence. Relevant existing Lean boundary is `YulangClosure.OriginalEffectHygiene` (opening scope notice) and `YulangClosure.OriginalSourceInterpretation.FunctionGuards.profile`; neither is a completed whole effect-hygiene theorem. Accepted annotation semantics come from Authoritative `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2, including October 15/16 corrections: permission, actual inflow and actual handler residual are distinct; symbolic dependencies and unrelated same-family contributions remain.

Pinned construction: `candidate_effect.rs:1408–1544`, `candidate_formal_value_pair`, `candidate_formal_pair`, `candidate_formal_effect_port`; published negative domain/permission list at `candidate_formal_annotation:1633–1705`. Functions use negative argument/positive result in the positive constructor and positive argument/negative result in the negative constructor. A negative concrete annotation allocates one shared effect-row port for its positive/negative pair; the permission records the full structural path and original source metadata, without storing the port itself. Tuple elements extend the path and preserve variance.

Capture owners: `candidate_scheme.rs:1797` (`Capture::term_endpoint`), `:1930–2100` (`Capture::expand_node`), `:2784–2800` (negative-formal-root publication). The last operation inserts a root only if the corresponding endpoint is already in the capture endpoint map. It does not itself prove endpoint existence or recursive child-image preservation. Export owner: `CandidateGraphExport::formal_effect_permissions`, `shadow_apply.rs:2638–2696`.

**First remaining premise / owner:** primary source/proof owner must establish from actual successful construction, interning, expansion and retained endpoint maps that each permission path reaches the captured image of the exact constructor-allocated port, with argument polarity flips, tuple child identities and aliases/representatives preserved. This is not an assumed `LocalLaws` field in the new module. The worker did not construct the source-to-Lean constructor simulation or the capture algorithm's endpoint-image invariant. The source lane's independent handoff remains separate evidence for primary adjudication.

Parent application: the structural consumer equations expose what a successful exporter reads; they cannot establish permission arrival, handler eligibility/selection, subtraction/residual preservation, whole effect hygiene, original A/B, source/native correspondence or production. Original parent quantifiers and accepted language are unchanged. No gate is closed.

## Artifact and represented cases

Changed only `notes/theory/lean/YulangClosure/OriginalFormalPermissionProjection.lean` and this handoff, plus leased scratch `/tmp/yulang-formal-permission-projection-20261028/proof/`. Shared root imports and `.lake` were untouched.

Final module SHA-256: `287908091421872e42a07214199351794f2b81d881c161797516a7f218171be3`.
Dependency/log/source inventory: `/tmp/yulang-formal-permission-projection-20261028/proof/manifest.json`, SHA-256 `4cd68c53dc69d338ce5eaa2a7164f09e053a0de9ed4ae6a729acf352f93f791e`. It records all five contract dependency hashes (all matched), additional parent/type/config hashes and isolated Lean source hashes. The isolated project is `proof/project/`; audit sources and logs are directly under `proof/`.

Fully qualified prefix for every declaration below: `YulangClosure.OriginalFormalPermissionProjection`.

- `function_argument`, `function_result`: any graph, node and polarity; a matching Function node makes a singleton Argument/Result path return its exact stored effect child.
- `function_nested`: any nonempty suffix; intermediate Argument/Result steps follow the corresponding value child.
- `tuple_element`: matching tuple, in-range index and actually stored child; a nonempty suffix follows that child. `tuple_final_rejected`: every graph/current/index rejects a final Element.
- `missing_root_rejected`: every path fails when its captured root is absent.
- `export_provenance`: intended inversion of successful single export into identical permission metadata and actual domain/root/path/effect-row lookup equations. **Final proof repair unverified.**
- `list_export_provenance`: intended all-or-error list projection preserving the complete input metadata list in order. Depends on the preceding theorem; **final proof repair unverified**.
- `unrelated_capture_can_succeed`: an explicit unrelated graph passes export checks and returns node 1 although an independent designated constructor port could be node 2. This refutes only the logical implication from export success alone; it is not an execution of Rust construction/capture.
- `equal_family_distinct_occurrences`: concrete example with equal concrete lists, distinct occurrence/source-row records and one shared returned graph node; neither record is erased.

Model scope: indexed graph Function/Tuple/Row lookup; empty/final/missing paths; arbitrary stored polarity; opaque unquotiented metadata. Non-Function/Tuple node constructors are collapsed to a rejecting `other` because this consumer rejects them. Missing nodes/tuple children/non-effect final rows reject by definition. Natural-number addresses model successful native checked additions; overflow is an omitted native rejection case. Full constructor execution, endpoint interning/deduplication, alias canonicalization, resource failures, owner filtering implementation and source simulation are **not proved**. Arbitrary row IDs permit shared/merged rows but do not establish Rust's merge/representative relation. Polarity-parametric lookup is not a proof of constructor polarity correspondence. This structural slice does not replace the original language.

## Actual execution and failure evidence

Native tool resolved read-only using `elan which lake`:
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Actual versions (exit 0): Lake `5.0.0-src+eb6cafb (Lean version 4.35.0)`; Lean `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release. Project pin/config/manifest read; no dependency or installation changes.

**10 Lean/Lake calls total; no further calls authorized or executed.**

1–2. Native `lake --version`; `lake env lean --version`: exit 0.
3. Direct `lake --no-cache env lean -j1 -M1024 YulangClosure/OriginalFormalPermissionProjection.lean` from wrong root: exit 1, missing relative file; `attempt-1.log` retained.
4. Same direct command in isolated project: exit 1; grouped structure fields failed elaboration, cascading diagnostics; `attempt-2.log` retained. Repaired fields individually.
5. Same isolated direct command: exit 1; `export_provenance` expected a reflexive domain equation after case reduction; `attempt-3.log` retained.
6–8. **Sole skill checker invocation**, exact command in `verification-resource.json` / `verification.log`: `check_lean.py --project .../proof/project --lake <native> --module YulangClosure.OriginalFormalPermissionProjection --full --timeout 220`, all ten `--theorem` names above. Its two version commands passed; module build failed at another equation in `export_provenance`; checker exit **1**, before default build/audit. **The reserved helper/full gate failed.**
9. `lake --no-cache build +YulangClosure.OriginalFormalPermissionProjection YulangClosure`: new module failed at the next equation; baseline targets continued rebuilding. Stopped the known doomed build, signalling the exact Lake process and current child; command exit **-15**. `manual-build.log`, `manual-build-resource.json`, `build-stop.json` retained. No successful default-target integration claimed.
10. Full new module source plus the helper's generated theorem-kind/type/transitive-axiom audit in `FinalModuleAudit.lean`, checked by native `lake --no-cache env lean -j1 -M1024 --root=<proof> -o <proof>/FinalModuleAudit.olean <proof>/FinalModuleAudit.lean`: exit **1**. `final-audit.log` retains complete printed theorem types, errors and axiom lists. Audit validator did not pass. Final repair replaces the remaining reflexive capture equation with its actual `captured` hypothesis; no post-repair execution was available under the call bound.

Complete axiom outcomes from call 10: `function_argument`, `function_result`, `function_nested`, `tuple_element`, `tuple_final_rejected`, `missing_root_rejected`, `unrelated_capture_can_succeed`, `equal_family_distinct_occurrences` each print `[propext]`. `export_provenance` prints `[propext, sorryAx]`; `list_export_provenance` prints `[propext, sorryAx, Quot.sound]`. The latter two are Lean's recovery declarations after a failed proof, explicitly rejected by the audit, **not delivered proofs**. No claim that the failing command checked the full module. The final source contains no explicit `sorry`, `admit`, project axiom, native-evaluation assumption or checker bypass; this source search does not override the failed audit.

Resources: individual timed records total approximately 89 seconds including versions (under 300s execution envelope). Largest measured RSS 981,976 KiB, under 1 GiB; full build max 866,220 KiB. Helper/manual build/final audit pinned OS affinity to CPU 0, `LEAN_NUM_THREADS=1`, Lean `-j1 -M1024`. Earlier direct calls used `-j1 -M1024`. Build wall 78.015s (72.810s user + 4.848s system); final audit 2.792s (1.418s user + 0.350s system). Overall worker wall start was not instrumented locally; primary owns actual launch timing. No Rust/Cargo/test/Git or network command ran.

## Exact continuation and STOP

Request `FORMAL-PERMISSION-CAPTURE-IMAGE-1`: parent unchanged; first required evidence is the constructor/capture endpoint-image invariant at the owners above, not equality of concrete families or canonical rows. Inputs: pinned constructor pair, capture endpoint map and actual expanded-node worklist. Proposed output: source-qualified construction invariant composed with exporter lookup; falsifier: an actually successfully constructed/captured/exported permission whose returned index is not that port's captured image. This packet supplies no such Rust falsifier.

Primary may grant a fresh bounded verification packet for the final local repair and the skill's complete helper/full gate, then assign fresh independent review. Current artifact is not commit-ready proof closure. No automatic renewal requested or used.

**STOP / writes stopped:** after freezing this revision, no more construction, checks or writes will occur. All worker-owned executions returned or were terminated with retained receipts. No descendants or unresolved worker-generated process is intentionally left running. Only primary may grant a new lease/verification envelope or integrate. Parent, source/native, review and production remain OPEN.
