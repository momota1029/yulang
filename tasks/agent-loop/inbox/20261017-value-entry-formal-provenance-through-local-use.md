# Source correspondence handoff — revision 2, delta review pending

Sprint-ID: `receive-role-indexed-inlet-introduction-20261017`  
Contract revision / SHA-256: **1** / `c2422818a92a6666ab9672b45d4d8bf1abf069116c82d4a91228374fc07e10cc`  
Assignment-ID / handoff revision: `LOCAL-FORMAL-TRACE-20261017` / **2**  
Parent: Goal `型推論と実行器が証明込みで実装できるまで続ける`; original FORWARD-FIRST-CALL A/B and all source/native and production gates remain OPEN.  
Outcome class: **source correspondence evidence; experimental playground only**.

## Assignment and result

- Author/worker: `/root` (Luna primary and sole Git integrator); no descendants.
- Requested/observed model and effort: gpt-6-luna/high / UNKNOWN.
- Session: `current-session`; source trace resumed 2026-10-17 02:21:47 UTC after all direct and inherited pins matched. This packet froze 2026-10-17 02:24:03 UTC; elapsed 136 seconds, conservatively charged 150/360 seconds.
- Exact leased outputs: this handoff and `notes/theory/2026-10-17-value-entry-formal-provenance-through-local-use.md`. No code or other path was written.
- Result: HIR and candidate Call retain the original source formal identity for `f x`. Local fresh-use stores structural solver remaps but no HIR formal ID/entry relation. Playground `execute` discards CandidateInference; runtime `from_hir` derives Value/Computation directly from the source formal annotation. No candidate-to-runtime evidence transport is established.
- Revision 1 finding and repair: independent compiler review found that the selected named `my step x = ...` formal had been cited to the separate inline-Lambda lowering branch. The selected named formal is produced from its `IdentifierPattern`: `local_source.rs:1285-1312` records its source origin and owning local; `:651-690` wraps it in the retained Lambda. The source artifact now states that exact path. The central transport conclusion is unchanged.
- Parent application: selected unannotated `step x` has runtime `Value` entry under this annotation rule. That does not prove semantic Pure/Handler role for `f` or arbitrary original c2. The trace identifies a missing correspondence seam; it is not a source counterexample or production compiler defect.
- First missing owner/path: explicit validated local-route-to-runtime plan export/import, retaining source root, Lambda and formal identity and its owner, plus the independent source theorem that gives the data semantic authority. Candidate local maps alone are structural constraints.
- Falsifier: any bridge that changes the `HirParameterId`/owning Lambda, treats a local alias as a formal without resolved parameter provenance, or equates Value/Computation entry with Pure/Handler.
- Checks: read-only source inspection and SHA-256 pin verification. No tests, build, probe, compiler execution, runtime execution or expected-output edits.
- Artifact revision 2: `notes/theory/2026-10-17-value-entry-formal-provenance-through-local-use.md`; SHA-256 `76855d9330a9b5404dfa83bffc4c033dea4c40763b8104bda04849474278deec`. Revision 1 artifact/handoff remain preserved in commit `3b16bb603`.
- Candidate inlet artifact remains unselected: `notes/design/2026-10-17-receive-role-indexed-inlet-introduction.md`, SHA-256 `7716a71d6bf6f5212bd455e1a3959569748e558238d0a164649ec1c57d92b72c`.
- `NO_SAFE_CODE_SLICE`: `candidate_source`, `candidate_call`, `candidate_scheme`, `inference-playground::execute`, and runtime `from_hir` do not supply a reviewed semantic bridge. No implementation authority was granted.
- Mutual TODO: original source typing/action owner to supply an independently justified T/Entry-Exec-Return producer/import path; local-route owner to account for source formal provenance if such a bridge is proposed; runtime consumer owner to authenticate it. Any behavior change returns to the user for semantic adoption.
- Writer STOPPED: revision 2 source trace and this handoff are frozen for compiler delta review; no descendants or generated outputs. Prior independent finding is not self-certified; spec and architecture reviews remain unstarted.

## Frozen input pins

The nine code/source pins and candidate artifact hash are recorded in the
source trace. Sprint contract SHA-256: `c2422818a92a6666ab9672b45d4d8bf1abf069116c82d4a91228374fc07e10cc`.
All pins matched immediately before authoring. The candidate rule, its SAT2/RG2
identification and original parent obligations remain unselected/open.
