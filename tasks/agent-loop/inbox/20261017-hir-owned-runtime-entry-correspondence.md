# Frozen HIR-owned runtime entry correspondence handoff

Sprint-ID: `receive-inlet-admission-and-hir-entry-correspondence-20261017`  
Contract revision / SHA-256: **3** / `e7300e34dbf87ca0dab862acd340d25a0cae84d7226caf97ea370cc39233a45d`  
Assignment-ID / handoff revision: `HIR-RUNTIME-ENTRY-CORRESPONDENCE-20261017` / **1**  
Parent: Goal `型推論と実行器が証明込みで実装できるまで続ける`; original theorem and production gates remain OPEN.  
Outcome class: **bounded HIR-to-runtime source correspondence for annotation-derived entry**.

## Result and application

- Author: `/root` (Luna/high), sole writer. Read-only lane began 2026-10-17 02:43:16 UTC after Astra STOP and all contract revision 3 pins matched. Exact outputs: this handoff and `notes/theory/2026-10-17-hir-owned-runtime-entry-correspondence.md`.
- For selected `my apply f = { my step x = f x; step }`, HIR parameter/local identity flows directly to runtime Lambda/Closure fields; Value/Computation role comes from that formal's own annotation; local return/alias preserves the closure value; entry binds the same HIR formal ID in the captured lexical environment; parent-chain lookup finds the captured outer formal ID. Saved frames preserve their identity fields and environment handles across request capture/restore.
- `execute` discards CandidateInference before `RuntimeProgram::from_hir`. The narrow annotation-derived runtime entry path therefore needs no candidate fresh-use evidence transport.
- This does not prove candidate result validity, source typing, semantic Pure/Handler role, arbitrary runtime correctness, original c2 inlet correspondence or production conformance. No code lease or semantic adoption follows.
- Falsifier: any changed named parameter/local identity, closure/capture relation, parent-chain resolution or saved-frame identity/environment restoration.
- Artifact: `notes/theory/2026-10-17-hir-owned-runtime-entry-correspondence.md`; freeze SHA recorded in final receipt/current state.
- Checks: bounded source reads and pin verification. No tests/builds/probes/compiler/runtime execution/Git/expected-output edits; no descendants or scratch outputs.
- Exact input: admission comparison artifact SHA `956b710546be0446ae6fd054a597196e467ce59202a08812d4c6ac349455a6e1`; handoff SHA `e8e0052c6337b28f6c252e5761f882f30574c1e2cdefdca79408cef9523d8822`.
- Original F2 SAT2 VIEW/CHECK owner requests remain OPEN in that prior handoff. The narrow HIR runtime result does not answer them.
- Writer STOPPED: exact artifact and handoff frozen for independent sequential compiler-referee, spec-auditor and architect review. This is not independent certification.
