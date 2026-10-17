# HIR-owned runtime entry correspondence handoff — revision 2, delta review pending

Sprint-ID: `receive-inlet-admission-and-hir-entry-correspondence-20261017`  
Contract revision / SHA-256: **3** / `e7300e34dbf87ca0dab862acd340d25a0cae84d7226caf97ea370cc39233a45d`  
Assignment-ID / handoff revision: `HIR-RUNTIME-ENTRY-CORRESPONDENCE-20261017` / **2**  
Parent: Goal `型推論と実行器が証明込みで実装できるまで続ける`; original theorem and production gates remain OPEN.  
Outcome class: **bounded HIR-to-runtime source correspondence for annotation-derived entry**.

## Result and application

- Author: `/root` (Luna/high), sole writer. Read-only lane began 2026-10-17 02:43:16 UTC after Astra STOP and all contract revision 3 pins matched. Exact outputs: this handoff and `notes/theory/2026-10-17-hir-owned-runtime-entry-correspondence.md`.
- For selected `my apply f = { my step x = f x; step }`, HIR parameter/local identity flows directly to runtime Lambda/Closure fields; Value/Computation role comes from that formal's own annotation; local return/alias preserves the closure value; entry binds the same HIR formal ID in the captured lexical environment; parent-chain lookup finds the captured outer formal ID. Saved frames preserve their identity fields and environment handles across request capture/restore.
- `execute` discards CandidateInference before `RuntimeProgram::from_hir`. The narrow annotation-derived runtime entry path therefore needs no candidate fresh-use evidence transport.
- This does not prove candidate result validity, source typing, semantic Pure/Handler role, arbitrary runtime correctness, original c2 inlet correspondence or production conformance. No code lease or semantic adoption follows.
- Falsifier: any changed named parameter/local identity, closure/capture relation, parent-chain resolution or saved-frame identity/environment restoration.
- Revision 1 finding and repair: compiler review found that the outer definition formal `apply/f` had been attributed to the local parameter-owner path. Revision 2 distinguishes it: `local_source.rs:597-632` retains the definition formal ID in its Lambda and records `LocalSourceNamedGroupOwner::Definition`; local `step/x` alone follows `:1285-1312`, `local_parameter_owners` and local Lambda wrapping. The identity argument is unchanged.
- Artifact revision 2: `notes/theory/2026-10-17-hir-owned-runtime-entry-correspondence.md`; final SHA recorded in current state after freeze. Revision 1 remains preserved in commit `fad55c382`.
- Checks: bounded source reads and pin verification. No tests/builds/probes/compiler/runtime execution/Git/expected-output edits; no descendants or scratch outputs.
- Exact input: admission comparison artifact SHA `956b710546be0446ae6fd054a597196e467ce59202a08812d4c6ac349455a6e1`; handoff SHA `e8e0052c6337b28f6c252e5761f882f30574c1e2cdefdca79408cef9523d8822`.
- Original F2 SAT2 VIEW/CHECK owner requests remain OPEN in that prior handoff. The narrow HIR runtime result does not answer them.
- Writer STOPPED: revision 2 artifact/handoff frozen for compiler delta review. Spec and architecture reviews remain pending; this is not independent certification.
