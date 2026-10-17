# HIR-owned runtime entry correspondence handoff — revision 3, spec delta review pending

Sprint-ID: `receive-inlet-admission-and-hir-entry-correspondence-20261017`  
Contract revision / SHA-256: **3** / `e7300e34dbf87ca0dab862acd340d25a0cae84d7226caf97ea370cc39233a45d`  
Assignment-ID / handoff revision: `HIR-RUNTIME-ENTRY-CORRESPONDENCE-20261017` / **3**  
Parent: Goal `型推論と実行器が証明込みで実装できるまで続ける`; original theorem and production gates remain OPEN.  
Outcome class: **bounded HIR-to-runtime source correspondence for annotation-derived entry**.

## Result and application

- Author: `/root` (Luna/high), sole writer. Exact outputs: this handoff and `notes/theory/2026-10-17-hir-owned-runtime-entry-correspondence.md`.
- For selected `my apply f = { my step x = f x; step }`, HIR parameter/local identity flows directly to runtime Lambda/Closure fields; Value/Computation role comes from that formal's own annotation; local return/alias preserves the closure value; entry binds the same HIR formal ID in the captured lexical environment; parent-chain lookup finds the captured outer formal ID. Saved frames preserve identity fields and environment handles across request capture/restore.
- `execute` discards CandidateInference before `RuntimeProgram::from_hir`. The narrow annotation-derived runtime entry path therefore needs no candidate fresh-use evidence transport.
- This does not prove candidate result validity, source typing, semantic Pure/Handler role, arbitrary runtime correctness, original c2 inlet correspondence or production conformance. No code lease or semantic adoption follows.
- Falsifier: any changed named parameter/local identity, closure/capture relation, parent-chain resolution or saved-frame identity/environment restoration.
- Compiler review finding and repair: revision 1 misattributed outer definition formal `apply/f` to the local parameter-owner path. Revision 2 separated definition ownership at `local_source.rs:597-632` from local `step/x` at `:1285-1312` and `:651-690`; compiler delta review closed this finding CLEAN.
- Spec review finding and repair: revision 2 cited `machine.rs:1120-1175` for ordinary saved-frame restoration, but ordinary `TemplateNode::Bind` re-pushes the cloned frame at `:1104-1107`. Revision 3 now cites that exact branch and separately identifies handler/environment restoration at `:1143-1162`, with Owner/View nodes distinct. The underlying identity argument is unchanged; narrow spec delta review is pending.
- Artifact revision 3: `notes/theory/2026-10-17-hir-owned-runtime-entry-correspondence.md`, SHA-256 `b01d4f968257d924bf6228b3b1799f36d21855fd815492772c54528278c83be9`. Revision 2 remains preserved in Git history.
- Exact proof input: admission comparison artifact SHA `956b710546be0446ae6fd054a597196e467ce59202a08812d4c6ac349455a6e1`; handoff SHA `e8e0052c6337b28f6c252e5761f882f30574c1e2cdefdca79408cef9523d8822`.
- Original F2 SAT2 VIEW/CHECK owner requests remain OPEN in that prior handoff. The narrow HIR runtime result does not answer them.
- Checks: bounded source read at `machine.rs:1104-1107,1143-1162` and pinned source hash `b8f15e4617a9d66940183c7327499ff8a2beb1e9cae2abb997137fc1ca464b82`. No tests/builds/probes/compiler/runtime execution/expected-output edits. Luna's artifact and handoff revision 3 are frozen pending delta review; no descendants or scratch outputs.

## Independent review state

Compiler-referee full review and revision-2 delta review: **CLEAN**, with the prior owner-locator minor closed. Spec-auditor full review found no blocking or major conformance issue and one minor saved-frame restoration locator, now repaired in revision 3. Spec delta review is pending; architect review remains pending. This handoff is not an independent certification or parent closure.
