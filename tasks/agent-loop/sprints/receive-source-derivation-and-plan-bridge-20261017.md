# Sprint receive-source-derivation-and-plan-bridge-20261017 — two-Call source and runtime plan bridge

Status: ACTIVE, primary-owned serial mode because three inherited writer reservations remain UNKNOWN
Branch / baseline: `research/simple-sub-intrusion` / `6dbb6ad2511b182c1761ecea73f25640eee68899`
Parent: user goal `型推論と実行器が証明込みで実装できるまで続ける`; parent theorem and production gates remain OPEN.
Authority: user explicitly authorized changing the procedure and drafting a missing bridge for independent review. This permits candidate drafting, not semantic adoption, compiler edits, or production cutover.
Contract revision: 6. Revision 2 added the directly inspected continuation-template consumer to the implementation dependency pins; revision 3 reallocated 120 seconds from reserve to the two implementation-contract reviews; revision 4 reallocated the remaining reserve to two bounded delta reviews after one major finding; revision 5 moved 30 seconds from importer authoring to metadata review; revision 6 adds another 30 seconds to close the remaining handoff revision locator. The already frozen proof lane remains under revision 1.

## Fixed outcome and success evidence

For the authentic selected fragment

```text
receive(f : Unit -> alpha+) = let g = f(Unit) in g(Unit)
alpha+ = ([ctrl]Unit) -> [ctrl]Int
```

derive the source judgments from the existing source constructors while retaining every independent caller-context, provider, source-interface, and native correspondence premise. Apply the selected Value(Function) first-call and receiving introductions. Either construct the source-owned Entry/Exec/Return plan for both Calls, or isolate the first exact missing source premise. Draft the narrowest missing source-to-plan bridge that preserves original syntax and source evidence; mark it proposed until independent review and required user adoption.

Success means a reviewed artifact identifies which judgments and plan fields follow from the frozen source premises, which do not, and the exact next owned obligation. It does not require pretending that an unprovided source `T` exists. Full inference/executor remains the parent outcome.

## Frozen dependencies

All listed bytes were hashed at the baseline immediately before activation. Recheck before review/integration.

| Input | SHA-256 | Scope/status |
| --- | --- | --- |
| `notes/theory/2026-10-16-runtime-callable-view-construction-and-transport.md` | `8a3abd17cd26162c689a592e3f855580663d53bead80e8904ac964a16e1dfcb0` | reviewed CLEAN candidate algorithm; no implementation/architecture/production authority |
| `notes/design/2026-10-16-known-function-first-call-profile.md` | `b779ba779b66515eddb7e44ba1d0772a6853e69a1aa13a6c4528dbd8ea0852a1` | authoritative selected first-call constructor, scoped as stated |
| `notes/design/2026-10-16-receiving-profile-introductions.md` | `401ac9eee69f27a863cd08ea24eea6fbbd3388ada9d5366bd5818ee966d73b6f` | selected source introductions, scoped as stated |
| `notes/theory/2026-10-16-receiving-profile-introduction-grammar.md` | `ec3375229f956d678c64003a43bdb68c70a77c6b8e614e9348bdca6bde9d5a8c` | reviewed scoped grammar; no parent closure |
| `notes/theory/2026-10-16-runtime-function-result-source-construction.md` | `bfec4f6aad05711b580ceac69b242de502342c31bc09fabc701ad17c583c4961` | conditional extraction from independently valid source `T`; does not establish `T` |
| `notes/theory/2026-10-16-runtime-receiving-formal-source-supplier.md` | `4528791a9020278623fe271c3616c7cec9156d2324f41b68bea37563b33eb90e` | frozen conditional derivation; supplier remains OPEN |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` | selected source rule |
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` | selected contextual membership; independent caller challenge remains required |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` | selected Call interface definition |
| `notes/theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` | source construction |
| `notes/design/2026-10-16-source-result-bind-projection.md` | `f943e28a57e1a18cb22ec3e63a892f08711a3422293a240b168ea6dba5a082aa` | selected first-Call ResultBind projection |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` | typed core, source/semantic dependencies remain open where stated |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` | Draft; full source realization open |
| `tools/inference-playground/src/lib.rs` | `b65cfd7200e459c9448438ec979ffeb9eddb35c282600349cebe7ddf3b759bbb` | current playground execute seam |
| `tools/inference-playground/src/runtime/program.rs` | `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748` | current HIR importer owner |
| `tools/inference-playground/src/runtime/machine.rs` | `b8f15e4617a9d66940183c7327499ff8a2beb1e9cae2abb997137fc1ca464b82` | current Lambda/Callee/Return consumers |
| `tools/inference-playground/src/runtime/receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` | current receiving/view representation |
| `tools/inference-playground/src/runtime/continuation.rs` | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` | saved-template owner; no callable plan recipe fields |

## Lanes, exact leases, and sequence

One author at a time. Preserve three inherited UNKNOWN reservations and two reviewer/integration slots. No new child launch is authorized under this resource snapshot; Luna carries the proof assignment serially with a real active-work receipt. After proof bytes freeze and Luna stops writing, assign a fresh independent `compiler_referee` review. Only then Luna/high writes the unapplied importer/exporter contract, with its own exact inbox; freeze and review with fresh `architect` and `spec_auditor` where the candidate changes construction obligations. No compiler source lease is included.

Exact output leases for this sprint:

- `notes/theory/2026-10-17-receive-source-derivation-and-plan-bridge.md`
- `tasks/agent-loop/inbox/20261017-receive-source-derivation-and-plan-bridge.md`
- `notes/design/2026-10-17-receive-source-plan-import-contract.md`
- `tasks/agent-loop/inbox/20261017-receive-source-plan-import-contract.md`
- this contract and `tasks/agent-loop/current.json`, primary-owned scheduling records

Proof stages: (1) keep original binders, scopes and shared substitution; derive formal/Name, both Unit judgments, first Call, sequential result binding and second Call from the selected constructors; (2) apply selected first-call/receiving introductions; (3) construct tagged Return inputs and source-owned plans conditionally on exact derivations; (4) draft missing bridge definitions with source erasure/preservation obligations and counterexample conditions; (5) apply back to this component and identify the precise remaining context/provider premises.

Implementation-readiness stages after proof STOP/review: trace actual fields through source/HIR, `execute → RuntimeProgram::from_hir`, Lambda/Callee/Return/operation consumers; define exporter/importer validation, provenance, ownership/lifetimes, resource accounting and rejection; distinguish fields with established source producers from fields whose meaning depends on proposed semantics. Output remains unapplied and is not executable implementation.

## Boundaries, reviews and resources

No compiler/runtime code edits, build, tests, executable probes, source admission, semantic adoption or production cutover. Do not assume `T` from annotation syntax, native solve success, or hand-built plan records. Preserve original Function/Call quantifiers, providers and caller-context obligations. A conditional bridge is not a complete source supplier or parent theorem.

No more than 2100 seconds aggregate: proof 900s, importer contract 420s, independent reviews 660s, coordination 120s, reserve 0s. Revision 3 reallocated 120s to separate architect/spec reviews; revision 4 reallocated the remaining 120s to bounded substantive deltas; revisions 5–6 transfer 60s from importer-contract authoring to one final spec metadata delta. Review caps: proof initial and delta 120s each; architect/spec initial 120s each; architect/spec substantive deltas 60s each; final combined metadata delta 60s. No check/execution allowance. Primary stops at a genuinely missing semantic decision or dependency that cannot be drafted while preserving existing meanings. Parent and production gates remain OPEN.

Independent review criteria: source rules and quantifiers match their frozen scope; no hidden `T`, MODEL, caller challenge or provider acceptance premise; both tagged Return inputs remain distinct; every missing bridge has explicit inputs, output, preservation law and falsifier; importer contract points to real current owner paths and rejects absent/foreign/malformed plans without inventing source evidence. Review does not adopt candidate semantics.

Git: Luna stages only these explicit paths after frozen review/integration receipts, checks the complete outbound range, commits meaningful checkpoints and pushes non-forced. Pending question paths are excluded. Static sprint check is scheduling evidence only.
