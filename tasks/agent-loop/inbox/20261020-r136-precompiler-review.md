# R136 prospective compiler/source review

Sprint: repeated-choice-20261020-r136, contract revision 1.
Contract SHA-256: `2a9faf4255b2d74bb3c03cd2feff342d8d4c15ea9b544177a93f10c07930d28f`.
Assignment: r136-precompiler-review, handoff revision 1.
Worker: `/root/r136_precompiler_review`; actual model/effort not separately observable.
Baseline supplied by primary: `6c04fc08f76bc4cc2d71a3910e4aa476097a378b`.
Lease: this inbox only. No descendants or contributing coauthors.

Outcome: CLEAN prospective review. No BLOCKING, major, or minor compiler-correctness findings. This is feasibility review of the frozen candidate, not verification of implementation or proof, and grants no writer authority.

## Cause, owners, and concrete paths

The candidate exposes existing evaluator behavior; it proposes no downstream patch masking an upstream fault. The existing owning constructors support its forms:

- `crates/yu-hir/src/module/local_source.rs:1065`, `:1170`–`:1230`, and `:1255`–`:1318`: Boolean literal, operation catch with empty-call Unit payload and lexical continuation binder, and integer/wildcard Case construction. The two applications reference the same catch binder; Case does not introduce a replacement `k`.
- `crates/yu-solver/src/candidate_source.rs:482`–`:498`, `:619`–`:631`: resolved monomorphic operation catch admission and bidirectional checks on a used continuation's declared response. Primitive Bool passes the existing primitive-value path. No Function-response v1 exception is needed.
- `tools/inference-playground/src/runtime/program.rs:476`, `:552`–`:578`: Boolean, If, and Case have direct runtime instructions, preserving branch order and literal patterns.
- `tools/inference-playground/src/runtime/machine.rs:1653`–`:1723`: primitive Bool response permits capture; one immutable template handle is bound as `k`; selection pops the shallow handler before arm evaluation. `:1355`–`:1425` retains ordinary suffix frames and the containing owner without a store snapshot. `:767`–`:846` checks each response against the original declaration and enters the same retained template with fresh per-use control state. `:1143`–`:1180` writes the retained local cell; `:1181`–`:1249` selects the If branch and the first matching Case arm.

The expected finite path is feasible: capture the pending `choice` binding and conditional; resume with true, write choice and return 11; write handler-local first, select integer arm 11; resume the same template with false, overwrite the retained choice cell and return 23. `first` is a separate handler-local cell outside the captured suffix. Its already obtained value controls the second application. The containing relay owner remains active while the operation arm runs; no expired receiving authority is needed for this example. Current executable-owner borrowing/freshening at `machine.rs:1450`–`:1477` must remain distinct from reviving historical receiving boundaries.

Existing source controls independently inspected: `runtime_resume.rs:387` exercises repeat writes through the original pending local cell; `:584` exercises the exact Bool declaration, empty-call operation, and colon-form If admission. These establish local precedents only; they do not substitute for the proposed combined source execution or its final independent trace review.

## Canonical fixture and frontend correspondence

One canonical fixture can serve all requested surfaces. `web/playground/src/main.ts:3` already imports a `.yu?raw` fixture; `tools/inference-playground/tests/cli_demo_identity.rs:8` already includes a Web fixture through `include_str!`; `web/playground/smoke-test.mjs:43` reads a fixture with Node fs. The new entry must read/import the same file in each surface, with matching HTML option/key; `main.ts:68` already selects `main` for every example except the existing identity island. The current fallback to `ordinary` makes matching option/key inspection a required final review item.

`apps/yulang-wasm/src/lib.rs:11`–`:21` and `tools/inference-playground/src/lib.rs:167`–`:204` share the ordinary execute pipeline and integer formatting. The planned CLI stdin inclusion and Web fixture read need no filename-specific runtime branch. Final evidence must still establish identical fixture bytes, actual admission, exact `23\n`, and successful browser/WASM execution; prospective inspection does not claim any check passed.

## Authority and hashes

Read root AGENTS instructions, operating map, current state/protocol, design-authority rules, the selected contract, charter §§13–17, source-call-scheduling §§1–2, top-level inference principles, relevant current owners/tests, and the prior raw-resume constructor/implementation records. Governing selected invariants: outside shallow selection; whole delayed argument; current shared cells; no historical boundary revival; finite-example evidence cannot close general source, A/B, or production gates.

All ten direct source hashes listed in contract revision 1 were recomputed and match exactly. Additional inspected constructor/frontend owners are pinned here for final review:

```text
crates/yu-hir/src/module/local_source.rs d9f516993c579ae8f4dd905abb8400ffc0769072a904a4b4c8d4ffbefcde6442
apps/yulang-wasm/src/lib.rs 2fc9feb353b3130c4efc888270cec14cba8b2bbcc2fca03d3780c676e0468f8a
tools/inference-playground/src/lib.rs a0769f77feac552304f0516b0742637f51660c0bb8bf9391d18ae0f9de5e2473
tools/inference-playground/tests/cli_demo_identity.rs 09fecc7c8b8a152ec49d939517d3dcd4951fad48a2909c1faee15bf95cc7a773
notes/design/2026-09-29-scc-intrusion-redesign-charter.md 547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed
notes/design/2026-10-02-source-call-scheduling-choice.md 7b2d2556f4b6a93d7beb73a78f476bfea7d0f94de0c5f77649f6cd15ff69a530
```

Checks: bounded read-only source inspection and SHA-256 inventory only. No compiler, tests, builds, Git commands, runtime experiments, or implementation/proof writes. No implementer self-explanation was used as evidence. No repair or general theorem is claimed. Next boundary belongs to Luna: adjudicate both prospective reviews, preserve/revalidate dependency pins, and decide whether to grant the contract's lanes.

Worker state: STOP. WRITES_STOPPED. NO_DESCENDANTS.
