# Sprint EFFECT-PERMISSION-OWNER-CERTIFICATE/20261030-R27 — authenticate template and frame replay

Status: ADMITTED by Luna; implementation and proof remain unstarted until this admission is pushed.
Revision: 1. Branch admission base: `68dd3616e6b3b31cae67bd855c14d919beedde0b`. Clean source baseline: `9a74a70a32ebda716a00c7203d8e606343cf442a`; the pinned runtime sources listed in the input manifest are byte-identical between these commits. Worktree base: branch admission base, detached.

## Original outcome and success evidence

Original parent: `SourceProblem.InferenceSoundness` and the source-preservation claims in `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1, 3, 5. Preserve all supported source programs, original history scopes, complete Call/effects, correlated evidence and the joint admissible strategy. Effect-hygiene policy remains the user-selected rule in `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1.1–1.2, 3–4. R26 remains `CLOSED_INCOMPLETE — PREFLIGHT_REJECTED`: exact owner-node identity, mandatory connected control boundaries, and non-no-op mutation coverage were not authenticated. No R26 time or artifact is promoted by this packet.

Fixed outcome: for the unchanged callback and companion source, capture ordinary-entry execution evidence and a reviewed test-only certificate joining immutable template lookup, owner replay, the complete surrounding frame projection, and the actual request consumer; construct a Lean replay invariant for the represented constructors and apply it to authenticated snapshots when possible. If either execution route fails, freeze its first failed source transition and report the remaining premise. This is provisional evidence, not native/source closure or production authorization.

Success requires all of the following, or an honest first-failure receipt:

1. Baseline ordinary-entry execution selects callback result `1` and companion result `23`, or the exact first failed transition is recorded.
2. The certificate authenticates the exact `(template_handle, node_index)` by immutable lookup and proves the selected node is the actual `TemplateNode::Owner`; control resolution, borrowed/fresh choice, previous owner and the resulting `OwnerReturn` are linked in order.
3. The complete retained outer frame projection has source-derived endpoints and mandatory connected boundaries. Saved suffix nodes and outer retained frames remain separate; the chain reaches the actual distinct `write` request consumer.
4. Every negative mutation checks that its target exists, changes an applicable record, and is rejected. Cover wrong positive node index, absent required boundary, changed borrowed/fresh disposition, disconnected write lineage, and a mutation that would otherwise be a no-op.
5. Lean proves exact-node and complete-chain validation for the declared constructor model, prints each delivered theorem type and complete transitive axiom audit under pinned Lean 4.35.0, and applies the result to source-authenticated snapshots if available.
6. A fresh read-only reviewer accepts the exact frozen Rust and Lean artifacts. Original parent, source/native application, Native Grant, RootComp reachability, conversion to the earlier `History`, effect hygiene, soundness, principality, termination and production remain OPEN unless separately discharged by their actual owners.

## Two lanes and fixed source domain

Implementation owner: `implementer` (Luna/high). First execute the two sources through the ordinary playground entry with the exact baseline pins. Then make only test-only snapshot extraction and certificate validation changes in `machine.rs` and `receiving.rs`; write the JSON receipt and one handoff. The selected callback source is the user-approved callback in the input manifest. The companion is the unchanged `original-suffix-outer-receiver.yu` fixture. Expected observations are result `1` and result `23`, respectively. No production behavior, parser, source fixture, expected output, dependency, lockfile, language semantics, supported source domain or authority changes.

Proof owner: registered `lean_prover`. Reuse the reviewed R26 conditional module unchanged as a read-only overlay. Add `TemplateOwnerReplay.lean`, prove the exact-node lookup and complete-chain acceptance implication over explicit template-node/frame constructors, and state exactly which snapshot-authentication premises remain. No `sorry`, `admit`, project axiom, checker bypass or stronger source restriction. A model lemma is not source/native application; apply every proved lemma to the original parent only when its real premise is authenticated.

Independent review: one fresh `compiler_referee`, not either author, after both lanes freeze their exact hashes. Review requires exact input/candidate authentication; replay of every validator and mutation; source/constructor/consumer coverage; complete theorem-type and axiom evidence; and explicit residual parent premises. A rejection blocks candidate Cargo execution and all closure claims.

## Exact leases

Worktree: `isolated/ep-owner-certificate-r27/project`, detached at the branch admission base.

Rust writes only:
- `isolated/ep-owner-certificate-r27/project/tools/inference-playground/src/runtime/machine.rs`
- `isolated/ep-owner-certificate-r27/project/tools/inference-playground/src/runtime/receiving.rs`
- `isolated/ep-owner-certificate-r27/project/receipts/owner-certificate.json`
- `isolated/ep-owner-certificate-r27/project/build-target`
- `tasks/agent-loop/inbox/effect-permission-owner-certificate-r27-rust.md`

Lean writes only:
- `isolated/ep-owner-certificate-r27/project/notes/theory/lean/YulangClosure/TemplateOwnerReplay.lean`
- `isolated/ep-owner-certificate-r27/project/notes/theory/lean/.lake`
- `isolated/ep-owner-certificate-r27/lean-scratch`
- `tasks/agent-loop/inbox/effect-permission-owner-certificate-r27-proof.md`

Primary-owned admission files are the R27 contract, schema, input manifest, admission receipt and `current.json`. The copied R26 Lean module at `isolated/ep-owner-certificate-r27/project/notes/theory/lean/YulangClosure/CallbackHygieneCorrespondence.lean` is a hash-pinned read-only overlay. The reviewer is read-only. No worker may launch descendants, change leases/budgets, or perform Git operations. Root runtime paths owned by `UNKNOWN_WRITER` remain quarantined and untouched. Existing frozen R26 paths are not writable.

## Finite resources, ordered execution gates and stops

Fresh envelope: 7,200 seconds total: Rust 1,550; Lean 800; one fresh independent reviewer 1,000; Luna primary 3,850, including 500 reserved for closeout. Astra 0. No R26 remainder transfers. At most 360 aggregate Cargo seconds. At most two pinned Lean audits totaling 120 seconds. One heavyweight process at a time; serialize Cargo, rustc, Lean and Lake. The Rust author can execute baseline ordinary-entry routes after authenticating the pinned clean worktree. After the Rust candidate freezes, candidate compile and candidate runtime are forbidden until the independent reviewer returns exact-hash ACCEPT and Luna records a separate stage authorization. A later reviewer finding requires a new frozen revision and review before any gated execution. Stop on a failed source transition, changed semantics/schema, new dependency or path, insufficient resources, repeated failure of the same premise, or user STOP. Do not widen scope or transfer unused time.

The compact current state records NOT_STARTED/WAITING until actual launch receipts exist. RUNNING requires a current-session launch and active-work receipt. Unknown writers retain their quarantined paths; no capacity/path release is implied. At the end, freeze outcome and artifact hashes, synchronize current state, inspect the full outbound range and push only a coherent intended range. The original parent and all non-R27 gates remain OPEN.
