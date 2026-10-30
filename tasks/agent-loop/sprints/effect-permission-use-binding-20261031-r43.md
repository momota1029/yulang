# EFFECT-PERMISSION-USE-BINDING / R43

Status: proposed bounded implementation/proof sprint. Admission follows state-size validation and live roster synchronization. This packet does not start work until Luna records exact leases and launches both lanes.

## Parent gate and intended result

Parent remains the annotation-effect permission/inflow/subtraction obligation in `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1, 1.1–1.2, with its original source domain and quantifiers. R39 retains a computation-formal permission. R41 carries registration-labelled entry incidence through capture/FreshUse. R42 checks the reconstructed native positive Function field under one exact module use. The remaining bounded gap is binding the actual retained permission record to that exact route without treating shared row or term images as identity.

The Rust lane may add a private, partial read-only binding interface. A successful result must use the actual retained `FormalEntryPermission` and one R42 native-incidence certificate, and preserve registration, parameter/formal, Lambda/source owner/occurrence, scope, annotation/row source coordinates, entry port, ordered concrete permission payload including duplicates, mapped row, exact `DefinitionUseId`, and FreshUse context. It must reject missing or ambiguous permissions, foreign owner/formal/scope/annotation/use/context, mismatched registration/Lambda/entry route, and any attempt to infer identity only from row or Term equality. It does not authorize a permission consumer or effect subtraction.

## Pinned checkout and dirty baselines

- Branch: `yulang3`.
- Pushed state head at proposal: `b41e2433644ef7359af6ab68754804dbf1eb768d`.
- R42 source checkpoint: `2182b07fbc7aa92c725634a78e0b2db3252e49e5`.
- Dirty admitted `candidate_effect.rs` baseline: SHA-256 `82da9265af3bd663443550f4b113816cf2618c56e96014d9298c4563e875e6db`.
- Dirty admitted `candidate_scheme.rs` baseline, including committed R42 plus pre-existing trace changes: SHA-256 `c14f6cecb38fbf54b15e808f7385d9782dec1a784a12eac1315e1c32becd8429`.
- R42 Lean: `61bb9ced2a80a75c2e952c3f5198a36ad7b9ae10f06df1a7996d38851107d4d6`.
- R42 review: `2bd380bc54c00674ca693d2058d11bddb471862d625215771aa444246aeec146`.
- R42 outcome: `784b45b73da9dbf0aff4e23d9b190b4f263070d9efeb56e037846eb453bf9a9f`.
- R41 Lean: `af7c2e3def8762287e95827896dc01d982954059bff09c476d1a94df94c0a79e`; R41 review: `33808a855db179bb7c51cb65f9703a556d05b2dd0445de0b20440ba880d50056`.
- R39 Lean: `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e`.
- Read-only `term.rs`: `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`.
- Read-only `lib.rs`: `b1dac8bd244e282ff42a2d580e237393153f9b912c6ac0adf110367def5c79ce`.
- Read-only `candidate_context.rs`: `030fcb4b6571c0db8a670d12d8a67fe8fcf465484502fe5b11b6d057e8026c38`.

Luna must rehash all pins at admission and record the exact source locations. Existing unrelated dirty bytes, tracked deletions and untracked artifacts remain untouched. If R43 code cannot be isolated from the admitted dirty baselines, commit the reviewed Lean/research artifacts alone and leave source uncommitted.

## Exact lanes and writes

### Rust implementation — Luna/high, ≤1,200 seconds

Writer: `/root/r43_rust`. Exact writes:

- `crates/yu-solver/src/candidate_effect.rs` — private lookup/binding over owning permission records;
- `crates/yu-solver/src/candidate_scheme.rs` — exact route/incidence handoff into that binder and ephemeral result;
- `tasks/agent-loop/inbox/effect-permission-use-binding-r43-rust.md` — sole handoff.

No changes to `lib.rs`, `candidate_context.rs`, term definitions/accessors, consumers, providers, Catch/subtraction, tests, fixtures, diagnostics, expected outputs or public API. Do not copy duplicate fields and compare copies in place of reading their owner. Do not flatten, sort, deduplicate, or reconstruct the concrete permission list. Missing/ambiguous or unavailable evidence yields no binding and leaves inference unchanged. Avoid persistent retained allocation; if exact implementation requires owned allocation, reserve fallibly and publish atomically or stop and return the material decision to Luna.

### Constructive proof — registered Lean prover, ≤1,200 seconds

Writer: `/root/r43_proof`. Exact writes:

- `notes/theory/lean/YulangClosure/UseScopedPermissionR43.lean`;
- `tasks/agent-loop/inbox/effect-permission-use-binding-r43-proof.md`.

Use the pinned R39/R41/R42 models in a bounded read-only stdin stream; no imports/install/build output. Model exact retained permission payload and route identity. Prove accepted-binding characterization, payload/duplicate-order preservation, distinct registrations despite shared row/Term images, and rejection of foreign/mismatched owner, formal, annotation, registration, definition-use or context. Apply prior theorems with the same permission witness. Rust record extraction remains an explicit premise; no verified Rust interpreter, provider-arrival result, subtraction, or parent closure claim.

Pinned Lean 4.35.0 executable only, stdin, one CPU, 1 GiB and 120 seconds per invocation. No `lake` or `lake env`, Cargo, tests, formatter, build, cache, `.olean`, scratch, target, worktree, environment or generated file.

### Independent review — ≤900 seconds

After both authors STOP and all outputs/hash identities freeze, assign a fresh non-author reviewer. Exact output: `tasks/agent-loop/inbox/effect-permission-use-binding-r43-review.md` (primary persists a read-only reviewer receipt if needed). Review owning-record lookup, all identity joins, duplicate/order preservation, no-certificate behavior, allocation/publication, dirty-baseline isolation, complete Lean theorem types/axioms, foreign/shared-image falsifiers, exact deviations, and remaining limits. No build or test.

## Sprint envelope and closeout

Total reservation: 4,200 seconds: Rust 1,200; Lean 1,200; independent review 900; Luna primary 900 including up to 500 closeout; Astra 0. At most two producers plus reviewer/integration reserve. No capacity override is proposed. Keep the existing checkout only; no worktree, environment, cache, target or scratch. Do not grow storage for this sprint.

Stage only independently reviewed R43 source hunks and exact Lean/handoff/review/outcome/state files. Inspect every outbound commit; push only coherent reviewed range. No force-push.

## Explicit non-goals

No provider-arrival authentication, permission consumption, propagation, Catch/residual selection or subtraction, original Simple-sub A/B closure, whole-language hygiene or soundness, principality, progress, termination, or production promotion. R42's two `lake --version` startup invocations remain recorded; R43 forbids Lake commands from process start. No authority to change semantics is granted.

## Falsifier and next consultation

Falsifier: a binding is accepted for a foreign registration/owner/formal/annotation/use/context, a missing or ambiguous permission, or a foreign shared-row/native-Term image; or duplicate concrete permission labels/order change. Stop on any such witness, missing owning source field, required write path outside the leases, or resource/authority change. Consult the dispatcher at those boundaries and at sprint close, not for each proof or check.
