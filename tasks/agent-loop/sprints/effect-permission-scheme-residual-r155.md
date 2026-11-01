# R155 — audit the remaining scheme diff

Status: admitted continuation for the user's ongoing Rust implementation audit. The only source subject is the immutable patch at `tasks/agent-loop/inbox/effect-permission-scheme-residual-r155-input.patch` (SHA-256 `6ffdb7fda9f822a40024498160eedcac4cc6950ebc4b7bf93548e497b296664f`). It changes only `crates/yu-solver/src/candidate_scheme.rs` from baseline `1dbb738de8af1b186ae56ca347e591ae0a1b3d83`.

## Fixed outcome

Classify every change as (1) already integrated in the baseline, (2) an independently justified candidate, or (3) HOLD because it depends on a removed or unauthenticated check. Directly compare the current binder with the reviewed R152/R153 session-owned version. Preserve the distinction between registration and packed/member positions, exact permission origin, source owner, provider identity and selected operation. Do not restore provider-equals-constructor-owner for returned/local functions. If a safe nonempty slice exists, provide an exact unapplied patch and source-qualified rationale; otherwise freeze `NO_PATCH`.

Original parent, quantifiers, source/native correspondence, original A/B and production remain unchanged and OPEN. This packet is analysis only: no live source edits, patch application, tests, build, Lean, cache, environment, scratch, checkout/worktree, staging, commit or push. The baseline R153 source checkpoint is already on `origin/yulang3`; its narrow review authorization does not apply to this residual candidate. Any candidate needs a separate exact source-only integration gate.

## Frozen identities and dependencies

- Baseline commit: `1dbb738de8af1b186ae56ca347e591ae0a1b3d83`.
- Baseline `candidate_scheme.rs`: `bc99466ff65d716c28295a0ab3ef2d50b1aef81c437bfcbac6ea4b79450a6ff2`.
- Dirty target `candidate_scheme.rs`: `4494ba879a05f90767779e12c9ca8e1364f2203f2f60eb63239a544c0d0da470`.
- Other committed Rust dependencies: `candidate_effect.rs` `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15`; `candidate_receiver.rs` `335f5f2cd4841dd8288306623ee863606e355b9ceda6948ab6877d944bed3165`; `candidate_context.rs` `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`; `candidate_intrusion.rs` `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97`; `candidate_source.rs` `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`; `lib.rs` `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be`.
- Relevant accepted evidence: R152 source/proof/review/outcome and R153 exact candidate/integration review; R154 receiver implementation/proof/review/outcome. Verify hashes before reuse. Do not read the live dirty source, dirty receiver, or quarantined runtime files.

## Lanes and leases

- `implementer` Luna/high, at most 600 seconds. Read only frozen input plus committed blobs; classify all hunks and, if justified, write an exact unapplied candidate patch. Outputs: `tasks/agent-loop/inbox/effect-permission-scheme-residual-r155-source.md` and `tasks/agent-loop/inbox/effect-permission-scheme-residual-r155.patch`.
- `prover` constructive source map, at most 600 seconds. Trace retained permission, source Lambda, selected member ordinal, capture and FreshUse through exact constructors/consumers; identify a concrete falsifier for cross-session or coordinate conflation. Output: `tasks/agent-loop/inbox/effect-permission-scheme-residual-r155-proof.md`.
- Fresh independent `compiler_referee`, at most 300 seconds, reviews frozen candidate and both handoffs; output lease `tasks/agent-loop/history/effect-permission-scheme-residual-20261102-r155-review.md`.
- Primary integration/adjudication ceiling 180 seconds; total 1,680 seconds. Reviewer must not inspect live dirty sources or quarantined runtime. Only Luna owns current-state/Git integration.

## Stop boundary

No candidate is applied or promoted by R155. Stop and report `HOLD` if exact session ownership, permission registration/member coordinates or required source evidence cannot be established. Keep the existing receiver diff and runtime quarantines untouched. Tests/builds/Lean and all new cache/environment/disk-heavy paths remain prohibited.
