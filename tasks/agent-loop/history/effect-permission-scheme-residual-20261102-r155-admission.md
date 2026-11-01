# R155 admission — remaining scheme diff

Sprint ID: `EFFECT-PERMISSION-SCHEME-RESIDUAL/20261102-R155`
Contract: `tasks/agent-loop/sprints/effect-permission-scheme-residual-r155.md`
Contract SHA-256: `1fb5c38fb14f6f11c1ac8d26930168f2b7bf0422948e4f79c0fcd3b916bd1309`
Baseline commit: `1dbb738de8af1b186ae56ca347e591ae0a1b3d83`
Frozen input: `tasks/agent-loop/inbox/effect-permission-scheme-residual-r155-input.patch`
Input SHA-256: `6ffdb7fda9f822a40024498160eedcac4cc6950ebc4b7bf93548e497b296664f`

The input contains one path only: `crates/yu-solver/src/candidate_scheme.rs`, 29 insertions and 77 deletions. Its committed base SHA-256 is `bc99466ff65d716c28295a0ab3ef2d50b1aef81c437bfcbac6ea4b79450a6ff2`; the exact dirty target inspected for freezing hashes to `4494ba879a05f90767779e12c9ca8e1364f2203f2f60eb63239a544c0d0da470`.

R155 follows dispatcher recommendation R155 after R154 concluded HOLD/NO_PATCH. It does not inherit source integration authority from R153. Implementation and proof workers are restricted to the immutable input and pinned committed source blobs. They must classify every change against the reviewed R152/R153 same-session binder and exact consumer/source-owner evidence. Receiver and runtime paths remain excluded.

The implementation lane has exact output leases `tasks/agent-loop/inbox/effect-permission-scheme-residual-r155-source.md` and `tasks/agent-loop/inbox/effect-permission-scheme-residual-r155.patch`. The proof lane has exact output lease `tasks/agent-loop/inbox/effect-permission-scheme-residual-r155-proof.md`. Fresh independent review is required at `tasks/agent-loop/history/effect-permission-scheme-residual-20261102-r155-review.md` for any candidate disposition. Each worker has a 600-second ceiling, review 300 seconds, Luna integration 180 seconds, total 1,680 seconds. No builds/tests/Lean, source edits, patch application, cache/environment/scratch/worktree, staging, commit, or push are authorized by this packet.

Success is an exact classification and an independently checked `NO_PATCH` or unapplied candidate with a source-qualified falsifier. Parent closure, runtime regression, source/native correspondence, INITIAL-STATE, CONSUMER, original A/B, and production remain OPEN.
