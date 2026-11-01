# R136 — native adapter typing and nested permission constructor law

Status: ADMITTED for one exact source-only Rust type correction and one
bounded Lean constructor theorem. The parent goal remains the original Yulang
source soundness/effect-hygiene obligations; this sprint closes neither
whole-language theorem nor production gate.

## Parent and fixed scope

Preserve `SourceProblem.InferenceSoundness` and the original Oracle effect
hygiene statement, including their source domains and quantifiers. The Rust
lane repairs only an internal argument-type mismatch in the already committed
native adapter. It may not connect a consumer, change solver decisions, weaken
validation, alter annotation semantics, or treat static reconstruction as
compilation.

The proof lane formalizes the committed nested-formal permission constructor
inventory: supported negative Function ports with explicit concrete rows
produce permission records carrying their exact structural path and source
identity; variance flips at arguments and is preserved at results/tuple
children. It must distinguish this `FormalPermission` path from the outer
computation-entry `FormalEntryPermission` path and preserve the committed
concrete-plus-symbolic-tail domain boundary. This is a constructor lemma only;
authentic arrival, per-use transport, Catch subtraction, source/native
correspondence and whole soundness remain OPEN.

## Baseline and Rust target

Branch `yulang3`, baseline `abbe733b952138b5d576c30936692dd262f3e92f`.
The committed `candidate_scheme.rs` baseline is 508,255 bytes,
SHA-256 `9cb8349a6ad43ddde8f54ae04ea464a61781b626b25917e928d45d49de3b2012`.
The exact source-only target is 508,261 bytes,
SHA-256 `e2b6209e3bf486a302e52e5051be60bf7cd8187a7a1e8453087b94f77e06b814`.
It changes only the extractor argument at line 506 from `&session.store` to
`&session.store.terms`, matching `&BranchTermArena` with the owned arena field
of `ConstraintStore`.

Pinned committed dependencies: `lib.rs` SHA-256
`429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be`,
`term.rs` SHA-256
`d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`,
`candidate_effect.rs` SHA-256
`102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01`, and
`candidate_receiver.rs` SHA-256
`335f5f2cd4841dd8288306623ee863606e355b9ceda6948ab6877d944bed3165`.
The Rust writer and referee inspect immutable `git show HEAD:` blobs only;
they do not inspect or edit dirty working-tree files.

## Exact assignments and gates

1. **Rust source candidate**, handoff lease only:
   `tasks/agent-loop/inbox/effect-permission-adapter-arena-type-r136-source.md`.
   Reconstruct the one-line target from immutable HEAD; verify the complete
   extractor signature/call sites, `ConstraintStore.terms` ownership/privacy,
   feature gates, exact dependency pins, target hash and changed-line count.
   No source write, compile, Cargo, test, Lean, environment probe, scratch,
   staging or Git operation.
2. **Lean constructor proof**, exact artifact leases:
   `notes/theory/lean/YulangClosure/FormalPermissionConstructorR136.lean` and
   `tasks/agent-loop/inbox/formal-permission-constructor-r136-proof.md`.
   Start from the existing `OriginalEffectHygiene` definitions and the exact
   committed Rust constructors. Define the supported structural fragment and
   prove a non-assumed inventory theorem. Do not encode the conclusion as an
   input field, admit missing cases, use `sorry`/axioms, or claim the model is
   already a source instance. Give theorem types and complete `#print axioms`
   audits. Use the pinned Lean toolchain/project and at most one verifier,
   1 CPU, 1 GiB RSS, 120 seconds; no `lake update`, network, extra worktree, or
   cache/environment setup. If the gate cannot complete within that envelope,
   preserve the exact failure and stop.
3. **Fresh independent Rust referee** reviews only the frozen Rust handoff and
   pinned committed dependencies, at most 180 seconds. No source writes or
   execution. A target/hash/dependency mismatch or a semantic/ownership issue
   blocks integration.
4. **Fresh independent Lean proof referee** reviews the frozen theorem file,
   handoff, original claim and exact source locators, at most 240 seconds.
   A source-domain mismatch, hidden assumption, unclosed theorem or incomplete
   axiom audit blocks proof promotion.

Total active envelope: 1,800 seconds; four assignments maximum; no Astra.
R111's Rust compiler/resource gate remains unmet and unspent. No Cargo/build or
tests are admitted in this sprint.

## Integration and stop conditions

Only Luna integrates. After a fresh Rust PASS, Luna may stage only the exact
one-line committed-baseline patch, preserving every existing dirty or
untracked path. Review PASS permits a research-only source checkpoint; it does
not claim compilation, runtime reachability, source/native correspondence,
proof closure, hygiene closure or production readiness. Before push, inspect
the complete outbound range against `origin/yulang3`; never force-push.

The Lean theorem may be retained as a conditional structural result only if
its own reviewer passes. It does not enter the whole closure unless its source
map is authenticated and integrated in a later exact packet. Preserve the
original parent gates OPEN. Stop if a required source path is dirty/quarantined,
the exact immutable target cannot be reconstructed, the theorem requires an
unapproved semantic choice, or a verifier limit is reached.

## Source map and falsifiers

Committed constructor locators: `candidate_source.rs:1323–1341,2472–2475`;
`candidate_effect.rs:1614–1748,1763–1835,1897–1976`; exported nested records at
`shadow_apply.rs:2609–2640,2680–2711`. HIR rows retain a possible concrete
sequence plus one symbolic variable at `source_annotation.rs:630–687`, while
nested negative formal rows reject concrete-plus-tail at
`candidate_source.rs:701–707` and `candidate_effect.rs:1607–1609`; the outer
entry constructor has a distinct rule.

Rust falsifier: another required coercion, cfg-specific signature, inaccessible
owned field, or source change outside the one call invalidates the target.
Proof falsifier: a supported nested annotation omits/adds a record, changes
variance/path/source identity/member order, admits the excluded concrete-plus-
tail case, or routes outer entry permission through the nested constructor.
