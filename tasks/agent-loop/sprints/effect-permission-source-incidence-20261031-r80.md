# R80 — construct source incidence from aligned choice and native records

Status: admitted bounded research sprint. The objective remains the user's ongoing Yulang soundness goal.

## Fixed outcome

Construct the exact existing `OccurrenceQualifiedConsumerR66.Incidence` from the aligned source choice and exact native permission records. Do not accept `Incidence`, `Root`, successful `sourceProbe`, or global owner-selection success as inputs. Reuse R77's computed same-use plan, owner selection and parameter recipe, and R79's typed HIR-to-collected-definition bridge. Preserve occurrence-qualified slot-0/slot-2 facts, the actual registration, Lambda recipe, permission and Function argument-effect observations.

Derive `sourceProbe` agreement, R45 `OwnerReads` and `Identity`, and the parameter-recipe field together. Include a nonempty successful finite witness with distinct Name/use and Apply/checking coordinates. Reject mismatched local/global selections, foreign registrations sharing Function/row images, substituted permissions, incorrect parameter recipes, duplicate source facts, and confusion between a parameter root and registered Lambda root. Stop at a missing owner record; do not add a weaker replacement relation or change approved semantics.

Apply the construction to the original R66 `Incidence` and identify the exact remaining premise before R66 `Root` and physical root joins. This is a bounded theorem and implementation checkpoint, not original A/B closure or production authorization.

## Exact assignments

- Constructive Lean: `notes/theory/lean/YulangClosure/ConstructedSourceIncidenceR80.lean`; handoff `tasks/agent-loop/inbox/effect-permission-source-incidence-r80-proof.md`.
- Rust join: `crates/yu-solver/src/candidate_receiver.rs`; handoff `tasks/agent-loop/inbox/effect-permission-source-incidence-r80-rust.md`.
- Fresh independent review after both author lanes freeze: `tasks/agent-loop/inbox/effect-permission-source-incidence-r80-review.md`.
- `crates/yu-solver/src/lib.rs` is read-only. No collection behavior, HIR fields, persistent maps, inference semantics, tests, fixtures or expected output changes.
- Luna primary owns current state, exact runtime leases, authorization of any direct Lean stdin invocation, review adjudication, outcome/closeout, explicit-path staging, commit and push.

The Rust join must combine `internal_owner_choice` with the existing native incidence inside `SourceInternalProjection::capture`, authenticate identical borrowed use/registration/recipe records, original permission coordinates and Function-child ownership, and feed that joined evidence into the existing projection. Do not add an unconsumed parallel constructor.

## Baseline and governing evidence

Baseline commit: `26dc98766a5779a92b42651bbc462d01ebc3ec72` (`HEAD == origin/yulang3` at admission). Direct dependency hashes are pinned in `effect-permission-source-incidence-20261031-r80-inputs-r1.json`. Governing definitions: R45 `InternalPermissionIncidenceR45`, R55 `SourceInternalContextR55`, R65 `OccurrenceQualifiedFactReadersR65`, R66 `OccurrenceQualifiedConsumerR66`, R77 `SourceInternalChoiceR77`, and R79 `CollectedDefinitionBridgeR79`; plus the R77/R79 outcome and reviewed handoff receipts named in the manifest.

## Resources, checks and stop conditions

Fresh envelope: 4,800 seconds total (Rust 1,000; proof 1,800; review 1,000; primary 1,000 including 500 closeout); Astra 0. At most two separately committed and pushed exact-input direct Lean stdin authorizations, each at most 120 seconds. No Rust compiler, Cargo, tests, builds, formatter, Lake, cache, target, scratch, additional environment, nested CLI, or worktree. Same existing checkout only; no generated build output. Preserve all 32 pending questions, UNKNOWN worker observations and quarantined paths; current state remains at most 16 KiB.

Use only in-memory stdin/stdout for an explicitly authorized Lean audit. Retain the exact input, stdout, stderr, executable and source-slice hashes and all theorem types/axiom reports in the assigned handoff. `git diff --check` and the required static sprint checker are allowed but do not establish compilation or independent review.

Stop at a missing owner record, a need for a wider lease/semantic decision, an accepted blocking finding that invalidates the construction, or budget exhaustion. Keep Rust source evidence, bounded Lean theorem evidence, independent review, source/native extraction, R66 Root, original A/B, whole-language soundness/principality/termination and production gates distinct.

## Review and integration

Freeze both author artifacts and dependencies before review. The fresh reviewer tests the named falsifiers and reports theorem scope, complete available axiom audit, implementation correspondence and omitted boundaries; no author self-review. Luna integrates only exact leased paths and synchronized compact state. Push only a coherent reviewed range to `origin/yulang3`; never force-push or disturb unrelated/unknown work.
