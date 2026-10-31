# R82 — construct the existing R66 Root from primitive current evidence

Status: admitted bounded research sprint under the continuing Yulang soundness objective.

## Fixed outcome

Starting from the accepted R81 finite-record `Incidence` constructor, derive the existing R66 `Root` from primitive `Source`, `Inventory`, `Native`, and `Request` inputs. Preserve the exact R66 `Root` type and all original source/native coordinates. The proof must derive, not assume:

- source/native artifact equality and the original permission-entry/native-entry-row equation;
- the current physical slot, unique emission at that slot, matching admission, exact constructor readback, and current bound;
- relation pairing and positive effect-entry ownership;
- the source Value root and emitted Effect relation as distinct roles;
- the unique same-use Origin and completed source-drain receipt, including occurrence, task, selected/created relation, and empty incoming/replay evidence;
- every conjunct of R66 `BeforeAncestry`, then construct the original R66 `Root` and apply `source_incidence_checked` to the same R81 incidence.

Do not accept `Root`, `BeforeAncestry`, successful `readRoot`, aggregate physical ownership, successful ancestry, or a preassembled root as an input. Include a nonempty mixed Value-root/Effect-emission witness and rejection cases for duplicate physical emissions, stale current bounds, substituted admissions, incomplete/foreign drains, wrong occurrence/task, parameter-root substitution, and collapsed relation roles. Keep A/B claims and quantifiers unchanged.

## Exact assignments and leases

- Rust implementation (`implementer`, Luna/high): `crates/yu-solver/src/candidate_context.rs`, `crates/yu-solver/src/candidate_receiver.rs`, and `tasks/agent-loop/inbox/effect-permission-constructed-root-r82-rust.md`.
- Constructive Lean (`lean_prover`): `notes/theory/lean/YulangClosure/ConstructedPhysicalRootR82.lean` and `tasks/agent-loop/inbox/effect-permission-constructed-root-r82-proof.md`.
- Fresh independent reviewer after both authors freeze: `tasks/agent-loop/inbox/effect-permission-constructed-root-r82-review.md`.
- Primary Luna owns `current.json`, audit authorizations, adjudication, exact-path staging, commits and pushes.

Rust method: preserve the already-selected Origin index and borrowed Origin/drain records through the private checked-emission result and existing owner projection. Do not add a second independent root search or change lookup/ambiguity, ancestry direction, error variants, inference, routing, or subtraction behavior. Preserve failure distinctions and immutable-owner semantics.

Lean method: compose R81's actual constructor with executable indexed physical/root-record checks. Derive the exact R66 fields and ancestry witness. All theorem declarations must be reported with full type and transitive axiom census; no `sorryAx`, project axiom, `Classical.choice` or native-evaluation shortcut.

## Baseline and pins

Baseline is post-R81 closeout `ba568e576badc6826ae3b3f70bba5d609f559f74`. Exact source and dependency pins are in `effect-permission-constructed-root-20261031-r82-inputs-r1.json`. Any changed source pin or disagreement with R66/R81 stops the packet for Luna adjudication.

## Resources and restrictions

Fresh envelope: 6,000 seconds total (proof 2,600; Rust 1,000; review 1,200; primary 1,200 including 500 closeout); Astra 0. At most two separately committed and pushed exact-input Lean stdin audits, each at most 120 seconds. Each audit authorization is primary-owned and precedes that invocation.

Same checkout only; no new environment, worktree, scratch, cache, target, compiler, Cargo, tests, builds, formatter, Lake, or nested CLI. Do not delete or rewrite unrelated files. `git diff --check` and the static sprint checker are bookkeeping only. Preserve 32 pending items, all UNKNOWN worker observations and all quarantined path leases. Keep `current.json` at or below 16 KiB.

## Review and limits

Reviewer independently attacks the named falsifiers and verifies the actual R66 Root fields, R81 constructor composition, source/Rust evidence preservation, full theorem types, audit receipts, hashes, remaining assumptions, and exact frozen files. A bounded Root construction does not authenticate the finite tables as a Rust runtime instance. R79 `OrderedRoots` extraction, compilation/runtime, physical identity beyond checked records, original A/B, whole-language proof and production remain OPEN unless separately established by their governing gates. If proof audit fails, no theorem is accepted from it; preserve output and stop after the authorized audit cap.
