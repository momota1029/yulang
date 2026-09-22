# F5c scheme-closure handoff — 2026-09-22

## Resume point

Branch `yulang3` is clean at `753a97e1` (`feat(solver): distribute nested
F5c products`). The branch is ahead of `origin/yulang3` by the current F5c
slice commits and has not been pushed. Resume the approved F5c general-scheme
closure gate; do not treat the gate as complete.

The latest user decision keeps normalized-union option 1: an incoming closed
positive Union uses its canonical first normalized member as the one public
source-fact representative, while all remaining members are private live
decomposition constraints under the same occurrence cause.

## Governing authority

- `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md`
  §§22, 24, 25, 32, 33, 43, and 44.
- §43 records the approved private closed-extreme Term nodes and zero fresh
  Q/R allocation for structural extremes.
- §44 records the approved normalized-union representative fact and retains
  the requirement that representative publication plus every private member
  constraint be one transactional route operation.
- `tasks/current.md` is navigation only; this handoff is the active resume
  record for the current F5c slice.

## Completed in this slice

`crates/yu-solver/src/term.rs` now has private `PositiveBottom`, `NegativeTop`,
and `NegativeBottom` nodes and the exact corresponding `TermView` variants.
They are structural closed extremes, not fresh live variables.

`crates/yu-solver/src/lib.rs` now includes:

- polarity census and normalized Union/Intersection generalization drafts;
- bipolar Q and guarded self/opposite-polarity R witnesses;
- draft-before-install component publication ordering;
- fresh Q/R incoming substitution and lower-before-upper R restoration;
- one public representative route/fact for a normalized positive Union;
- private member constraints under the source occurrence/cause;
- public-store fact/canonical-key cleanup when representative admission or
  provenance injection fails;
- recursive product expansion through nested positive Union and negative
  Intersection Function children.

The focused F5c coverage includes bipolar census, direct and multiple bounds,
guarded R, finalizer round-trip, normalized-union routing, representative
failure cleanup, and nested product instantiation.

## Confirmed review state

The post-repair semantic delta review closes the previous nested product
instantiation blocker: positive Function children distribute
negative-argument parts × positive-result parts, and the negative dual does
the same with polarity preserved. The performance delta review found no
material successful-path regression in the localized public-store rollback or
route staging.

The specification delta review still has one blocking finding: private live
constraints are admitted before the public representative, but if public
admission/provenance then fails, typed-pair memo, bounds, frontier/diagnostic
state, logical counters, and other private session mutations remain. The
current focused failure witness checks only public facts/provenance/route
absence; it does not prove complete private-state restoration.

Other open F5c gates remain:

- component-scoped iterative summary sharing and stack-safe expansion;
- complete ineligible-variable rejection without fallback extremes or panic;
- closure of non-pure Function effects;
- closed-DAG instantiation memoization and resource accounting;
- end-to-end per-use failure rollback across every availability lane.

Do not claim F5c completion or F5e resource/public-observation certification.

## Immediate next action

Implement a bounded transactional checkpoint/rollback for the incoming
normalized-Union route, or an equivalent full preflight that proves the same
atomicity. The checkpoint must cover the private live algebra and public route
state together: typed-pair memo and diagnostic delta/scratch, value/effect
bounds and extrusion work, errors, relevant logical counters, store facts,
canonical entries, provenance/receipts, and routed-use markers. Preserve the
approved first-member representative projection; do not introduce a live
Union Term or silently weaken §44.

Add a failure witness with two canonically distinct Union members that records
the complete relevant pre-state and asserts restoration after a later private
or representative-public failure. Use the smallest safe focused checks first,
then rerun the single-threaded `yu-solver` library suite at the coherent gate
boundary.

## Verification already passing

- `cargo fmt --check`
- `cargo check -p yu-solver --tests`
- `cargo check --workspace`
- `cargo test -p yu-solver --lib f5c_ -- --test-threads=1`
- `cargo test -p yu-solver --lib --no-default-features -- --test-threads=1`
  — 91 passed
- `git diff --check`

No benchmark or F5e 1k/2k/4k resource matrix was run. The last independent
review set was the focused semantic/specification/performance delta review;
the primary must adjudicate any new findings before another repair pass.

## Repository-policy note

`AGENTS.md` now explicitly states that subagents are the primary working
mechanism for bounded role-shaped exploration, implementation, and review,
while the primary retains authority, user interaction, adjudication, records,
and git integration.
