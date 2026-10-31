# R76 Rust source-choice handoff

Sprint: `EFFECT-PERMISSION-SOURCE-CHOICE/20261031-R76`  
Lane: `/root/r76_rust`  
Disposition: **IMPLEMENTED, STATICALLY REVIEWABLE; WRITES STOPPED**

## Contribution

Added `ReceivingResidualExperiment::internal_owner_choice` in
`crates/yu-solver/src/candidate_receiver.rs`. It returns a private borrowed
choice assembled directly from the experiment's definition-use, source-call,
formal-registration, Lambda-origin, Lambda-recipe, parameter-recipe, and
component inventories. The derivation does not call
`internal_formal_permission_incidence`, consume an already selected
registration, or use a shared Function/row as a filter.

The use is selected by the source receiver/target definition roots and one
exact source-call occurrence in the receiving owner's LocalSource. The
construction retains the use ID and record, call index and record, source and
target owner coordinates, both component indices and terms, selected origin
index and record, registration index and record, Lambda-recipe index and
record, parameter-recipe index and exact parameter ID, and the formal's
`native_root` separately from the registered Lambda root read through the
recipe's root component.

## Selection order and correspondence

Before scanning owners, the constructor checks the use/cause/occurrence
identity, the unique Internal route, and its exact slot-zero fact and endpoint
terms. It then scans the full ordered Lambda-origin table. Out-of-range
registration indices are skipped as in the native loop. Each in-range
computation formal owned by the exact target definition must have exactly one
Lambda recipe **before** the recipe root component is compared with the use's
target-root component. A missing or duplicate recipe fails immediately,
including for an eligible origin earlier than the eventual selected origin.
The scan fails on a second matching origin. It then rechecks the exact
selected registration/recipe identity and Lambda occurrence, verifies the
parameter recipe at the registration's exact `recipe_position`, validates the
source Lambda and parameter, and confirms there is one Lambda origin for that
registration.

This follows the order in `lib.rs::InferenceSession::internal_formal_permission_incidence`
and the actual R66 `ownerSelection` definition: registration owner and role,
recipe cardinality, target-root component, then global uniqueness. The R76
Lean lane is responsible for proving the finite R55 owner-selection model
corresponds to the actual R66 function. This Rust constructor is source-side
evidence only; it does not derive physical root/emission ownership, genuine
R66 `Root`, native execution, original A/B, or production authority.

The existing `SourceInternalProjection::capture` still consumes the native
incidence helper. This new method is separate so that the plan and owner
choice have a constructor that does not take that result as a premise. No
consumer is connected and no ordinary inference or routing behavior changed.

## Evidence reused and rejected

- Reused R55's primitive `Use`, `Plan`, `Formal`, `Construction`, `Recipe`,
  and `Native` inventory roles, R66's exact ordered `ownerSelection`, and the
  native loop's route and origin scan at `lib.rs:18281`.
- Reused the reviewed R75 source evidence that formal source-root and emission
  relation IDs have distinct roles. R75 does not establish plan uniqueness or
  global formal-owner selection.
- Rejected the old R55/R66 path through `sourceProbe` as a constructor for
  this obligation: it starts from a supplied query/plan path and uses
  `ownerSelection` as an operation, rather than constructing the exact plan
  from Rust's source-owned DefinitionUse and call inventories.
- Inspected existing source tests around exact DefinitionUse cause identity
  and multiple-use identity (`lib.rs:22900` and `:28249`). They are static
  source evidence only; no tests were run or changed.

## Diff and verification

Exact changed paths:

- `crates/yu-solver/src/candidate_receiver.rs`
- `tasks/agent-loop/inbox/effect-permission-source-choice-r76-rust.md`

No other path was written. No scratch or disposable output was created.
`git diff --check` is the only requested check for this lane; no Rust
compiler, Cargo, tests, formatter, Lake, build, environment, worktree, cache,
target, or generated output was run or created. This code has **not** been
compiled or independently reviewed.

Frozen authority:

- Contract: `tasks/agent-loop/sprints/effect-permission-source-choice-20261031-r76.md`
  SHA-256 `87325ab223af0e98a6ca8c78162ead6ba1d72403b318342d155ee5dd55069936`.
- R1 inputs: `tasks/agent-loop/sprints/effect-permission-source-choice-20261031-r76-inputs-r1.json`
  SHA-256 `33a8769ab21ded37b85e436b90fe67f12ab8561eb2ffd0e90fe754acc23bb0dd`.
- Baseline: `9b523f587cf1e8cf2142ede750fa85121876d415`.
- Requested model/effort: Luna/high. The execution environment did not expose
  an independently observable model/effort receipt.
- Budget used: below the 1000-second Rust-lane bound.

Next related in-envelope step: independent review of the exact source diff and
Rust handoff against R66 failure order and the required counterexamples. This
lane is **STOPPED / WRITES STOPPED** pending primary coordination.
