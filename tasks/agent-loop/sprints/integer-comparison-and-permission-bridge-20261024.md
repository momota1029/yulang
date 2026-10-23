# INTEGER-COMPARISON-AND-PERMISSION-BRIDGE-20261024

Status: ACTIVE under the existing user goal. This is a bounded implementation
and source-correspondence sprint; it does not close the full inference/evaluator
goal or adopt the source manuscript's permission candidate.

Branch: `research/simple-sub-intrusion`

Baseline: `d0015dd930f9dfc8df165d4a719a72382c153f13`
Selector boundary: `/root/next_action_selector` returned this next outcome after
the Boolean slice checkpoint. Luna retains authority over contract, leases,
review and Git.

## Original outcome and success evidence

The original user goal remains: use established proofs and approved source
behavior to implement Yulang type inference and evaluator, commit and push, and
keep the worktree clean. No A/B claim, quantifier, source domain, semantic gate,
or open question is narrowed by this sprint. The type/evaluator objective and
the source-safety parent both remain open after this bounded increment.

Implementation outcome: carry the complete pinned integer comparison family
`int_eq`, `int_lt`, `int_le`, `int_gt`, `int_ge` from exact HIR source identity,
through candidate source constraints and curried primitive annotations, to
runtime application over arbitrary precision signed integers. Oracle behavior
is mathematical signed equality/order and returns Boolean. Do not parse through
a machine integer or floating-point representation.

Success requires all five exact source names to reach their matching primitive
identity, `Int -> Int -> Bool` candidate and annotation paths, binary runtime
arity and execution, including negative results and zero normalization. A
bounded `cargo check -p yu-hir -p yu-solver -p yu-playground` and fresh
independent review of the frozen source-to-runtime diff are required. No tests,
expected-output changes, runtime probes, or broad evaluator claim are implied.

Before-state: HIR marks all five names Unsupported; candidate generation has no
Int-to-Bool primitive leaf; candidate annotations and runtime do not implement
the family. After-state must be established from the frozen diff and compiler
check, not inferred from a test count.

The independent proof/source lane audits the repaired permission candidate in
the source manuscript and its §§10–11 dependencies against the actual current
implementation owners. Its result is one exact correspondence handoff or a
source-qualified counterexample applied to the existing source-safety parent.
It cannot approve semantics, close that parent, or authorize a code change.

## Frozen authority and dependencies

Approved source meaning for primitives: Oracle commit
`a58eefc31e22141574b6f20c6a5748151c6d79f1`.

- `crates/infer/src/builtin_ops.rs`, Git blob
  `2fcddfe8015df988e7c05ce23651c63467719d96`: `int_eq`, `int_lt`, `int_le`,
  `int_gt`, and `int_ge` each use `BinaryPredicate { param: "int" }`.
- `crates/evidence-vm/src/runtime.rs`, Git blob
  `a91ce6c11a57dd14d80caa6b217d54b7f9adc70a`: the five operations compare the
  two integer values with signed `==`, `<`, `<=`, `>`, `>=`, and return Bool.
- Oracle checkout has unrelated working-tree changes. The authority above is
  the pinned commit content; do not use modified checkout bytes as authority.

Prior compiler baseline and exact starting SHA-256 values:

- `crates/yu-hir/src/module/source_annotation.rs` —
  `b7094dac5b277cf2efe39bd33d4f0d2301071b6ca96260887822575663dbcd89`
- `crates/yu-solver/src/candidate_source.rs` —
  `70c29b9e489b6ea17ecbee6610c0b256feacb92c90f87ba6c452b56cf0daf0a7`
- `crates/yu-solver/src/candidate_effect.rs` —
  `d7bebf24a823ccd56ceb200ff6e9915e4b81c4fad0e4ad77d6ad6d5043e454f9`
- `tools/inference-playground/src/runtime/machine.rs` —
  `30c83d44623ceae1951091745bf15d6025eca2b64bfbc33ae2bf31b5f8118b75`
- `tools/inference-playground/src/runtime/decimal.rs` —
  `b211ef1ea2c26e64a19b15c498d6c8202fe5ba7115401726fae68bdef7c9d009`

Pinned proof inputs, unchanged at sprint start:

- `docs/yulang-source-type-safety-ja.tex`, SHA-256
  `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`; especially the repaired
  permission candidate in §15 and its actual source construction/dependencies
  in §§10–11.
- `docs/yulang-operational-type-safety-ja.tex`, SHA-256
  `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
- `docs/yulang-dot-selection-safety-ja.tex`, SHA-256
  `47b7fcec1f501e7c326ab9859885e329aab2730066806ea79212e825ebb32b0b`; retained
  as a neighboring proof input, not authority to change resolver semantics.
- Existing gate: `SOURCE-SAFETY-BRIDGE` remains `OPEN_REVIEW`; the release
  outcome records that permission adoption and complete source/native
  correspondence remain open. The wildcard repair is a candidate, not adopted
  behavior.

## Two continuing lanes

### Implementation — Luna / primary

Exact write leases:

- `crates/yu-hir/src/module/source_annotation.rs`
- `crates/yu-solver/src/candidate_source.rs`
- `crates/yu-solver/src/candidate_effect.rs`
- `tools/inference-playground/src/runtime/machine.rs`
- `tools/inference-playground/src/runtime/decimal.rs`

The decimal helper may implement signed comparison by normalizing with existing
`parts`, comparing magnitude length and digits, then reversing magnitude order
for negative values. Keep zero nonnegative. Preserve fallible behavior and avoid
machine-width conversion. These are the only implementation write paths.

Falsifiers: negative ordering reversed; `-0` differs from `0`; large values
truncate; wrong result leaf/type; wrong primitive identity or annotation arity;
partial application has wrong arity; runtime accepts a non-integer argument or
returns a non-Boolean result.

### Proof/source correspondence — `/root/source_permission_review`

Exact write leases:

- `notes/theory/2026-10-24-permission-implementation-bridge.md`
- `tasks/agent-loop/inbox/20261024-permission-implementation-bridge.md`

Inspect source manuscript §15's wildcard repair and its §§10–11 construction,
then identify the exact current source constructors, generated candidates and
consumer/runtime owners that would have to implement that candidate. Return an
implementation correspondence with every missing premise, or one finite
source-qualified counterexample to the original source-safety parent. Preserve
receipt, receiver, scope and evidence identities across raw resume; do not
identify type equality with permission, erase a foreign protection under a
wildcard, or treat a permission candidate as adopted language meaning. No Rust
edits or extra file outputs are leased to this lane.

The lane's assignment cap is 1500 active seconds; total sprint active-work cap
is 3600 seconds. Requested role is read-only source/proof review. Requested and
observed model/effort remain separate; missing runtime metadata remains
UNKNOWN. If no exact live launch/receipt is returned, record NOT_STARTED (the
assignment is not a launch) rather than RUNNING and continue primary-owned
implementation.

## Permissions, review and resources

Primary-owned write paths are the five implementation files above, this
contract, its paired outcome, and `tasks/agent-loop/current.json`. The proof
lane owns only its two exact outputs. All other compiler and proof files are
read-only. Any additional source path or semantic change returns to Luna for a
versioned contract revision before writing.

Resources: ≤3600 active seconds total, ≤1500 for the proof/source assignment,
zero Astra. Preserve four UNKNOWN reservations and their quarantined leases;
with the primary and one proof assignment the six-assignment envelope is full.
Reserve fresh review/integration capacity. One heavy compiler process at a
time. The primary owns the single bounded Cargo check; no tests or probes are
authorized by this contract.

Freeze implementation bytes and direct dependencies before independent review.
The code author is Luna. A fresh reviewer must not author the implementation;
the proof/source contributor may review only the distinct code artifact after
its own handoff is frozen and it confirms no code writes. Blocking or major
implementation findings must close before acceptance. The permission note gets
its own review and remains a research candidate until source/native evidence and
semantic adoption are separately authorized.

Stop at the coherent reviewed implementation checkpoint, a source-qualified
counterexample, a real authority/dependency boundary, the budget bound, user
STOP, or session end. Unknown writers keep their leases. Integrate only exact
accepted paths with a non-forced push. Preserve all pre-existing untracked
paths; no cleanup authority is created here.

## Parent application and remaining gates

Integer comparisons add ordinary inference/evaluator capability but discharge
no effect, profile, source hygiene, parser/module, or full-language obligation.
The source permission lane applies its result to the existing
`SOURCE-SAFETY-BRIDGE` gate. Even a correct bridge leaves full source/native
coverage, semantic adoption, and the original parent theorem/open A/B obligations
separate. The next dispatcher consultation is at a material counterexample,
authority/dependency/lease/resource change, cross-lane seam, or sprint boundary.
