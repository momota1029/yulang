# Sprint PRIMITIVE-BOOL-RUNTIME-20261024 — source to runtime boolean primitives

Status: ACTIVE by Luna's current-state receipt.
Branch / baseline: `research/simple-sub-intrusion` / `e80b83f0f`.
Authority: `notes/design/2026-10-11-yulang-inference-top-level-principles.md`;
`notes/design/2026-10-20-r149-types-console.md`; pinned Yulang2 oracle at
`a58eefc31e22141574b6f20c6a5748151c6d79f1`.
Contract revision 1; current-state receipt records this file's SHA-256.

## Original outcome and success evidence

The unchanged parent goal is to implement Yulang type inference and evaluation
from the established proofs, then commit and push while leaving the worktree
clean. The original Simple-sub A/B claims and quantifiers remain unchanged.
This sprint takes one source-native increment on that path: connect the pinned
`builtin_op::{bool_eq,bool_not,bool_to_string}` identities through source HIR,
candidate type constraints, and the inference playground runtime.

The pinned source signatures are `bool -> bool -> bool`, `bool -> bool`, and
`bool -> str`, respectively. Runtime meaning is boolean equality, boolean
negation, and canonical `"true"`/`"false"` strings. These are fixed by the
oracle's `lib/std/bool.yu`, `crates/infer/src/builtin_ops.rs`, and
`crates/mono-runtime/src/lib.rs`. R149's source evidence records the standard
library bindings and exact oracle revision. The registered HIR primitive
identity, not spelling at runtime, must reach execution.

Success evidence:

1. HIR no longer classifies the three names as `Unsupported`.
2. Candidate source collection and primitive signature construction emit the
   matching Boolean/String leaves and curried types.
3. Runtime program construction retains the identity; primitive arity and
   application return the oracle-defined result for valid Boolean arguments.
4. A fresh reviewer finds no blocking or major source/constraint/runtime
   mismatch, and the affected crates compile.

No theorem or production gate is inferred from this increment. No test claim is
made. The source safety, permission adoption, whole-language BuildLocal,
principal inference, native correspondence, and original A/B obligations
remain open. The reviewed bounded §15 permission lemma is not used as authority
for these primitive semantics.

## Continuing lanes

Implementation owner: Luna / primary. The fixed path is
`source_annotation::pinned_primitive_op` → `LocalSourceForm::Primitive` →
`candidate_source::Action::Primitive` and its primitive leaves →
`candidate_effect::candidate_pinned_primitive` → runtime `Instruction::Primitive`
→ `pinned_primitive_arity` / `pinned_primitive_apply`.

Complementary proof/source owner: compiler referee, read-only audit of the
pinned source signatures, primitive type constructors, and runtime meanings.
It does not author code or extend semantics. Luna applies the result to the
source/native correspondence row. Fresh code review is assigned after the
implementation diff is frozen.

Permitted follow-up within the same envelope: compile the affected crates,
obtain independent review, repair findings within the leased files, record the
exact source-to-runtime correspondence, and prepare an explicit-path commit.
Adding other primitive families, changing source/effect permissions, or
expanding the standard-library loader is outside this sprint.

## Permissions and resources

Read-only authorities and evidence: the two R149 design/evidence documents,
the top-level inference principles, the three named oracle source files, and
the existing operational/source/dot-selection manuscripts. No manuscript is
rewritten or treated as production approval.

Exact write leases: this sprint contract; its paired
`primitive-bool-runtime-20261024-outcome.md` outcome; `tasks/agent-loop/current.json`;
`crates/yu-hir/src/module/source_annotation.rs`;
`crates/yu-solver/src/candidate_source.rs`;
`crates/yu-solver/src/candidate_effect.rs`;
`tools/inference-playground/src/runtime/machine.rs`.
No test, fixture, expectation, unrelated untracked, or quarantined path is
leased. Existing unknown writers and all pre-existing untracked files retain
their recorded owners and reservations.

Maximum active sprint time: 3600 seconds; one implementation owner and one
read-only complementary assignment, with review reserve. No Astra assignment.
One Cargo check is the sole heavy process. No tests or executable probes are
authorized by this contract. Stop on a signature/behavior ambiguity, changed
authority or dependency hash, expanded lease need, reviewer blocking finding,
or resource limit.

## Frozen seam and integration

The reviewer receives frozen hashes for the four leased Rust files and direct
R149/oracle dependencies. Acceptance requires checking all three operations
from resolved source identity through candidate constraints and runtime
application, with mismatched primitive identities remaining unsupported.
Incomplete whole-language and effect-safety gates remain open.

Only Luna stages the exact leased implementation and sprint receipt paths,
reviews the complete outbound range, commits, and pushes without force. The
clean-tree goal remains conditional on preserving pre-existing untracked files
whose writer cessation or ownership is not resolved; no cleanup or blanket
staging is allowed.
