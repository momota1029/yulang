# Sprint R66 — test source Lambda staging before whole-ascription checking

Status: CANDIDATE only. No work is granted until Luna verifies the frozen
manifest and baseline, obtains the dispatcher start check, reconciles workers,
and activates this exact contract in `current.json`.

Branch / candidate baseline: `research/simple-sub-intrusion` /
`64f63ff01577155b892e658c5fbeb090dd4c451b`. Primary: `/root`.
Proposed session: `current-conversation-2026-10-19-r66`.
Parent: original computation-forwarding preservation §§1,6–7; unchanged source
domain and quantifiers; Simple-sub A/B OPEN 0→0; R50 NOT ADOPTED.
Immediate parent TODOs: `R65-CURRENT-OPERAND-1`, downstream
`R64-SRC-ANN-ARG-1`, original `R61-SOURCE-ASCRIPTION-FORMATION-1`.

## Fixed source and outcome

```yu
act io:
    our tick: int -> int

my forward (t:[io] int): [io] int -> [io] int = t
my outer (q:[io] int) = forward q
```

Determine whether the exact whole-binding annotation can be staged through an
ordinary symbolic Lambda operand while preserving the original joint source
context and permitted source solutions. The target staging is a proof question,
not a selected algorithm or source-rule amendment:

1. Retain the original formal annotation `p_t` and resolved body `Name(t)`.
2. Construct the symbolic Lambda operand and its prior source evidence, if an
   applicable existing Lambda/body-result rule permits that derivation at this
   annotated binding.
3. Add the whole-ascription obligations at their original owner and scope.
4. Show that this staged derivation has exactly the original joint source
   solutions and typed substitutions, or identify the first exact missing
   premise in the proposed factorization.

“Stage” must preserve one joint context. It must not solve the Lambda separately,
assume a completed `xi`, erase the whole annotation, equate an interior operand
to the final root, or choose witnesses after solving. Preserve original
`I,d,L,t,n`, provider, formal/whole/result annotation occurrences `p_t/p_A/p_R`,
open incoming `E`, permissions, ordinary constraints, body/result evidence and
all original scopes. Native inequalities cannot create source premises. Do
not assume `Sol_src`, `Corr`, actual `Q`, `Sol_nat`, solution lifting/reversal,
or substitution/transport beyond the local result actually derived.

Success is either a source-rule derivation of the staged equivalence at the
original binding, or the first exact premise the selected rules do not supply.
This is not a semantic ambiguity result: ambiguity requires two compatible
applicable derivations or a real conflict that changes an original observable.
Preservation concerns the original source coordinates, permitted joint
assignments and their evidence. Fresh auxiliary coordinates may be renamed or
related by an explicit witness transport; preserving an incidental naming or
assignment of newly introduced auxiliaries is not required.

## Method and falsifiers

**Proof lane:** compare the original whole-binding source rule with the proposed
factorization using a bidirectional elaboration argument. Start at actual
source syntax and rule owners; apply the formal/Name premises and selected
result-synthesis law at their declared scope; then attempt the Lambda operand
and whole annotation steps. Explicitly test whether the result rule applies
inside this whole-annotated binding. Keep every annotation and ordinary
constraint in one shared symbolic context. Prove both directions with the same
valuation, scoped witnesses, provider and typed substitutions, or stop at the
first authentic premise mismatch. Apply the result back to the original parent.

**Complementary Sol/medium attack:** independently seek a direct applicable
Lambda/checking clause or a counter-reading that invalidates the staging step.
Focus on expected-type dependence, scope order, annotation erasure, result
polarity and whether the joint context is circular. Do not propose new semantics
or repeat R65's approved bridge inventory.

**Luna/high source/native owner map:** trace the actual HIR source annotation,
formal/Name, Lambda and whole-binding owners through candidate construction,
preflight and consumers. Identify which owner could consume a staged source
operand and which required evidence each owner receives. Make no compiler edit;
decide whether any source-to-native code slice is justified by already approved
semantics. Do not change the negative-`p_A` guards.

Falsifiers: no existing rule allows the synthesis premise in this annotated
position; staging changes the set of permitted joint solutions; it loses
expected-type information, provider/permission/result evidence, or an original
constraint; context formation depends circularly on the desired operand;
`p_t` permission is borrowed for `p_A`; or a native comparison is promoted into
source evidence.

## Lanes, outputs and resource envelope

- Constructive proof, Sol/high, 900 seconds: write only
  `notes/theory/2026-10-19-r66-lambda-boundary-staging.md` and
  `tasks/agent-loop/inbox/20261019-r66-proof.md`.
- Complementary source-rule attack, Sol/medium, 300 seconds: write only
  `notes/progress/2026-10-19-r66-staging-counter-reading.md` and
  `tasks/agent-loop/inbox/20261019-r66-research.md`.
- Luna/high owner mapping, 500 seconds: Luna writes only
  `notes/progress/2026-10-19-r66-lambda-owner-map.md` and
  `tasks/agent-loop/inbox/20261019-r66-implementation.md`.
- Fresh independent compiler and spec reviews, 200 seconds each, after all
  author outputs are frozen.
- Luna integration and durable closeout, 300 seconds.
  Exact closeout: `notes/progress/2026-10-19-r66-closeout.md`; Luna also owns
  `tasks/agent-loop/current.json` and the required shared task-record sync.

Total: 2,400 seconds; Astra 0; no carryover. No implementation lane is
authorized because R65 and both reviews establish no safe code slice yet. The
owner map may identify an implementation prerequisite but cannot edit compiler
code, tests or semantics. This proof/source-owner packet must reduce the exact
parent obstruction; it is not a replacement success criterion for type
inference/evaluator implementation.

## Boundaries

No compiler, test, semantic, expected-output, build, execution, probe,
instrumentation, measurement or production change. No test runs are authorized.
The root operating instructions and task handoff are required operational
context: `AGENTS.md`, `AGENTS.pre-sprint.md`, `rules/agent-orchestration.md`,
`rules/research-lab.md`, `rules/design-authority.md`,
`notes/design/2026-10-16-goal-driven-sprints.md`,
`.agents/skills/yulang-sprint/SKILL.md`,
`.agents/skills/yulang-proofs/SKILL.md`,
`tasks/agent-loop/current.json`, and `tasks/agent-loop/README.md`. They do not
count as semantic evidence or dependency pins. For source/semantic evidence,
writers use only the frozen direct dependency manifest below; reviewers read
only the frozen contract, frozen author outputs and that exact manifest. Any
additional authority needed as semantic evidence returns to Luna before a read
or write.
Authors cannot start descendants, expand leases, extend budgets, stage/commit/
push or edit shared state. Reviewers are read-only. Luna alone adjudicates,
updates current/task records, stages explicit paths, and commits/pushes.

## Frozen direct dependency manifest

Every listed direct file must match its SHA-256 at activation, freeze and review.
This includes the prior reviewed result, its source authorities, and the actual
source/native construction owners inspected by the owner-map lane.

```text
ea9aac36ea152733b6c4babb7060f18b1e39d7516af5e90bf4d44deadec62d85  notes/progress/2026-10-19-r65-closeout.md
6222ed3f75e8299d2afbc3d7d869e055bf0bd81e78841074d5e7a6f89ad795aa  notes/theory/2026-10-19-r65-typed-root-pA-derivation.md
d70513dd369a653648ad75b2b5195f3736bbfd351ca959828d0dd3917f2de652  tasks/agent-loop/sprints/source-annotation-root-bridge-to-pA-20261019-r65.md
e64660cf79f52d5000468426dd9c1c794739b95d7a64b3cd183b5e4d1ad71c99  tasks/agent-loop/sprints/source-annotation-root-bridge-to-pA-20261019-r65-rev2.md
c53e7d4a1c791cd93f428af9c11572327e4b72a462fa3c311d5c1141d3d5b670  notes/progress/2026-10-19-r64-closeout.md
b8041fae28a4a88d7143ab6e16be6658ce156f3de90888667dded93e8b643772  notes/theory/2026-10-19-r64-whole-ascription-derivation.md
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md
7766aff08cedde1ebc796b8927cd1d44f459df72a632e0c0d35d4bfcd28d335e  notes/theory/2026-10-15-computation-formal-permission-construction.md
71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992  notes/design/2026-10-02-source-result-synthesis-choice.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38  notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240  notes/theory/2026-10-08-source-generalize-definition-and-proof.md
3cb57799e423f7c5036aa02e77e232b1924ecf3d8487c2649bb669d70da0e238  notes/design/2026-10-10-source-annotation-any-name-design.md
a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
766c3575dcded7dc2ed95de24e7c4dc97a1211494b683f2d0aac954f323c4222  questions/2026-10-10-source-annotation-typed-root-bridge/approved-answer.md
aa9cb81d91d265d9cb6e862f78fc2edab62e59b2d7802562cc863932bb315528  questions/2026-10-10-source-annotation-typed-root-bridge/receipt.md
7ff42d0a11f9b1535e9423d41c52ed51266b1712f4317e801949a9dda02f3cd6  questions/2026-10-10-source-annotation-typed-root-bridge/question.md
7c564a6e28c85059473b2c8498fdff72fd5f5e8f6378e9a8dce2780b63d69785  questions/2026-10-16-annotation-declared-envelope/approved-answer.md
8957bb5e0e1f306b0ba5f3b16e3f58fbc246316acb4fb9effde0527b2b7b5a58  questions/2026-10-16-annotation-declared-envelope/receipt.md
08eba1525b88e869dc9753d650240fc4e10e6cdc8cb17cca906a766b9463488d  questions/2026-10-16-annotation-declared-envelope/question.md
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c  notes/design/2026-10-08-call-source-interface-definition.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f  crates/yu-hir/src/module/source_annotation.rs
ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5  crates/yu-hir/src/module/local_source.rs
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c  crates/yu-solver/src/candidate_source.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb  crates/yu-solver/src/shadow_apply.rs
```
