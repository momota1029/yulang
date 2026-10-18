# Sprint R67 — direct Lambda checking for the original whole-annotated binding

Status: CANDIDATE only. No work is granted until Luna verifies this exact
manifest and baseline, obtains the dispatcher start check, reconciles all
identities/leases, freezes the contract and activates it in `current.json`.

Branch / candidate baseline: `research/simple-sub-intrusion` /
`3b974b9337d8490e1af2ebaa5f1b54ece2e62cd5`. Primary: `/root`.
Proposed session: `current-conversation-2026-10-19-r67`.
Parent: original computation-forwarding preservation §§1,6–7; unchanged source
domain and quantifiers; Simple-sub A/B OPEN 0→0; R50 NOT ADOPTED.
Upstream OPEN items: `R66-LAMBDA-RESULT-STAGE-1`,
`R65-CURRENT-OPERAND-1`; downstream `R64-SRC-ANN-ARG-1` and
`R61-SOURCE-ASCRIPTION-FORMATION-1`.

## Fixed source and outcome

```yu
act io:
    our tick: int -> int

my forward (t:[io] int): [io] int -> [io] int = t
my outer (q:[io] int) = forward q
```

Attempt to construct the original symbolic Lambda operand directly through
the selected source Lambda, Parameter, resolved Name, Result/checking and
designated-consumer rules. Retain the actual formal entry, original captures,
body checking under the actual `t` binding, body consumer and complete
invocation return. Derive the symbolic Function interface and its evidence at
their authentic source owners before using that interface in any whole-type
check. Return the actual operand and prior evidence to the original
whole-binding annotation boundary, or identify the first exact unsupported
local premise.

This is the direct-checking route after R66; it must not replace the Lambda
body-checking premise with Result-A's unannotated Lambda synthesis equation.
The Function interface is a proof target, not an assumed type, successful
check, generated `xi`, or source rule amendment. Preserve the original
`I,d,L,t,n`, provider, formal and whole/result annotation occurrences
`p_t/p_A/p_R`, open incoming `E_t`, permissions, captures, ordinary
constraints, body/result evidence and original scopes. All evidence and
alternatives stay in one joint source context. Do not solve the Lambda
separately, assume a completed `xi`, borrow `p_t` permission for `p_A`, erase
the whole annotation, equate an interior operand to the final root, or choose
witnesses after solving. Fresh auxiliary coordinates may be hygienically
renamed or transported with their dependencies; incidental auxiliary names
need not be preserved. Native constraints do not create source premises.

Success is either a direct source-rule derivation of the completed operand
and prior evidence at this original binding, or the first authentic premise
the selected rules do not supply. This does not attempt to derive all of
`p_A`, R64/R61 correspondence, actual `Q`, `Sol_nat`, full `Corr`, production
admission, or a new semantic decision. No source range, semantics, compiler,
test or expected output change is authorized.

## Method, falsifiers and R66 boundary

**Proof lane:** use the independent source-checking grammar in
`source-generalize-definition-and-proof.md` §§3.1–3.2 at the original source
occurrences. Construct the authentic formal entry and `Name(t)` derivation,
then apply the actual Lambda body-checking, body-consumption and invocation
premises. Show how the symbolic Function interface, body/result relation and
typed evidence are formed before whole-annotation checking; do not set it to
`Fun(P,Result(I))` by Result-A unless an applicable direct checking rule proves
that equality here. Keep all local checking alternatives and ordinary
constraints in the original joint context. Preserve provider, scopes and
typed substitution/witness dependencies. Either show the exact bridge input
required by R65 or name the first unsupported local clause.

**Complementary source-rule attack, Sol/medium:** independently inspect direct
Lambda checking, Function challenge/observation checking, actual body
consumer and invocation-return premises. Seek a circular interface, assumed
body safety, a fresh expected-type choice, omitted formal permission or
missing invocation evidence. Falsify any proposed derivation with an actual
original premise mismatch. Do not rely on Result-A to fill a direct checking
gap and do not repeat R66's already reviewed conditional cut.

**Luna/high owner map:** trace formal/Name/Lambda/body/invocation source
owners through HIR and candidate construction/consumers. Identify what
evidence the native path receives and where direct typed source evidence would
be consumed. Preserve both negative-concrete `p_A` guards. No compiler edit;
decide whether already reviewed source rules justify any code slice.

Falsifiers: the selected Lambda rule does not construct a symbolic operand at
this boundary; its Function interface depends on the whole annotation before
its own formation; a body consumer or invocation-return proof is absent or
guessed; formal `p_t` permission migrates to `p_A`; source provider, `E_t`,
captures, ordinary constraints or result evidence are lost; joint witnesses
are selected after a solve; or native comparisons are promoted to source
judgments.

## Lanes, outputs and resource envelope

- Constructive direct-checking proof, Sol/high, 900s:
  `notes/theory/2026-10-19-r67-direct-lambda-checking.md` and
  `tasks/agent-loop/inbox/20261019-r67-proof.md`.
- Complementary rule attack, Sol/medium, 300s:
  `notes/progress/2026-10-19-r67-checking-counter-reading.md` and
  `tasks/agent-loop/inbox/20261019-r67-research.md`.
- Luna/high source/native owner map, 500s:
  `notes/progress/2026-10-19-r67-lambda-operand-owners.md` and
  `tasks/agent-loop/inbox/20261019-r67-implementation.md`.
- Fresh independent compiler and spec reviews, 200s each, after every author
  output is frozen.
- Luna integration and durable closeout, 300s:
  `notes/progress/2026-10-19-r67-closeout.md`; Luna owns
  `tasks/agent-loop/current.json` and the shared task-record sync.

Total 2,400s; Astra 0; no carryover. No implementation lane is authorized;
R66 established `NO_SAFE_CODE_SLICE`. The owner map cannot edit compiler code,
tests or semantics. This packet must make direct progress on the original
operand obligation; an exact unsupported premise is a bounded result, not
completion of the broader type-inference/evaluator objective.

## Boundaries

The fixed source, source domain and original parent quantifiers do not change.
No compiler, test, expected-output, semantic, build, execution, probe,
instrumentation, measurement or production change. No test runs are authorized.
Required governance/startup reads are operational context, not source evidence:
`AGENTS.md`, `AGENTS.pre-sprint.md`, rules `agent-orchestration.md`,
`research-lab.md`, `design-authority.md`, sprint decision
`notes/design/2026-10-16-goal-driven-sprints.md`, skill `yulang-sprint`,
skill `yulang-proofs`, `tasks/agent-loop/current.json`, and
`tasks/agent-loop/README.md`. For semantic evidence, authors/reviewers use only
the frozen direct dependency manifest below. Any further semantic authority
returns to Luna before a read or write.

Authors cannot start descendants, expand leases, extend budgets, stage/commit/
push or edit shared state. Reviewers are read-only. Luna alone adjudicates,
updates current/task records, stages explicit paths, and commits/pushes.

## Frozen direct dependency manifest

Every direct file below must match its SHA-256 at activation, each author
freeze and review. This packet includes the reviewed R66 result, every R66
author artifact/handoff and its underlying source owners; it does not treat an
R66 conditional result as the missing direct Lambda derivation.

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
0af68443b372f1407f68e0b9f21194348b469f8c5d3dce06a8cd98ed976e6f01  notes/progress/2026-10-19-r66-closeout.md
7ee35d3d66b2acd0c5115a75e7a8125bd136df98308dfc61dbc6d205a8e433e4  tasks/agent-loop/sprints/lambda-boundary-staging-20261019-r66.md
dffc0e0ad0cd9e453e2f28340856a4eba31f147028af867249e18873ad302705  notes/theory/2026-10-19-r66-lambda-boundary-staging.md
beb821e8de9b4264a66d3176f7b236cc8abc442ac515b2f0e01433ebc1f1dbe2  tasks/agent-loop/inbox/20261019-r66-proof.md
ca53ec252b4af8612fb88e0ee1d04f566eeb6f252796284574e77c933535275f  notes/progress/2026-10-19-r66-staging-counter-reading.md
9e5dede065a51d5fcd8ae99ce173ffcc95e393ef18be15322d954a189925bd5e  tasks/agent-loop/inbox/20261019-r66-research.md
51c48d1f69520878a586e159315b9f955667dfe002a4cc50992028752bccc5d8  notes/progress/2026-10-19-r66-lambda-owner-map.md
4d6130f063c940816db297d417a800804b7cfe2da5bf380bd7645f4470956c29  tasks/agent-loop/inbox/20261019-r66-implementation.md
```
