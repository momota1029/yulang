# Sprint R65 — test the approved source-annotation root bridge against p_A

Status: CANDIDATE only. No work is granted until Luna verifies this manifest
and clean baseline, obtains a dispatcher start check, reconciles workers, and
activates this exact contract in `current.json`.

Branch / candidate baseline: `research/simple-sub-intrusion` /
`8a3ba2ae6e82a052cdbe2ff12f4c79183314755b`.
Primary: `/root`; proposed session: `current-conversation-2026-10-19-r65`.
Parent: original computation-forwarding preservation §§1,6–7; original source
domain/quantifiers and Simple-sub A/B unchanged; OPEN 0→0; R50 NOT ADOPTED.
Parent TODO: `R61-SOURCE-ASCRIPTION-FORMATION-1`.
Exact child: `R64-SRC-ANN-ARG-1`.

## Fixed source and targeted question

```yu
act io:
    our tick: int -> int

my forward (t:[io] int): [io] int -> [io] int = t
my outer (q:[io] int) = forward q
```

Determine whether the already approved source-annotation typed-root bridge
and declared-envelope decisions, together with the pinned call-view and
annotation-polarity authorities, derive the whole-ascription argument
interpretation identified in R64. The target is exact:

```text
R64-SRC-ANN-ARG-1:
  derive the typed interpretation of whole-ascription p_A on the original
  Lambda/formal incoming computation carrier, with p_A's own permission and
  scope, under the original joint component context, preserving the distinct
  p_t/Name evidence and all ordinary constraints.
```

Start from the R64 D0–D2 prefix and reproduce the source-argument premises.
Then instantiate each approved judgment at its authentic owner/position and
test whether it supplies the missing typed interpretation. The result must be
either a derivation from the approved rule clauses, or the exact first clause
that the rules do not supply and why. It may identify a concrete unresolved
semantic choice only if two applicable derivations or an actual conflict show
that existing decisions do not determine the meaning. Missing documentation
alone is not semantic ambiguity or an approval gate.

Construct source constraints before native inequalities. Do not assume a
completed joint `xi`, `Sol_src`, `Corr`, actual `Q`, or checking/exposed
correlation. Preserve original `I,d,L,t,n`, distinct `p_t/p_A/p_R`, open
incoming `E`, permissions, ordinary constraints and scopes. Do not apply R60
unless its actual-Q premise is proved. Native guards remain unchanged.

## Method and falsifiers

**Proof lane:** follow each clause of the approved typed-root bridge, declared
envelope, source-result policy and selected annotation policy. Make the
definition/root ownership step explicit, then the Function child/argument
step, then the original Lambda/formal incoming-carrier and joint-context
step. Do not treat a whole-root endpoint as an argument port unless a rule
derives that path. For every premise, cite its approved clause and original
source identity. Stop on the first clause whose authentic rule premises do
not match the fixed source.

**Complementary source/spec lane:** independently inventory the same approved
question answers and the exact meaning/owner of each premise. Seek a direct
counter-reading or overlooked clause that either supplies the argument port
and permission lineage or shows it is outside the rule's stated scope. Do not
propose new semantics or repeat a HIR crosswalk/API validation.

Falsifiers: the bridge only types a root endpoint and does not provide the
argument child; the bridge assumes an already-typed child/permission; the
declared envelope is only a public/effect bound; the derivation borrows p_t's
permission for p_A; joint context is assumed rather than formed; provider,
position, scope, ordinary constraints or result evidence changes; native
comparison is used to create source evidence; or a proposed semantic fork
violates another approved decision.

## Continuing lanes and outputs

- Configured prover / Sol high, 600 seconds: apply the approved rules to the
  exact R64 clause, construct the derivation or first failed premise, and apply
  it back to the original parent. Write only
  `notes/theory/2026-10-19-r65-typed-root-pA-derivation.md` and
  `tasks/agent-loop/inbox/20261019-r65-proof.md`.
- Complementary researcher / Sol, 500 seconds: independently map approved
  source-rule ownership and test for an omitted clause or exact counter-reading
  at the original p_A carrier. Write only
  `notes/progress/2026-10-19-r65-spec-owner-map.md` and
  `tasks/agent-loop/inbox/20261019-r65-research.md`.
- Fresh independent compiler and spec reviews, 200 seconds each, after both
  authors stop and freeze all four outputs. The compiler reviewer checks
  source/native scope and guard boundaries; the spec reviewer checks exact
  approved-rule applicability, hidden premises and authority limits.
- Luna integration, 300 seconds, writes only
  `notes/progress/2026-10-19-r65-closeout.md`, updates
  `tasks/agent-loop/current.json`, and owns Git. Total candidate allocation:
  1800 seconds; Astra0; no carryover.

No implementation lane is included: R64's reviewed owner boundary and source
guards leave no safe code slice before this source rule is derived. This is a
source-spec proof packet, not another native constructor or API audit.

## Boundaries

No code/semantic/test edits, tests, builds, execution, probes, instrumentation,
measurements, source-domain narrowing, accepted-output change, or production
claim. Do not alter the approved answers or question-board state. Any authority
conflict, unpinned dependency, lease expansion, new semantic choice, or need
for an implementation path returns to Luna. Authors cannot create descendants,
expand resources, read outside these pins, or stage/commit/push. Reviews are
fresh and read-only. The primary must preserve the exact original parent and
all independent quantifiers; a local p_A clause alone closes no parent theorem.

## Frozen dependency manifest

These 16 direct SHA-256 dependencies are pinned at the candidate baseline and
must all match before activation:

```text
c53e7d4a1c791cd93f428af9c11572327e4b72a462fa3c311d5c1141d3d5b670  notes/progress/2026-10-19-r64-closeout.md
b8041fae28a4a88d7143ab6e16be6658ce156f3de90888667dded93e8b643772  notes/theory/2026-10-19-r64-whole-ascription-derivation.md
ca77147a62dc1a43f5cbecacf09a0203add761f235b46998d1ef41255bc7ecc7  tasks/agent-loop/inbox/20261019-r64-proof.md
2f008cc535a4db8da53fc40acac6ae5750d25083be6d6abe4a5ee35f318576bf  tasks/agent-loop/sprints/whole-ascription-derivation-20261019-r64.md
f29635c1dbccb0e6478ace00a47209684740a32c15a1426610221dca2e21bc8d  tasks/agent-loop/sprints/whole-ascription-derivation-20261019-r64-rev2.md
766c3575dcded7dc2ed95de24e7c4dc97a1211494b683f2d0aac954f323c4222  questions/2026-10-10-source-annotation-typed-root-bridge/approved-answer.md
aa9cb81d91d265d9cb6e862f78fc2edab62e59b2d7802562cc863932bb315528  questions/2026-10-10-source-annotation-typed-root-bridge/receipt.md
7ff42d0a11f9b1535e9423d41c52ed51266b1712f4317e801949a9dda02f3cd6  questions/2026-10-10-source-annotation-typed-root-bridge/question.md
7c564a6e28c85059473b2c8498fdff72fd5f5e8f6378e9a8dce2780b63d69785  questions/2026-10-16-annotation-declared-envelope/approved-answer.md
8957bb5e0e1f306b0ba5f3b16e3f58fbc246316acb4fb9effde0527b2b7b5a58  questions/2026-10-16-annotation-declared-envelope/receipt.md
08eba1525b88e869dc9753d650240fc4e10e6cdc8cb17cca906a766b9463488d  questions/2026-10-16-annotation-declared-envelope/question.md
3cb57799e423f7c5036aa02e77e232b1924ecf3d8487c2649bb669d70da0e238  notes/design/2026-10-10-source-annotation-any-name-design.md
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c  notes/design/2026-10-08-call-source-interface-definition.md
71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992  notes/design/2026-10-02-source-result-synthesis-choice.md
3a3186723cd93edd2f767a7e4a481cb6dbed701fc749502e640071f65a4d89ae  notes/design/2026-10-10-concrete-effect-annotation-implementation.md
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1  notes/design/2026-10-05-inferred-function-call-views.md
```
