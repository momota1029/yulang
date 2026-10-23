# Constructor polymorphism and scoped release: paper extension

Sprint: POLYMORPHISM-RELEASE-20261023, contract revision 1.
Contract SHA-256:
`20db775cc8198eefbab6476adfffd136564d423eecf16c6f4da872d76c476008`.
Baseline: `31db23095e63fe8a1b1253612a1c2706df0d0790`.
Author: this primary only; no children, dispatcher or independent reviewers.
Claim class: **candidate paper derivation, independent review NOT_RUN**.
No parent A/B, production, compiler conformance or inference gate is promoted.

## Parent and concrete result

The user asked to include constructor rank-2, `'e?`, and contravariant
`[undet, 'e]` without a semicolon in the inference-independent safety work.
The previous manuscripts did not cover this combination. The new revision
adds the rules, local derivations and application to refined execution safety:

- Operational manuscript sections 10--12, Theorem 12.3: universal payload
  construction/elimination and value-restricted type abstraction; explicit
  polymorphic type arguments; comma-row normalization; authenticated scope and
  target association; actual crossing, release lifetime, same-view transport,
  multi-shot resumption; concrete release and finite abstract transfer; seventh
  cut-context frame; extended preservation/progress and safety.
- Selection manuscript section 12, Theorem 12.2: field projection retains its
  universal binder, while a method callable uses one whole instance; rigid
  universal boundary construction is value-restricted; scope/target evidence
  travels with qualified fields and dictionaries; eabs/eapp and selection
  preserve the extended calculus. Pure dictionary retrieval does not admit
  release merely because an outward row is empty.

The original 9.7 and selection 10.2/10.3 retain their previous-calculus scope.
The selection manuscript pins both the old core and the extended core; the new
claims explicitly use the extended rules rather than applying an old theorem
to new instructions without proof cases.

## Scope and authority distinctions

The annotated core includes both polymorphic constructor payloads and an
explicit polymorphic type argument such as Box<forall a. a -> a>. The latter
is explicitly called an impredicative instance, not disguised as a consequence
of rank-2 inference. An optional clarification distinguishing these forms was
asked asynchronously; no response was received before freeze. Both are included
as explicit declarative constructions. No new unannotated inference policy,
source syntax adoption or prior user decision is invented.

Release timing/lifetime follow the integrated 2026-10-05 q1/d1 decision, and
the alias-inside-output requirement follows the 2026-10-15 compose decision.
The concrete handles, state set, delimiter and finite diagrams are this
paper's proposed realization, not an adopted compiler architecture.
Separator admission follows the existing BracketRow syntax; polarity and
concrete permission follow the later annotation policy.

Direct authorities and hashes:

| Source | SHA-256 |
| --- | --- |
| `notes/design/2026-10-15-compose-scoped-effect-release.md` | `fd56f819f9b33adc5d75cbfdae378c90903e4aa3a266fc053c05dda315d40679` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| `syntax-reference/ja/src/types/bracket-row-grammar.md` | `5aacd95b8b28a82bda6c96cf358e9c4bb4389e5a3c16afc05e9b7dbff258111d` |
| `questions/2026-10-05-handler-protection-release-crossing/approved-answer.md` | `df33959fffeac0003723909de5af11edce2bd233ff70496a0dc5d3864126baff` |

The release-crossing and function-effect-row-denotation approved bundles were
read with their receipts; question/draft/answer/receipt bytes match HEAD, and
each approved answer contains its complete saved draft. Nothing in questions/
was changed or staged.

## Author's repair and adversarial cases

The initial construction placed release inside the original receiver's Scope.
Author reread identified that this could move a more external source marker
earlier than intervening handlers. The final text fixes the delimiter at its
actual annotated output slot. It does not move the slot to keep a receiver
alive; an inactive original receiver cannot grant new release authority.
Target entries retain each scope's original receiver separately.

The manuscript also distinguishes: a polymorphic field from a monomorphic
instance; a monomorphic reference storing a universal value from a universal
reference to one mutable cell; Observe from actual crossing; inner consumption
from outward propagation; aliases inside the same output packet from unrelated
views; the same live target from a new receiver/target; saved bound state from
current free state; restored release frames from a reinstalled shallow handler.
These are written derivations and author checks, not executable experiments
or independent validation.

## Exact remaining premises

The stated safety result takes explicit, well-scoped declarative derivations.
It does not establish general source construction of higher-rank instances or
the ingress/scope/target table, including multiple source annotation occurrences.
The concrete source-to-scope/lifetime derivation for the selected compose scheme
and its principality remain open; the identity transport calculation does not
close them. Existing resolver uniqueness/compact-to-raw correspondence,
snapshot lifecycle, inference completeness/termination, compiler lowering and
VM/native correspondence remain open. Independent review and mechanization of
both the older core and these extensions are still needed.

## Frozen artifacts and checks

- `docs/yulang-operational-type-safety-ja.tex`: SHA-256
  `bba63cf35153335a22be221ad0925dcef7ac4afdf441e49a5fa5bb2a555f799c`;
  XeLaTeX PDF: 44 pages in `/tmp/yulang-polymorphism-release-20261023/op/`.
- `docs/yulang-dot-selection-safety-ja.tex`: SHA-256
  `66e5da71711a6457a9b77915c9484f5a3dc23659c1f96fdcdbf258240737a780`;
  XeLaTeX PDF: 23 pages in `/tmp/yulang-polymorphism-release-20261023/dot/`.
- Final XeLaTeX passes: successful, no undefined-reference, overfull-box or
  LaTeX warning. The operational log retains 10 underfull-box notices at
  pre-existing lines before the new sections. No such notices in selection.
- Visual inspection: operational pages 35 and 39, selection page 22.
- `git diff --check`: PASS.
- `python3 tools/agent_sprint.py check`: STATIC CHECK PASS, not live-agent or
  proof evidence. Direct record inspection verified both artifact hashes,
  the original user-document hash, the unchanged four UNKNOWN identities and
  quarantined leases, absence of RUNNING rows, and the 16 KiB state limit.
- Compiler code changes, builds, tests, executable proof probes, independent
  review, mechanization: NOT_RUN / no changes, as applicable.

## Runtime, ownership and integration

Primary work clock: 2026-10-23 13:55:43 UTC; manuscript freeze observed at
14:19:39 UTC, 1,436 seconds within the 7,200-second cap. Remaining work is exact
record and Git integration. Runtime session/model metadata remain UNKNOWN;
no synthetic session identity or independent reviewer is claimed.
Manuscript authoring STOPPED at freeze; no children or background continuation.
The four old UNKNOWN identities and quarantined leases are retained. Original
untracked user documents and the quarantined R349 artifacts were not modified.
Previous frozen versions remain available at the baseline commit.

This is an unreviewed research-only preservation checkpoint. Next work is
independent review of the explicit crossing/state/finite-transfer construction
and the universal substitution boundary, followed by source-to-derivation work;
production implementation is not promoted by this checkpoint.
