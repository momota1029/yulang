# Selected annotation hygiene: current source owners and first missing cut

Date: 2026-10-12
Status: frozen, unreviewed research characterization; no parent gate closure
Method: one bounded static source pass; no execution, Oracle invocation or delegation
Baseline: `research/simple-sub-intrusion`, `1f6ea89bffc69dfe614d5b20d25a353b9ea52a34`
Exclusive lease: this note only

## Objective, authority and hypotheses

Locate the first actual construction/consumer gap for the selected annotation
policy, rather than repeating the Oracle same-task/force investigation.
Authority is [annotation hygiene integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–5 and [residual lineage selection](../design/2026-10-10-contextual-residual-lineage-selection.md),
Selected policy / Preserved contract. Contravariant concrete `[E]` permits
function-local subtraction at its position; covariant `[E]` permits concrete E;
polarity composes through Function arguments/results. Variables are excluded
from concrete atom collection but keep their connections. Separate residual
constructors retain identity even when their source rows become equal, and
current/future lowers must fan out to every retained applicable recipe.

[Top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5 govern implementation/proof direction and abnormal paths. Full rollback
is not assumed necessary. The retracted callback output in hygiene integration
§6 is not an expected scheme or oracle. This audit chooses no new meaning,
representation, restriction, diagnostic or cutover law.

The [same-task audit](2026-10-12-oracle-same-task-route-audit.md) and
[typed-boundary derivation](../theory/2026-10-12-oracle-typed-boundary-adequacy-proof.md)
were read as dependency boundaries: a poly dump is not a selected SolvedTask,
shared consumer maps do not independently certify provider preservation, and
the original H/M interpretation remains OPEN. Their Oracle argument is not
repeated. No Oracle files were inspected or invoked in this pass.

All code locators below are relative to the repository and pinned baseline.
Static conclusions assume those bytes, normal owner calls with valid retained
identities, and successful allocation/resolution where explicitly needed.
They do not assume source admission, annotation soundness, complete Call,
principality, a public scheme, or a reached runtime request. This is bounded
source characterization, not an established general theorem or executable result.

## 1. The earlier gap table is partly historical

The current private path already retains source annotation and concrete-view
evidence. Repeating the 2026-10-10 table as current would mislocate the work.

| Responsibility | Actual owner and retained data | Remaining boundary |
| --- | --- | --- |
| HIR parameter annotation | `module.rs:2171–2274`, `plain_binding_header`, admits a parenthesized annotated identifier when `local_source` is enabled. `local_source.rs:155–161,291–300` retains the annotation beside parameter ID, source key and scope. | This is the shadow LocalSource route, not ordinary HIR adoption. |
| Annotation occurrence / concrete identity | `module/source_annotation.rs:32–93,349–377,505–564`: `SourceAnnotation` retains definition owner and annotation position; each row retains its own SourceNodeKey, resolved SourceEffectIds and a separate variable list. IDs use module plus declaration key. | Concrete declarations/row operands are nullary identifiers. Parameterized effect operands have no retained type-argument representation here. |
| Composed polarity | `candidate_source.rs:117–130` preflight reverses at Function arguments and preserves at results. `candidate_effect.rs:1034–1050,1399–1437` reproduces the recursion. Formal roots begin Negative at :1090; whole/local/ascription roots use Positive. | HIR retains the tree, not a precomputed polarity certificate. Solver `polarity` and source `variance` are separate parameters. |
| Concrete candidate endpoints | `lib.rs:755–769` includes Contribution, Allowance, Support and AnnotationMember under `shadow-apply-candidate`. `candidate_effect.rs:140–174` stores concrete ID, origin/use instance, or view owner/position/allowed set/tail. | `yu-types::Leaf` still has only effect bottom/empty; concrete views live in the private candidate, not its ordinary leaf alphabet. |
| Capture graph | `candidate_scheme.rs:74,420–465` captures concrete views in `Node::EffectOperand`, including tail references. | `candidate_scheme::Atom` lacking E is not itself a missing concrete representation; the separate node already carries it. |

HIR parsing resolves all family headers before signature rows
(`source_annotation.rs:125–217`). `parse_row` requires one resolved declaration
for a concrete spelling and separates symbolic operands; it does not treat a
symbolic name as an empty row. Its one-variable and annotation-depth limits are
observed implementation boundaries, not restrictions approved by this audit.
No claim covers imports, parameterized families or all source type syntax.

## 2. Earliest remaining gap and a minimal discriminator

For a nullary family already represented by LocalSource, the first missing cut
is composed-negative concrete admission, before candidate collection:

```yulang
act io:
    our tick: int -> ()
my bridge (cb:int -> [io] ()) = cb
```

The operation declaration is only a resolved family scaffold; its operation is
never used. The decisive term has one formal, one Function and one concrete
row. A paired static discriminator moves the same row to the Function argument:

```yulang
my bridge (cb:([io] int) -> ()) = cb
```

Use each bridge in a separate source with the same declaration. Assuming
successful LocalSource formation, the first annotation's formal root is
Negative; its Function result retains Negative, so `[io]` is Negative. The
second's argument reverses that root to Positive. Primitive values and omitted
other ports introduce no further explicit row.

Direct derivation from owners:

1. `CandidateInference::solve`, `shadow_apply.rs:79–112`, calls
   `candidate_source::preflight` before `collect_candidate_mode` and session
   creation.
2. Its Lambda branch at `candidate_source.rs:97–101` calls
   `preflight_formal(ty, false)`. The formal itself has no outer effect row.
3. `preflight_formal` at :117–122 requires a Negative explicit row to contain
   no concrete atoms and exactly one variable. The first row has one concrete
   ID and zero variables, hence the branch returns false and solve returns
   `CandidateError::Unsupported` before construction/propagation.
4. The second row is Positive and has zero variables, satisfying that row
   predicate; its other nodes satisfy the same preflight. This proves only
   that this annotation passes this preflight, not successful solving or any
   expected output scheme.

The same limitation is guarded again at
`candidate_effect.rs:1035` (`candidate_formal_pair`), :1054–1070
(`candidate_formal_effect_port`), and :1508–1538
(`candidate_signature_effect`). Whole/local/ascription annotations also reject
Negative concrete rows at `candidate_source.rs:123–130`. Removing the outer
preflight alone would encounter an availability error, not construct scoped
subtraction. Explicit Negative empty rows have an additional formal limitation;
this witness isolates the selected concrete case instead of reinterpreting it.

The source variants are a minimized static discriminator, not a run or a
source-qualified soundness counterexample. Existing
`tests/candidate_formal_effect_polarity.rs` documents these shapes, including
positive argument rows and negative preflight rejection; no test was run and
its assertions supply no semantic proof. For parameterized E, the earlier
boundary is instead HIR `declarations` / `parse_row`, which only accepts singleton
identifier operands. The nullary discriminator avoids that unrelated syntax gap.

## 3. Executable covariant consumers and the missing subtraction consumer

For admitted Positive source variance, `candidate_signature_effect`
(:1540–1576) creates an occurrence-keyed view, copies resolved concrete IDs into
`allowed`, retains the scoped symbolic tail and attachment source, and places
Support on its positive solver port / Allowance on its negative solver port.
`candidate_formal_effect_variable` (:979–999) interns the tail by
`(AnnotationScope, name)` independently from value variables. Paired construction
reuses its per-operation view map keyed by row occurrence, not row equality.

`candidate_source::emit_candidate_source`, :276–283, schedules an actual
FormalAnnotation with parameter, occurrence and scope. The source driver at
:662–683 dispatches formal/local/ascription/whole constructors.
`candidate_formal_annotation`, `candidate_effect.rs:1073–1114`, creates both
Function faces, inserts the two parameter comparisons at slots 43/44 and
retains the negative formal domain. `shadow_apply::admit_candidate_fact`
(:1308 onward) checks retained source Apply inputs and forms a four-port demand;
this is not an annotation subtraction constructor or a complete Call proof.

The concrete consumer is real: `candidate_check_effect_operand`
(:888–957) expands Support into each AnnotationMember plus its connected tail;
compares actual concrete IDs against an Allowance's allowed IDs; sends an
unmatched atom into a present tail; otherwise records an effect conflict.
`candidate_apply_effect`, `candidate_extrusion.rs:840–864`, inserts row bounds
then replays opposite bounds. Bound insertion at :408–565 retains ordinary
typed bound evidence and capture incidence; :569–628 enumerates both bound
sides. Thus symbolic variables are not skipped from ordinary propagation.
This establishes these local transitions, not their global semantic adequacy.

The missing consumer is different from this allowance check:

- `candidate_context::LocalWeight`, :115–133, has zero-length live left-word
  and right-pop arrays. `source_weight`, :2174–2195, records resolved atoms,
  source scope and an optional `SourceUnitPush`, but publishes zero live words.
- `materialize_unit_push`, :2196–2215, creates a detached weight only. Its
  call sites found by exact symbol search are in `candidate_context_tests.rs`;
  it produces no live context, relation, bound or subtraction recipe.
- Live context seeding (:2479–2506) takes only an actual closed Allowance's
  zero-word weight. `candidate_zero_word_filters`, :2613–2710, validates and
  extracts this fragment; its consumer at :2744–2811 installs/replays ordinary
  allowance checks and marks their relation discharged. That discharge is
  not cancellation of an annotation-attached E contribution from an output.
- Negative empty attachment bundles (`candidate_effect.rs:1280–1313`) and
  inferred Lambda entry origins (`candidate_context.rs:1236–1249`) remain
  construction evidence. They are not EntryCertificate authorization.

Consequently the next cut needs both an authentic Negative concrete constructor
and its executable scoped consumer. A Positive allowance, matching family ID,
shared row, dormant attachment flag or successful comparison cannot substitute
for that pair. No Oracle pop count or successor carrier is selected here.

## 4. Equality, fresh uses, lineage and result boundaries

The existing lifecycle provides concrete seams to extend, not proof of the
missing feature. `candidate_copy_effect_view` (:806–831) validates the original
payload and copies owner, row position, allowed IDs, provenance and the supplied
tail. `candidate_remapped_effect_view` (:832–847) memoizes by original view ID
and remapped tail during one operation. Separately constructed views remain
distinguishable even when their tails become equal.

Extrusion (`candidate_extrusion.rs:104–175,180–205,262–326`) copies the selected
bound direction, transports view tails, and recaptures incoming allowance
incidence. Fresh use (`candidate_scheme.rs:1007–1107`) allocates local generic
row images, clones views through one use-local remap, allocates new Contribution
instances while retaining origin, and renames stored context weights.
Parent/copy merging (`candidate_intrusion.rs:514–595`) appends both bound sides,
transfers origins, splices capture incidence, then canonicalizes contextual
bounds. These are source operations; qualifying SCC correspondence and their
semantic preservation remain separate OPEN gates. This audit does not choose
the pending Value-reference transport law.

In particular `ReplayRecipe` / `ReplayRecipeId` in `candidate_context.rs:381–399,612–621`
is inert bound evidence keyed by Dependency and explicitly carries
`ReplayUseAntecedentsNotRetained`. It is not an executable residual-subtraction
recipe identified by its source constructor. `discharge_residuals`
(:2423–2428,2804–2806) stores a leftover ContextId after receiver checks; it is
also not that recipe. The selected residual-lineage policy therefore has no
source-qualified executable residual constructor/consumer correspondence in
the inspected cut. Neither existing structural memoization nor origin copying
establishes fan-out to every separately retained residual recipe. Origin
transport itself records `MissingOriginAssociation` at
`candidate_effect.rs:592–600`; this is an explicit evidence gap, not proof of
lost effects or incorrect output.

Diagnostics and publication stay distinct. Effect mismatches retain branded
operand/annotation handles (:604–657); `shadow_apply.rs:173–207` exposes their
actual occurrence-bearing operands. Candidate graph export/fresh-use observation
is refused on retained errors (:123–159). `lib.rs:10361–10375` finishes the
private CandidateSolvedResult with no closed types or public schemes.
Ordinary `SolvedModule::solve` (:17601–17603) uses the ordinary session, and
ordinary HIR lowering does not set `local_source` (`module.rs:878–924`). No
candidate graph or conflict here proves source rejection, a public effect
result, or F5 replacement.

## Next evidence and limits

One recommended next action: assign a bounded **proof/source-construction packet
for the coupled Negative concrete constructor and scoped residual consumer**.
Require an actual annotation occurrence, composed polarity, resolved atoms and
connected tail to construct a distinct residual lineage, then show how each
current/future source lower reaches every retained lineage through sharing,
fresh use and qualifying equality without removing independent same-family
contributions. Its first evidence should come from these owners, not another
checker with supplied subtraction transitions. Representation adoption and
compiler instrumentation need separate primary authorization; no code change
is proposed as already proved or implementation-ready.

The prior Oracle attempts left their native interpretation premise open. This
pass investigates a different owner, the actual Y3 admission/construction seam;
it supplies no new H/M interpretation and does not count as another Oracle
attempt. It does not establish the required constructive theorem, its
source-to-consumer bridge, complete Call, source rejection, principality,
termination or public conformance. There was no all-source census and no
search over seeds/ranges. No executable model, independent oracle, mutation,
runtime force or complete output was produced. Shared premises are pinned code
and accepted authority; local branch derivations assume their real owner input.

## Checks, dependency snapshot and resource accounting

Performed bounded `cat` / `sed` / `rg` source/rule reads; read-only branch,
HEAD and status checks; Python SHA-256 plus byte comparisons against
`git show 1f6ea89bffc69dfe614d5b20d25a353b9ea52a34:<path>` for all 18 direct
dependencies listed below. Every file matched. At that comparison HEAD had
advanced to `4621f771f98a9be7a22604d272ba0f41547496a7`; none of the inspected
semantic/source dependencies changed. Initial broad output truncations were
followed by narrow reads of decisive definitions; bounded symbol inventories
are not a complete repository census.

Direct dependencies: the three governing design documents linked above, the
two required Oracle notes, `crates/yu-hir/src/module.rs`,
`crates/yu-hir/src/module/{local_source,source_annotation}.rs`,
`crates/yu-solver/src/{lib,shadow_apply,candidate_source,candidate_effect,candidate_extrusion,candidate_intrusion,candidate_scheme,candidate_context}.rs`,
`crates/yu-types/src/lib.rs`, and
`crates/yu-solver/tests/candidate_formal_effect_polarity.rs` (read only).
The final submission repeats dependency/lease/whitespace/link checks.

One leaf, at most four lightweight read shells in an initial independent batch;
zero build/test/Oracle/probe processes and zero measurement samples. Each
observed shell command completed in under one second. CPU/RSS and reasoning
wall time were not instrumented; the assigned wall budget was one 30-minute
static pass. No heavyweight process, child launch, Git mutation, shared-record
write or compiler/test edit occurred. No independent review is claimed.

## Commit packet

- Exact leased path: `notes/progress/2026-10-12-effect-hygiene-source-owner-audit.md`.
- Baseline SHA: `1f6ea89bffc69dfe614d5b20d25a353b9ea52a34`.
- Changed dependency hashes: none; all 18 direct dependency bytes matched that
  baseline despite unrelated HEAD movement. Recheck remains required at primary integration.
- Review status: frozen unreviewed research characterization; H/M, concrete
  Negative implementation, complete Call and F5/public gates remain OPEN.
- Checks already run: narrow static owner/consumer inspection, source dependency
  byte/hash comparison, read-only branch/status; final note integrity checks in
  submission report. No tests/builds/Oracle/executable probes.
- Proposed one-line checkpoint message:
  `research: map annotation hygiene source owners and negative admission gap`.
- Shared-record deltas intentionally left for primary/curator: update the
  historical gap table with retained LocalSource annotations and private
  covariant EffectOperand support; identify Negative concrete preflight plus
  dormant subtraction/residual consumers as the next coupled cut. Keep source
  admission, residual fan-out, complete Call, hygiene, principality and public/F5
  gates OPEN. No shared task/design/index/theory or question file was edited.
