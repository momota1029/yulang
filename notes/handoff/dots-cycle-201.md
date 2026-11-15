# dots cycle 201 — nonterminal total assembly and same-model tree heads

## Timing, recovery, concurrency

- Event: 2026-11-15T00:27:19Z. Actual start: 00:30:01Z.
- Hard finish deadline: 01:22:19Z, using the stricter event-based 55-minute cap.
  The user's latest cap overrides the standing document's longer work-time instructions.
- Fresh integration at start: `de7f12306187c25516e99489bf7b482d147634bf`.
  Read standing orders/inbox anew, no STOP, I33 last instruction. Prior cycle200
  report and completed heartbeat checked before writing. No overlapping Yulang writer.
- Reused the retained worktree/cache. A proof/review delegate could not start
  because the team thread limit was reached; performed work directly.
- Normal GitHub fetch succeeded. Source publication used the GitHub app with
  expected-head, nonforce ref updates, only `work/dots-main`.
- During checkpoint readback integration advanced to
  `190f6471d50cb7561722ae5bdc0ad7c54bb9f3fd` (owner Alloc/V7 work).
  Reread instructions: still I33, no STOP. Merged all owner files unchanged.
  The import conflict was resolved owner-first, then retained 200/201 appended
  lines, without removing previous imports or changing existing proof modules.

## Published source

1. `53676a4fe1d29060a15d7f1c972e3186f2964e52`: five Mat assembly/regression modules,
   small audit and design note.
2. `2f2f457fbc26b69a05cb0d4e1c70032bc30f14ee`: five further tree/V7 modules,
   second small audit, two design notes, and unchanged owner 190f6471d integration.
   Both the prior work branch and owner integration are parents.

The final source tree was freshly fetched and matched the local verified tree
exactly (`git diff --exit-code`, exit 0). The report/verification publication
follows this source checkpoint. No rewrite of aggregate `lean/Audit.lean` or
`lean/README.md`; both compare byte-identically to the owner integration base.

## Proved, with exact scope

### 1. Nonterminal input-variable total packet assembly

`GeneralDictionaryMatInputVariables201.InputVariableClauses` requires each
where-clause to have no named outputs and literal variable arguments whose
names belong to inputNames and not outputNames. Requirements may be repeated
and nonempty. This is strictly narrower than cycle200's normalized-variable
fragment; no claim of normalized-join/compound coverage is made.

- Lower/upper total input equations are reflexive at the forwarded capture endpoints.
- Actual child-center equations are reflexive at the forwarded shared binder.
- Each child Site.Holds follows from the same HeadEquations binder Fits.
- Needed shared names are proved to be input names; this is not an extra premise.
- Root total output equations follow from actual ClassEffects at the recorded
  raw site, without requiring terminality or scalar root outputs.
- `GeneralDictionaryMatInputAssembly201.holds_of_head_class`: for every plan,
  assignment and current registered site, same-assignment HeadModels,
  HeadEquations and ClassEffects plus this source restriction imply the actual
  total `GeneralNominalCenteredHeadMatStepPackets.Holds`. Neither packet Holds
  nor child Site/schema validity is assumed.

### 2. Same-model structural head realization

`GeneralDictionaryMatTreeHead201.HeadTree` contains only an existing finite
nominal-tree witness, injective binder names, exact inputNames, query and packet
bounds. It has no Models, Holds, Instance, Evidence or completion field.

For every assignment satisfying the packet context state, `head_models` proves
HeadModels in that same assignment, reusing GeneralNominalTreeFacts.private_models.
With a current Frame, journal Models supplies that source-state premise.
`packet_of_current_tree` combines the structural head theorem with input-variable
assembly: current journal Models plus Effect.Holds imply total packet Holds.
No separate common HeadModels premise remains. Root named outputs are unrestricted
for this assembly theorem. HeadEquations/ClassEffects are still genuine semantic
obligations in Effect.Holds, not consequences claimed from selection alone.

### 3. Exact selected adapters, including the incoming Alloc/V7 boundary

`GeneralDictionaryMatSelectedInputs201.evidence_of_selected_common_head` maps
assembled total semantics to Mat/V6 selected Evidence with exact selected child
list and multiplicity.

`GeneralDictionaryAllocV7InputBridge201` proves the source input-variable
restriction invariant under the owner's allocation encoding, and exact root
request preservation. Its evidence theorem targets actual
`GeneralNominalCenteredHeadAllocV7Boundary.boundary` with source Checked/Reachable,
compiled effect registry and actual V7 Local/Stable, not a renamed Mat boundary.

`GeneralDictionaryAllocV7TreeEvidence201.evidence_of_selected_tree` further derives
the common head component structurally. Its remaining premises include:

- a current effect with the correct compiled registry and snapshot;
- a HeadTree shape and InputVariableClauses;
- ChoiceCompatible and ONE jointly valid current journal/effect model;
- actual selectedness/stability, RootDefined and scalar compatibility for the
  old recursive Evidence conversion;
- target current Models and exact child Evidence for the selected child list.

The common witness may differ from the target assignment; stability transports
packet validity. The theorem does not claim that selectedness supplies the
common effect witness, ChoiceCompatible, structural shape or child Evidence.

### 4. Concrete regressions and target distinctions

- `GeneralDictionaryMatInputFixture201`: a checked nonterminal declaration with
  two genuine where-clause child demands. For every source model, head/class
  assembly gives actual total packet Holds. Concrete source and current journal
  Models are inhabited. `child_count = 2`; no requirement is erased.
- `GeneralDictionaryMatTreeFixture201`: an explicit structural HeadTree exists
  for the same two-child fixture, with current Models, same-assignment HeadModels
  and total Holds. This is a nonvacuous packet-semantics regression, not a claim
  of a complete selected recursive dictionary for those children.
- `GeneralDictionaryMatInputScope201`: the previous real scalar-conflict fixture
  has current journal Models, HeadModels and a valid Frame, yet cannot jointly
  satisfy HeadEquations/ClassEffects in that assignment. It is not a stable
  selected V7 counterexample.
- `GeneralDictionaryAllocV7EvidenceScope201`: the owner's new stable selected
  ancestor with an empty final Models set DOES satisfy the exact final-snapshot
  B4SkeletonV7.EvidenceAt, while global HeadBaseline and SelectedCompletion are
  false. This explicit vacuity regression prevents mistaking failed existential
  completion for a refutation of modelwise V7 EvidenceNode.

I33's unrestricted prior EvidenceNode remains refuted by cycle199's inhabited
output-conflict witness. V6 rejects that witness. Neither that result nor the
empty-final-model V7 ancestor refutes the owner's selected/modelwise target.
No new skeleton, semantic-policy repair or assertion of B4 completion was made.

## Verification

Full command/output transcript: [verification](../verification/dots-cycle-201.md).

- Combined focused strict build of all 10 new modules: exit 0, 1120 jobs (mostly
  cached dependency jobs; not 1120 newly rebuilt modules).
- `lake env lean --trust=0 -DwarningAsError=true Audit/MatInputAssembly201.lean`:
  exit 0, 25 named entries.
- Same command for `Audit/MatInputV7Tree201.lean`: exit 0, 20 named entries.
- Temporary all-constants checker over the 10 new modules, including generated
  declarations: `AXIOM-GATE-PASS: 84 declarations`, exit 0.
- Only propext, Classical.choice and Quot.sound; no new axiom or kernel bypass.
- `bash tools/verify-lean.sh . 190f6471d50cb7561722ae5bdc0ad7c54bb9f3fd --no-build`:
  PASS, exit 0. This is explicitly the diff-only gate, not full validation.
- Final published source tree readback: exact match, exit 0. Frozen aggregate
  Audit/README comparison: exit 0.

Initial focused proof attempts failed on list membership/index bounds and
unused simp arguments; corrected only unpublished new files, then strict checks
passed. One latest-base diff gate correctly failed when fresh integration had
advanced but was not yet an ancestor; merged owner changes and reran successfully.
No full umbrella build, all historical audits, owner-wide AxiomGate, CI check,
or Yulang2 runtime rerun. The historical Y2 role-boundary audit was read; its
where/body and ambiguity differences were not adopted as new language semantics.

## Next cycle

1. Fresh fetch/re-read instructions, heartbeat and this report. Continue the
   selected/modelwise target as directed; distinguish current I33 wording from
   owner V7 composition already present in integration.
2. Reduce the remaining common journal/effect and ChoiceCompatible obligations
   under explicit, noncircular source conditions. HeadTree now removes the
   separate same-model HeadModels gap for finite linear nominal-tree heads.
3. Extend beyond literal input-variable children only with an actual proof of
   total endpoint/center/named-output equations; do not assume old empty schemas
   mean the total compiler has no child equations.
4. Do not demand global existential HeadBaseline at empty-model snapshots.
   A modelwise premise is the right scope for V7 EvidenceAt. The unrestricted
   selected EvidenceNode field and B4 Statement remain open.
