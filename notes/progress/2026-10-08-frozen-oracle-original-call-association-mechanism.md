# Frozen Oracle ordinary Call association: bounded novelty stop

Date: 2026-10-08
Yulang3 baseline: `85b42f96883eabefa80b51532416b24d928644de`
Branch assigned: `research/simple-sub-intrusion`
Frozen Oracle: `/tmp/yulang2-oracle-rebuild`, `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Status: frozen research-only bounded historical characterization; compiler-referee reviewed
Exclusive lease: this note only
Authority: none for language semantics or production implementation
Review: compiler_referee PASS on content SHA-256 `a7ca57d766ca3e8465303857df01f7973f4c2bd4acb5cdba698f05d45a510221`; no semantic findings

## Objective, method and result

Find a historically distinct producer joining the fixed ordinary source cut
`call(result(name f),result(name x))` to its original complete inference
contribution or receiver owner. The method is bounded constructor/consumer
archaeology, with novelty checked against the six assigned October 7 notes
and the older notes encountered at the candidate seams.

**No new historical mechanism satisfying this assignment was found.** The
candidate local-call registry, local scheme instantiation, and expression
occurrence registry are already characterized. The primary then requested
one remaining check: ordinary-cast activation, source-boundary payloads and
local application construction outside those routes. That check finds a
downstream diagnostic consumer of the existing boundary mechanism and a
desugaring caller of the existing App constructor. Neither supplies a
distinct pre-query typed owner/view-kernel contribution witness. This is an
honest bounded stop, not a repository-wide absence or nonderivability result.

## Governing premise and claim classes

The current frontier is
`CALL_REL -> CALL_TYPE -> ORIGINAL_ASSOC -> ATTACH -> LIC_FORWARD/LIC_INVERT -> PROFILE -> ROWS -> independent admission`.
`tasks/current.md`'s “Priority frontier: complete original source contribution”
requires an inhabited original fiber in `I_orig(X)` whose witness owns the
exact original slot/contribution at `beta,p0`, types the complete receiver
invocation and preserves source arm, scope, providers and `xi=(nu,K,D)`.
Neither `c=j_call`, `s=p0`, a per-use slot count nor a new predicate can be
chosen by decree. Callee computation effects and the designated receiver's
upper invocation view stay distinct within the complete Call contribution.

[Inferred call views](../design/2026-10-05-inferred-function-call-views.md)
§§1.1–2 and 5 retain source/public/internal separation, source-derived static
identity and joint coordinates, and comparison-independent formation and
admission. [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
§2.1 explicitly takes independently typed primitive and owner/view-kernel
contracts as input. Its §3.5 realization theorem assumes those contracts and
local typing/conformance certificates; it does not introduce the missing
owner/view contract. Approved Option 2 continues to permit conservative
production observations without source execution witnesses.

Hypotheses for the local reduction below:

1. H-bytes: the inspected Oracle checkout resolves to the recorded pin; the
   cited bytes are the hashed files below. HEAD identity alone does not prove
   those files equal committed blobs; this pass did not compare blobs.
2. H-event: a `NominalCastNeeded` event supplies an already generated producer
   constraint and is routed through the inspected lifecycle branch.
3. H-quiescence: the caller reaches the eligibility-classification entry after
   pending work is drained, as its debug assertion requires. This is a
   control-path hypothesis, not an established solver completeness claim.
4. H-eligible: when following activation, the classifier supplies
   `EligibleSourceBoundary`; all other classifier outcomes are retained.
5. H-location: an ApplicationArgument explanation needs the corresponding
   span record. Missing recording remains a real branch.

Established here: concrete data/control dependencies on this bounded historic
path. Conditional characterization: under H-event/H-quiescence, activation
consumes a generated producer and its explanation-derived boundary; under
H-eligible/H-location it can recover diagnostic application/callee/argument
locations. No conditional theorem about the current source judgment, accepted
source counterexample, exhaustive licensing result or gate closure is claimed.
Interpreting one of these diagnostic IDs as an original slot or complete
contribution would be a candidate assumption with no bridge supplied here.

## Already-covered mechanisms and stop points

All Oracle locators are relative to the frozen checkout.

| Route | Concrete retained relation | Prior coverage / remaining boundary |
| --- | --- | --- |
| Source App | `tail.rs:630–685` allocates a boundary before the demand and installs span records after App construction | October 7 application-source-boundary producer and October 6 source-boundary-eligibility mechanism already cover this; origin allocation alone does not type the original contribution. |
| Formal/call aggregation | `tail.rs:603–614,690–717` records guarded call-upper IDs under a resolved local `DefId` and frame state | October 6 missing-producer-followup and multiuse-aggregation archaeology/continuation already cover this; no new ordinary App-owned tuple was found. |
| Local scheme use | `tail.rs:855–927`, entered by `name_ref.rs:146–174`, instantiates the local value and attaches generalized witness routes | October 6 source-producer-archaeology already covers this; generalized-use transport is not original Call contribution generation. |
| Actual/expected occurrence records | `chain.rs:8–28`, `tail.rs:564–586`, `occurrence_provenance.rs:15–67` retain bound/constraint roots by owner/role/path | October 6 presolve-application-types already distinguishes App actual-value snapshots from argument-owned expected demand roots after submission. |
| Resolved name/SCC and selection | Lexical use endpoints and hidden selection demand/result endpoints | The assigned October 7 SCC/selection notes already cover these identity/lifecycle mechanisms. Selection changes the fixed ordinary source cut. |
| Function paths and Specializer2 | Explanation labels, projected witness paths and materialized callee consumer | The assigned October 7 Function derivation/path and specializer notes already cover these downstream consumers. |

The first three candidate routes therefore failed the novelty requirement
before any new toy experiment was proposed. Repeating their endpoint or ID
discriminators would leave the same independently typed source introduction
untouched. They are mapped here for dispatch avoidance, not presented as new
research findings.

## Remaining bounded angle: cast activation and local construction

The following direct reduction answers the primary's follow-up. It is not a
new source-producer mechanism.

1. `analysis/session/lifecycle.rs:478–495` receives
   `ConstraintEvent::NominalCastNeeded { lower,upper,source,target,weights,producer }`.
   It deduplicates pending requests by **producer constraint ID**, retains
   that event payload, and separately invokes `constrain_nominal_cast`.
   There is no App, source formal, original slot or current contribution field
   in `PendingNominalCastRequest` (`ocast_activation.rs:30–38`).
2. `lifecycle.rs:520–540` drains pending requests at quiescence and calls
   `classify_ocast_eligibility(request.producer, explanation_budget)`.
   `constraints/ocast_eligibility.rs:155–175` queries
   `why_constraint_without_scheme_instantiation`. At `:178–276` the result
   depends on explanation completeness, source leaves, contributor maps,
   coherent owner maps and an eligible-evidence path. The owner/contributor
   maps propagate over explanation nodes (`:327–438`); they are not source
   receiver-owner or complete contribution judgments. The October 6
   eligibility note already establishes this distinction.
3. `ocast_activation.rs:47–109` converts that classification into boundary ID,
   source kind, diagnostic derivation kind and an optional parameter-bound
   record. `InternalOnly` and `Incomplete` provide no eligible request.
   `:127–153` resolves nominal cast cardinality; `:157–193` emits missing or
   ambiguous cast diagnostics, or takes no action for a unique cast.
4. For missing ApplicationArgument casts, `:195–239` looks up the existing
   boundary span table and emits diagnostic sites for argument and callee,
   plus the whole application span. A missing table record returns no
   locations/explanation. The table's application record is exactly three
   spans (`lowering/source_boundary_provenance.rs:93–97`), whereas
   `ApplicationProvenance` has source origin, module, application span and
   callee span (`lowering/application_provenance.rs:41–53`). Neither payload
   adds a typed contribution.
5. A scoped `rg` in `lowering/expr/block_local.rs` found the loop-desugaring
   applications at `:482–483`. Direct inspection shows `make_app(for_in,iter)`
   followed by `make_app(applied_iter,body)`. `tail.rs:479–495` forwards this
   helper to the already inspected constructor with Internal origin and
   source-expected capture disabled. It does not allocate the ordinary
   surface source boundary. This is a synthetic caller, outside the fixed
   five-node ordinary Call; it is not an alternative source-owner producer.

Thus the bounded dependency chain is

```text
generated nominal producer constraint
  -> pending producer-keyed cast request
  -> quiescent explanation query
  -> eligible diagnostic boundary projection
  -> cast cardinality / diagnostic locations
```

It does not precede the ordinary source constraint production it consumes.
This reduction uses the actual constructors and consumers; no checker was
written whose supplied transitions purportedly prove their source validity.

Failure conditions are explicit: no nominal event means no request; repeated
events with one producer deduplicate; pending work violates the entry's debug
precondition; incomplete/unknown/imported or missing-ownership explanations
can withhold eligibility; missing source locations withhold locations; a
unique cast emits no diagnostic. No mutation was executed. The proposed
shortcut “replace original association by eligible cast boundary” would
depend on an explanation query and optional nominal-cast event absent from
the required unconditional source introduction. This is a premise mismatch,
not a language counterexample or proof of nonderivability.

## Oracle independence, missing premise and next action

The historical code grounds the shape and lifecycle independently of current
research notation. Its solver, explanation classifier and diagnostics share
one implementation's transition/provenance assumptions. They are not an
independent semantic oracle for Yulang3, and no Oracle execution or successful
query is used as language authority.

The precise current blocker remains the original independently typed
owner/view-kernel introduction at the fixed Call: it must provide original
`beta`/`Slots(beta)`, typed `p0`, exact slot/contribution ownership and complete
invocation contribution on one shared original `X/xi`. A generated demand,
formal endpoint, source span or explanation boundary supplies none of that
interpretation by analogy. All legitimate original witnesses and the complete
contribution must be preserved; downstream projections do not exhaust them.

Recommended next action: stop this Oracle archaeology lane and derive the
current original slot/contribution introduction from its independently typed
source premises. Retain this route map to avoid dispatching another equivalent
boundary/registry probe. `ORIGINAL_ASSOC` and its dependent gates stay open.

## Checks, resources and omissions

Read `rules/research-lab.md`, `rules/design-authority.md` and
`rules/git-concurrency.md`, the current frontier and index, and the governing
sections above. Commands were bounded `cat`, `sed -n`, `nl -ba`, `rg -n`,
`rg --files`, initial read-only `git rev-parse HEAD` in both checkouts, and
Python SHA-256/file-existence reads. Initial combined document output and one
search output truncated; decisive governing sections and code windows were
reread, and no claim relies on complete search enumeration.

No Oracle execution, build, test, executable experiment, applied mutation,
compiler edit, formatter, scratch output, Git mutation, interactive question
or child delegation occurred. Heavyweight process count: zero. At most four
independent lightweight shell reads were batched; each completed in reported
sub-second tool time. CPU time, peak memory and total wall time were not
instrumented; no numeric assignment budget was supplied. No seeds/ranges or
runtime samples exist for this static method.

Coverage is the explicit windows and candidate seams above. Full solver and
classifier correctness, all other local/synthetic forms, App consumers outside
the listed routes, admitted source realizability, semantic completeness,
runtime adequacy, repository-wide absence, and current source conformance
remain unverified. Initial HEADs resolved to the recorded pins; this pass
records bytes rather than certifying Oracle worktree cleanliness. The note is
the entire write set and freezes on submission; the producer makes no claim
of independent review.

| Direct dependency | SHA-256 at freeze |
| --- | --- |
| Source-contracts design | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| Inferred-call-views design | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| Oracle `analysis/session/ocast_activation.rs` | `d87cb3c04d6c63e04156d74d0e2c4c58934b6a27567e1fd353abe9d5b64aa2f0` |
| Oracle `analysis/session/lifecycle.rs` | `196b0f1eeef891e3547bf77e3d00f5f0574399e24bc59c4697219df6ff93d5ed` |
| Oracle `constraints/ocast_eligibility.rs` | `5391594b96be39532c48c15a526cf285b264dd6c66c67fa807a990a10151a892` |
| Oracle `lowering/application_provenance.rs` | `b062742b588830ce5edf1a51a9c8718aca0b81b1360b3c4c1172b09e112614aa` |
| Oracle `lowering/source_boundary_provenance.rs` | `9d9f1694d4848be9daddea986b80be833f081d1e78a31ce1a0e540b740d74412` |
| Oracle `lowering/expr/block_local.rs` | `661386fe559d8e207a9597962cfee3c11f05f21aa2888e22b2c0143825051898` |
| Oracle `lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-08-frozen-oracle-original-call-association-mechanism.md`.
- Baseline SHA: `85b42f96883eabefa80b51532416b24d928644de`; Oracle pin:
  `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none introduced by this worker. Freeze hashes
  above identify inspected inputs; initial-to-final byte equality was not
  instrumented and should not be inferred from that statement.
- Review status: compiler_referee PASS on the content hash recorded in the
  header. No independent certification of current semantics or theorem
  closure is claimed.
- Checks already run: initial HEAD identity; leased-path absence; scoped
  novelty searches; direct code/payload/order reduction; SHA-256 reads;
  artifact trailing-whitespace check and decisive payload-locator check.
  No tests/builds/Oracle execution. Primary owns final lease/diff/dependency
  validation and any independent review.
- Proposed one-line checkpoint message:
  `research: bound remaining Oracle ordinary Call association routes`.
- Shared-record delta intentionally left for primary/curator: optionally
  record that this bounded follow-up found no new producer and cast activation
  consumes the already characterized generated-boundary explanation; keep
  `ORIGINAL_ASSOC` and every dependent gate open. No task, index, authority,
  theory or question-board file was edited.

The producer froze this artifact before review submission; the independent
review result is recorded in the header.
