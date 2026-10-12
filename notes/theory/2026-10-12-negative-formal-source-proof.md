# Negative concrete formal: exact source generation and output obstruction

Date: 2026-10-12
Status: bounded derivation independently reviewed; no parent gate closure
Claim class: bounded formal source-generation characterization and current-Y3 unavailability derivation
Primary baseline: `0e621f549035537e4d3e799c78f79dd9385df350`
Oracle document baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this file only; leaf, no delegation

## 1. Frozen statement, authority and limits

The packet asks whether the approved composed-negative concrete formal behavior
constructs one exact attachment-qualified removal/residual transition from the
same annotation occurrence through its actual resolved callback call and owning
output, or fails at a specific source rule/consumer. Do not assume this
association, effect-row equality, or contribution identity.

Governing authority is
[annotation-effect-hygiene-integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–4 and the withdrawal in §6;
[concrete-effect-annotation-implementation](../design/2026-10-10-concrete-effect-annotation-implementation.md),
“Annotation checking and publication owner”;
[contextual-attachment-admission-design](../design/2026-10-10-contextual-attachment-admission-design.md)
§§3–6, particularly one identity per concrete set at one exact occurrence in
§3.1 and the still-disabled general concrete-formal admission in §6; and
[top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. Negative concrete annotation **permits** local subtraction. This does
not independently require automatic subtraction at every unhandled output.
No retracted callback scheme is used as an expectation.

Keep the original universal H in
[global hygiene proof](2026-10-11-oracle-global-effect-hygiene-proof.md) §1
unchanged: every successfully lowered negative occurrence, original lexical
scope/binders, actual instance and actual call/output route; independent
same-family contributions survive; symbolic tails and current/future checks
remain connected; copying/generalization preserves the coupled identity and
residual lineage. No local statement below replaces those quantifiers.

For the **formal-model subclaim**, fix finite families with one resolved
nullary member E, empty initial environment Γ, level ℓ, one lambda binder cb,
one concrete slot occurrence a, and the unique syntactic application k:

```text
K = Empty -> {E}
e = λ(cb:K):*. (ref cb) ()
```

This is exact notation from the pinned mini-language grammar, not asserted
Y3 surface syntax. Let u be the fresh static ID allocated at a; r_a and r_b
the fresh domain/result rows of K; r_i and r_o this application's fresh demand
rows; and r_f this lambda's fresh output proxy. All coordinates, a, u, cb and
k are distinct roles. No callback provider body occurs in e; none is chosen
to explain its output.

**Formal subclaim M.** Its printed annotation and term-generation rules
construct the u-qualified positive result-row wrapper and forward it through
this same k to the owning output constraint. They construct no matching
POP_u on that output spine and no concrete row upper endpoint that could
trigger a removal/residual split there. Consequently those rules alone do
not establish the direct-call/output cancellation reported for the historical
production singleton. This is a bounded statement about emitted constraints,
not a predicted public scheme, an operational underflow claim, or a
counterexample to H.

For the **Y3 subclaim Y**, quantify over any successfully formed LocalSource
whose Lambda parameter retains a Function annotation with a concrete result
row at composed-negative position. The singleton has one member E and zero
symbolic variables; the argument also covers a concrete E with one retained
symbolic tail. **Y:** candidate preflight cannot accept this source. If
traversal reaches the matching formal, its `preflight_formal` test returns
false. Earlier unsupported checks may stop traversal before that branch. In
all cases, preflight failure precedes construction or execution of the formal
action, call demand and lambda output. The paired constructor has an
independent rejection as well. This is the packet's alternative (ii), a
concrete implementation boundary; it does not authorize rejecting those
sources in the supported language.

Shared premises: the exact inspected bytes; ordinary fresh allocation without
ID exhaustion; successful HIR formation where Y explicitly assumes it. No
supplied attachment-to-call map, invented provider, complete replay,
generalization theorem, or runtime discharge premise is used. Exclusions:
source runtime handler selection, parameterized family arguments, complete
Call, all-history replay/termination, extrusion/intrusion preservation,
generalization/fresh use, soundness/principality and public cutover. These
remain original parent obligations.

## 2. Pinned Oracle rule derivation

All Oracle locators in this section are document blobs at the pinned revision,
read with authorized `git show`, never the dirty checkout. The owner is
`research/effect-mini-language/directed_stack_weight_letrec_complete_ja.tex`:
surface grammar 250–277; slot/skeleton translation 719–780; I-Unit/I-Ref/I-Lam/
I-App 795–847; W-Pos/W-Neg/W-Fun/W-Comp/W-Filter 499–550; row fact/split
machine 951–1022; lexical-bracket assertion 1102–1118; materialization and
bracketing 1584–1655; fundamental proof 1848–1878.

1. `A_-(K)` reverses polarity in the callback domain and retains it in the
   callback result. Positive Empty is `Filter(Empty, r_a)`; negative
   concrete `{E}` allocates fresh u with seed `{E}` and gives
   `PWeight(PUSH_u({E}), r_b)`. Thus, with fresh value variables α and β,

   ```text
   C_cb = ((α ! Filter(Empty, r_a)) -> (β ! PWeight(PUSH_u({E}), r_b))) ! Empty
   ```

   The original formal occurrence owns u. No row equality or nominal
   comparison constructs that identity. No negative wrapper containing
   POP_u is returned by this translation.

2. I-Lam installs that very monotype at Γ[cb]. I-Ref looks up that entry;
   there are no quantified IDs in it to instantiate independently. I-Unit
   supplies `Unit ! Empty`. I-App creates its one fresh shape demand for k:

   ```text
   (α ! Filter(Empty, r_a)) -> (β ! PWeight(PUSH_u({E}), r_b))
       <: (Unit ! r_i) -> (B ! r_o)
   body result = B ! seq(Empty, Empty, r_o)
   ```

   This is the same resolved binder's single use. It does not derive complete
   provider compatibility for a future supplied callback.

3. W-Fun reverses domain constraints and preserves result constraints.
   W-Comp then gives the actual effect-result child:

   ```text
   PWeight(PUSH_u({E}), r_b) <: r_o
   r_b @ PUSH_u({E}) <: r_o                 W-Pos
   ```

   The other children constrain `Unit <: α`,
   `r_i <: Filter(Empty, r_a)` and `β <: B`. The actual domain filter owner
   W-Filter checks its row and retains its inner constraint; this domain's
   endpoints and incoming zero weight contain no u. Native bound insertion accumulates
   these facts; ordinary replay composes their recorded weights. No eager
   solution is assumed. No independent choice of result row is made.

4. I-Lam's explicit result annotation is wildcard. Its only output
   constraint is

   ```text
   seq(Empty, Empty, r_o) <: sem(*)+(r_f) = r_f.
   ```

   It has no filter, matching POP_u, or `[J; gamma]` endpoint. Even without
   simplifying `seq`, its printed construction supplies no u operation.
   Composing this output forwarding with the result child therefore cannot
   justify `PUSH_u ; POP_u`. The row-only split owner requires an upper
   concrete row endpoint `[H; y]`; none is generated on this spine. A
   genuine handler source would introduce that endpoint through I-Handle,
   a different source derivation, not through the annotation alone.

5. I-App's prose separately protects fresh internal positive effect
   occurrences with `PUSH_v(Empty)`. Whether that convention applies to
   a particular demanded/output occurrence is not specified as an explicit
   constructor distinction between annotated and unannotated callees here.
   Every such v is fresh and distinct from u. This ambiguity affects complete
   effect transport, but either reading leaves the decisive absence of a
   constructor for **POP_u** unchanged. No exception is invented to remove
   this ambiguity.

This establishes M at the original rule-generation boundary. In the finite
u-containing type fragments above, u occurs only as its positive PUSH. W-Pos
absorbs an existing operation; W-Neg requires an existing negative wrapper;
decomposition/replay transport or compose existing operations. They cannot
serve as a source constructor for the absent matching POP_u. The claim does
not infer every eventual compact output from this small graph.

The later lexical-bracket proof says lambda/application/handler exits place
matching pops. I-Lam and I-App do not supply that exit construction. Normalized
materialization maps **existing** `(m,n,F)` entries to m pop markers and n
push markers; it does not define a cb/a/k-specific exit that creates an
additional m. Invoking lexical bracketing or the fundamental theorem at this
point assumes the missing source-to-exit bridge. This is an identified proof
gap, not a new proof from a checker supplied with balanced transitions.

The pinned production spec `spec/2026-05-31-effect-variable-subtractable.md`,
“Annotation lowering” 255–275, gives the same permission reading. Its
“outer/local/repeat” worked example 627–653 actually obtains a residual only
after `catch f()` emits `r_b @ PUSH_u({E}) <: [E; tail]`. A permission wrapper,
an actual handler row-upper constraint, and a matching output POP are distinct
constructions. No implication between them is silently adopted.

## 3. Historical production singleton versus the formal model

The already reviewed
[negative-formal source proof](2026-10-11-negative-formal-effect-source-proof.md)
§§1,3 pins the historical source:

```yulang
pub act tick:
    pub ping: () -> ()
my f(cb:(() -> [tick] ())) = cb ()
```

That note derives an additional production spine: the paired annotation
result constructor returns a POP predicate; lambda lowering stores it on cb's
local record; the actual resolved local call extends f's latent frame; and
the defined-lambda output wraps both Value and Effect with that frame predicate.
The same freshly allocated ID occurs in those owners, even when a closed row
coordinate is shared. Its local `PUSH_i ; POP_i` algebra is independently
reviewed, conditional on the actual path reaching its consumers. The note
records the old observed scheme but does not certify universal source hygiene.

This packet inherits that reviewed bounded evidence and does not re-certify it.
One narrow additional pinned source inspection checks the wildcard guard:
`crates/infer/src/lowering/expr/lambda.rs:1509–1527` recursively scans the
whole annotated callable, including its parameter, argument effect, result
effect, returned value and tuple descendants. At 1585–1586,
`lambda_annotation_predicate_constraints` returns the empty predicate when
that Function annotation contains any effect wildcard; at 1339 the same
condition disables call projection. A non-wildcard immediate result effect
does not bypass this whole-callable guard.

The frozen formal K above contains **no wildcard anywhere**: Empty in its
domain and `{E}` in its result. Its q=`*` belongs to the enclosing lambda's
output annotation, outside cb's annotation K. Thus this K avoids the
whole-callable guard. An earlier candidate K=`* -> {E}` would trigger it
under a translation preserving the wildcard; that candidate is excluded from
comparison with the production singleton. The actual model wildcard rules
are `sem(*)- = PUSH(All)` and `sem(*)+ = identity`, with omitted slots sugar
for `*` (draft 273–277,725–743; pinned spec “Annotation lowering”). No
wildcard is reclassified as an empty row. The historical singleton shown
above has no written effect wildcard, and the inherited production derivation
uses its actual unsuppressed predicate route. No new Oracle execution ran.

The new result is that the printed mini-language generation rules above do
not construct the corresponding production call-predicate/output-frame spine.
The mini-language has effect-only value variables rather than that source's
fixed unit/value annotation; no source translation theorem identifying the
two is claimed. The disagreement is a missing bridge between constructions,
not evidence that the production compiler violates its approved behavior.

## 4. Current Y3 owning constructors and failure

HIR's `source_annotation.rs::parse_type` (399–480) preserves Function
argument/result structure, and `parse_row` (505–558) retains exact row
SourceNodeKey, declaration-resolved concrete member identity and symbolic
variables separately. `local_source.rs` (289–300; 752–788 for local formals)
retains the formal's actual HirParameterId, annotation owner and original
scope. The annotation fact is known before inference; source spelling or
equal row endpoints need not reconstruct it.

`CandidateInference::solve` in `shadow_apply.rs` (92–115) invokes
`candidate_source::preflight` before collecting the batch or creating/running
the session. The Lambda branch at `candidate_source.rs:97–99` starts
`preflight_formal` with `positive=false`. Its Function recursion at 119–121
reverses the domain sign and retains the result sign. The negative row test
at 117 is:

```text
row.concrete.is_empty() && row.variables.len() == 1
```

At a concrete result row E this is false, with or without one symbolic tail.
If traversal reaches this branch, preflight returns
`CandidateError::Unsupported`; earlier unsupported checks may terminate first.
Either way, candidate preflight cannot accept this source, before assuming a
successful negative-formal action, completed replay or an output consumer.
The source policy and source-support gate remain separate.

Removing preflight alone cannot complete the missing cut:

- `candidate_formal_annotation` (effect.rs:1073–1097) begins the paired
  constructor at Negative, at the actual parameter row's level.
- `candidate_formal_pair` (1034–1052) independently rejects negative concrete
  rows before constructing ports. `candidate_formal_effect_port` (1054–1070)
  implements omitted/symbolic rows and the positive concrete view branch;
  the negative concrete case returns an availability error.
- `candidate_check_effect_operand` (888–958) expands actual Support members,
  checks an Allowance, and forwards the exact unmatched lower to its tail or
  reports conflict. Allowance acceptance supplies no removal/residual result.
- `candidate_context::source_weight` (2174–2195) retains owner, row position,
  member ordinals and scope while storing empty executable words.
  `materialize_unit_push` (2200–2222) is explicitly detached from live
  ContextExprs, relations, bounds, registrations and recipes. Its prepared
  attachment ID is not a call/output transition.

Actual prospective consumers are already identifiable. `admit_candidate_fact`
(shadow_apply.rs:1308–1400) validates the same registered call occurrence,
callee/argument endpoints, result and application effect, allocates its
invocation row and builds its four-port demand. `admit_lambda_fact`
(lib.rs:11233–11351) uses the retained formal domain and joins body/entry
effects into the owning latent output. `CandidateSourceCall`
(candidate_call.rs:390–442) validates the exact formal registration and
resolved parameter name route. These mechanisms preserve structural incidence;
none of those facts constructs the absent negative formal transition. Their
current complete-Call/provider premises remain explicitly unresolved in
`shadow_apply.rs:12–48`.

## 5. Disposition in H and proof-obligation economy

Result: alternative (ii) is derived for the current Y3 constructor route.
The Oracle formal model supplies actual negative-annotation-to-call forwarding,
but no direct matching output cancellation constructor. Neither result
discharges H, refutes H, or authorizes general formal admission.

The exact remaining constructive premise is:

> For a negative concrete formal whose actual callable annotation passes the
> whole-callable wildcard guard, the paired source constructor and its actual
> resolved call/output consumer must agree on one executable attachment
> instance, including the authentic activation/removal or residual operation.

That is one coupled constructor/consumer premise, not two independently
selected witnesses. Its universal application still must preserve the original
scope, provider correlation, current/future checks and residual lineage.
Wildcard-containing formals remain in H's original source domain with their
actual guarded behavior; this local discriminator does not remove them from H
or require the suppressed direct-call predicate to appear on their route.

Two methods now reach this seam: the earlier production singleton establishes
the extra local call/output predicate construction, while this direct formal
generation inspection identifies its absence from the printed rule owners.
The static Y3 owner trace identifies a concrete source-support rejection.
Another proof assuming a PUSH/POP pair cannot close that seam.

Economy audit: actual local effect hygiene and ordinary negative formal
inference are required A/B obligations. Guessing attachment or provider/output
incidence after source formation would be D debt. HIR already knows occurrence,
resolved member, lexical scope and binder; the call owner knows its authentic
demand. Retaining those known facts can avoid reconstruction, but an ID alone
does not establish executable removal, whole-provider compatibility, residual
feedback or replay. No new representation, source restriction, mandatory
annotation, optional-C reclassification or change in proof status is selected.

One next action: primary adjudicate the exact paired-formal/call/output
construction against the reviewed production singleton, then assign its
source-owned executable invariant with independent falsification/review.
Keep H, complete Call, generalization, soundness/principality, admission and
F5 replacement OPEN until their original evidence is established.

## 6. Checks, resources, runtime and commit packet

Independent `compiler_referee` review found no blocking or major issue and one
minor quantifier-precision point. Y3's formal branch is reached only if earlier
preflight checks succeed; the claim now separates universal preflight
non-acceptance from branch-specific `preflight_formal` rejection. This does
not narrow H or the supported source domain. The reviewer also checked the
Oracle mini-language/production-constructor distinction, the wildcard guard,
and the Y3 owner localization; it did not certify H, generalization, complete
Call, source-wide replay, soundness, principality, or production admission.

Only this leased note was written. Static evidence: bounded `cat`, `sed`, `rg`
and Python SHA-256 reads; authorized read-only `git show` for the three
pinned Oracle document blobs and the primary-requested narrow wildcard guard
in the pinned lambda source. No dirty Oracle source read, Git mutation,
status/history operation, build, test, executable probe, Oracle invocation,
benchmark, child assignment or shared-record edit. Initial broad captures
were truncated; decisive owners were subsequently read in bounded excerpts.
An early lookup of the still-unwritten concurrent transfer note returned
missing-file; it supplies no premise and is not a dependency. An obsolete
`/tmp` Oracle locator was absent; all Oracle claims use the pinned Git blobs.

Resource use: lightweight static reads only, at most four independent shell
reads in one batch; no heavy verification process or measurement sample.
Aggregate CPU/RSS was not instrumented. Stop bound: 30 minutes or a concrete
obstruction; stopped at the obstruction. Requested launch model/effort is not
visible inside this leaf; configured defaults are `gpt-6.1-sol` / `high` and
the prover role has no model/effort pins. Observed runtime metadata: unknown.
No Astra, override-effect or hot-reload claim. Review is primary-owned.

Inspected SHA-256 dependencies (not Git blob IDs or proof of live-Y3 equality
to the primary baseline):

| Dependency | SHA-256 |
| --- | --- |
| annotation integration design | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| concrete annotation implementation design | `3a3186723cd93edd2f767a7e4a481cb6dbed701fc749502e640071f65a4d89ae` |
| contextual attachment admission design | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| Oracle source bridge note | `f61b3a4f720c120a0a25681cbc4160e162e13b32066198b3f07e460fbfa2f7ae` |
| global hygiene note | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| reviewed negative singleton note | `262c2569935c30a369846f50fede295d7f024677dca203b5d11e56ed6484f856` |
| `source_annotation.rs` | `a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb` |
| `local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `candidate_call.rs` | `79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35` |
| `shadow_apply.rs` | `cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411` |
| `lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| pinned Oracle complete draft | `efed007a3848c94f9d8925985f66e76ab86082dcb094c7ec3851b2bdd7082843` |
| pinned Oracle subtraction spec | `fbd9588b489dbc6b987c5e7a11d1d3f1bdc696be3bed605e5dcac849f42cda7a` |
| pinned Oracle effect brief | `9a537ddafb1fc0ba60ad6d2077d5d7d6bde0c02ab1ecab39b8a1bad641b7dc4c` |
| pinned Oracle lambda wildcard guard source | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |

Commit packet:

- Exact lease/change: `notes/theory/2026-10-12-negative-formal-source-proof.md`.
- Baseline: `0e621f549035537e4d3e799c78f79dd9385df350`; Oracle document
  anchor `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Claim/review: unreviewed bounded source-generation characterization and Y3
  unavailability derivation; no certification or parent closure. Writes stop
  at handoff for a frozen independent review.
- Checks already run: exact static owner reads, pinned Oracle document reads,
  SHA-256 dependency snapshot/recheck, leased-note whitespace/local-link check.
  No builds/tests/probes.
- Changed dependency hashes: none observed between final snapshots; equality
  of live Y3 inputs to baseline remains primary-owned.
- Proposed message: `research: trace negative formal source and output obstruction`.
- Shared-record deltas left to primary/curator: link this source-generation
  discriminator; distinguish formal permission transport, production
  call-predicate/output cancellation and absent Y3 negative construction;
  keep the original H and dependent A/B/admission/implementation gates OPEN.
  No shared record was edited.
