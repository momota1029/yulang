# Negative licensing: source identity falsification

Date: 2026-10-12
Status: independently reviewed bounded source characterization and conditional
constructor derivations; no negative-license counterexample or theorem closure
Baseline: `79f5fc15bd652f8b86cea73721ffd452cb99c9d7`
Branch supplied by primary: `research/simple-sub-intrusion`
Method: read-only source tracing, distinct from the constructive prover lane
Lease: this file only; writes stopped on submission

## Objective and authority

Test whether current source identities distinguish an annotation's licensed
concrete member/route from independent same-family lower operands meeting the
same effect row. Do not posit a new license field or reinterpret annotation
meaning. The required missing premise is an actual source construction relating
the negative annotation occurrence and member to the particular lower operand
and its derivation fiber. Neither a family comparison nor a row comparison
supplies that construction.

Governing sections are annotation-effect-hygiene-integration §§1,3–4;
contextual-attachment-admission-design §§1,3–4,6 (including the selected set
grouping in §3.1); contextual-residual-lineage-selection, “Selected policy” and
“Preserved contract and open obligations”; concrete-effect-annotation-
implementation, the opening contract, “Annotation checking and publication
owner”, and “Conflict ownership and replay”. Top-level inference principles
§§1–5 govern proof direction and abnormal paths. In particular, composed
negative `[E]` supplies position-local authority; co `[E]` is allowance/support,
not an emitted contribution. The withdrawn callback output is not an oracle.

The primary confirmed that the governing designs and all source/fixture
dependencies listed below are byte-identical to the pinned baseline. No Git
command was run by this worker. The principles file was read and hashed; its
baseline equality is not separately asserted by this worker.

## First missing constructor, before any licensed comparison

`candidate_source.rs:84–132` checks module, local, expression, formal and
operation annotations before source planning. `preflight_annotation` rejects
any nonempty concrete row at composed negative polarity. Formal preflight
additionally requires exactly one variable for an explicit negative row;
omitted ports retain their separate behavior. Function argument descent flips
the sign; result descent preserves it. This is a guard on the private candidate,
not an approved permanent language restriction.

The shortest relevant rejected formal shape is:

```yulang
act E
my f (cb:int -> [E] int) = cb
```

The parameter root is negative; its Function result effect remains negative.
Thus `preflight_formal` returns false and source admission returns Unsupported.
This exact literal was not parsed or run here. The same rejection shape is
already asserted by the retained fixture
`candidate_formal_effect_polarity.rs:65–70` (`int -> [io] ()`). Changing Int/Unit
or the resolved nullary family does not change the inspected guard.

The construction-side guard is independently visible at
`candidate_effect.rs:1507–1509`: `candidate_signature_effect` refuses a negative
concrete row before tail/view construction. Its negative symbolic branch at
1527–1538 returns a row/empty leaf rather than a concrete attachment. The
explicit negative empty bundles at 1280–1312 carry inert provenance only.

Consequently this scan does **not** find an admitted source with one genuinely
licensed negative contribution and one independent same-family contribution.
The first missing owner on these routes is negative concrete annotation
admission/construction, not information lost later by SCC equality or residual
key coalescing. The positive source weight records owner, position, member
ordinals and scope, but `LocalWeight.left_word` and `right_pops` have length zero
(`candidate_context.rs:115–150,2174–2196`). Its unit PUSH is detached preparation
only (2198–2215). No live negative word or subtraction consumer follows from
that record. This explains the inspected obstruction; it is not a universal
impossibility theorem over future source owners.

## Smallest retained same-family member collision

There is an actual constructor collision in the existing operation fixture,
without a negative annotation:

```yulang
act E
act F
act tick:
    our next: () -> [tick, tick, E] int

my lookup = tick::next; my rejected: () -> [F] int = lookup
```

`candidate_operation_source.rs`,
`owning_family_is_prepended_without_removing_original_interface_members`,
retains this literal and asserts all four operation-member identities. This
test was read, not run. The source law can be inspected directly: `parse_row`
(`source_annotation.rs:509–562`) preserves each concrete entry; outer operation
formation prepends the owning family and then extends by the original entries
(`candidate_effect.rs:1425–1429,1544–1548`). For one operation view `v`, members
`(v,0)`, `(v,1)`, `(v,2)` all resolve to the identical `SourceEffectId(tick)`,
with the same operation declaration, signature position, owner and operation
lookup occurrence. Their `AnnotationMember(v,k)` endpoints remain distinct.
Reducing the written row to `[tick]` leaves the minimal implicit/written pair
`(v,0)` and `(v,1)`; that reduction is a source derivation, not an executed fixture.

`candidate_check_effect_operand` expands Support by ordinal (895–914), so a
family/position/origin tuple cannot recover which member was consumed. These
are operation interface support members, not `Contribution` instances and not
two differently licensed members. The example falsifies member-identity
reconstruction from the nominal family and common provenance only.

## Precise common-row source candidate

The following small combined literal exercises two independent operation
source routes meeting one computation row:

```yulang
act tick:
    our next: () -> int

my answer = { my ignored = tick::next(); tick::next() }
```

This full literal is **not an existing inspected fixture and was not parsed,
lowered or solved here**. Its full admission and concrete numeric IDs remain
unverified. No rejection was observed either. The following derivation has
explicit hypotheses: HIR formation produces the displayed two resolved
Operation/Unit/Apply occurrences, one local initializer and a final Apply in
one Block; private planning/admission and scalar replay succeed without
suspension/resource failure. It is a conditional source construction, not
executable evidence or a negative-license counterexample.

Let `o1,o2` be the two operation lookup occurrences, `c1,c2` the two Apply
occurrences, `p1,p2` their operation result-effect rows, `i1,i2` the fresh
invocation rows, `a1,a2` the Apply computation rows, and `b` the Block's
computation row. These are ordinal locators, not invented numeric IDs.

1. Each actual Action::Operation invokes `candidate_operation` with its own
   occurrence (`candidate_source.rs:351–367,683`). The view constructor allocates
   separately, so `v1 != v2`; both have `allowed=[tick]`, no tail, and distinct
   OperationOrigin occurrences (`candidate_effect.rs:744–780,786–804,1458–1466`).
   Their actual lower operands are `Support(v1)` and `Support(v2)`, each initially
   below its own `p_j`. Member expansion yields `(v1,0)` and `(v2,0)`.
2. Each actual Apply creates its own `i_j` and negative Function demand
   (`shadow_apply.rs:1346–1366`). Function result-effect comparison supplies
   `p_j <= i_j`. Apply slots 2 supply `i_j <= a_j` (1438–1445).
3. Initializer installation emits `a1 <= b` at the first Apply's slot 20
   (`candidate_source.rs:306–316`). The final-expression Group recipe emits
   `a2 <= b` at the Block's slot 1 (462–470;
   `shadow_apply.rs:1414–1424`). These are actual constructor edges, not proposed
   attachment edges.
4. Native insertion and opposite replay (`candidate_extrusion.rs:740–802,
   841–864`) therefore transport both support lowers to the same canonical
   receiver `canonical_effect(EffectRow(b))`. Closed no-tail operands retain
   their view endpoints through extrusion (177–210). The two resulting
   relation pairs are `(Support(v1), EffectRow(b))` and
   `(Support(v2), EffectRow(b))`, with their actual replay contexts. Their pair
   components differ, so their RelationIds cannot coincide under the current
   interning key. Intermediate fibers retain their ordered replay dependencies.

The two lowers are independent operation routes of the same family on one row.
They have **no annotation subtraction license**. This is a positive common-row
candidate only. A same-row/family shortcut would erase their distinction, but
current source has no admitted licensed sibling against which to execute that
mutation. The primitive operation-call admission is retained in
`candidate_operation_source.rs::empty_operation_calls_validate_the_real_unit_argument`;
Block initializer scheduling and final Group construction are inspected above.
Those separate facts do not certify this combined literal's execution.

## What origin and RelationId actually certify

`Contribution { effect, origin, instance }` has no annotation-member incidence
(`candidate_effect.rs:139–144,864–886`). The production source action owners
inspected here create operation Support views instead. The only inspected
non-test caller of `candidate_effect_contribution` is graph freshening:
`candidate_scheme.rs:1064–1067` copies `effect,origin` and allocates a new instance.
Thus, **conditional on a captured Contribution graph**, equal Contribution.origin
can coexist with unequal instances. No source-emitted Contribution graph was
established in this scan. Operation origin also survives view copies (823–829).
Neither observation is a negative licensing witness.

RelationId interns `(typed pair, exact context)` and stores source occurrences
separately (`candidate_context.rs:2232–2251,2496–2532`). It certifies neither
unique source occurrence nor license. The retained test
`distinct_source_origins_survive_identity_memo_and_self_omission` explicitly
constructs one self-pair with two causes; it is a synthetic fixture, not a raw
source witness. A source-directed collision candidate is:

```yulang
my answer:['e] int = 1 as ['e] int
```

Ascription peeling uses the literal's exact computation component
(`candidate_source.rs:222–232`); both boundaries have Definition scope;
variable-only root checks directly select the same `(scope,'e)` tail
(`candidate_effect.rs:979–999,1330–1336`). Consequently their slots 47 and 42
seed the same `EffectRow(literal) <= EffectRow(tail)` with identity context,
while Origin occurrences remain distinct by slot. That gives one RelationId
for two boundary origins if the full literal forms and executes. Again, this
literal was not run; existing empty-root sibling fixtures at
`candidate_context_tests.rs:2268–2284` substantiate the slot owners, not this
tail collision. It has no concrete member and supplies no subtraction authority.

## Coverage, limits, and next action

Commands were bounded `cat`, `rg`, `sed` and `sha256sum` reads plus creation of
this note. No tests, builds, Oracle, executable probes, randomized seeds,
mutations, Git commands or child delegation ran. Compute samples/processes:
zero experimental processes; read commands were short single shell processes.
Peak RAM, CPU time and precise wall time were not measured; the packet allowed
30 minutes. Initial combined task/index output was truncated; only narrow
locators relevant to this gate were subsequently used. No complete task-file or
repository scan is claimed. Independent review remains pending.

Oracle independence: none is claimed. Evidence is current Y3 constructor source
and retained fixture text. Neither fixture assertions nor this derivation prove
their own runtime success without execution. Unsupported parameterized effects,
unresolved/imported declarations, complete Call, handlers/Catch, arbitrary SCC
intrusion, recursive context saturation, general residual construction and
soundness/principality remain outside this scan. A changed negative guard or
new source Contribution/licensing owner invalidates the corresponding boundary
claim and requires a fresh source trace.

Recommended next action: give the construction owner the original negative
annotation/member-to-lower-fiber obligation, with the guard above as its first
missing source application; require preservation of the common-row independent
operation routes. An equivalent supplied-flag checker would leave that premise
untouched. No new representation or production authorization is proposed here.

## Commit packet

- Exact leased path: `notes/progress/2026-10-12-negative-license-source-falsification.md`.
- Baseline SHA: `79f5fc15bd652f8b86cea73721ffd452cb99c9d7`.
- Dependency changes: none reported by the primary's frozen-baseline checks.
  Snapshot SHA-256s for principal source owners:
  `candidate_source.rs=13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49`,
  `candidate_effect.rs=ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df`,
  `candidate_context.rs=4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987`,
  `candidate_scheme.rs=9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1`,
  `shadow_apply.rs=cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411`.
- Review: unreviewed producer artifact; frozen on submission; no closure claim.
- Checks run: bounded source/fixture reads and dependency SHA-256 capture only.
- Proposed commit message: `research: locate negative license construction guard and source identity collisions`.
- Shared deltas left for primary/curator: keep negative source licensing OPEN;
  record the concrete admission/construction guard and conditional common-row
  candidate separately from executable negative evidence. No shared records,
  authority files, question bundles or compiler files were changed.

### Independent review

A `compiler_referee` reviewed the source-owner localization, conditional
common-row route, member-ordinal identity, contribution freshening condition,
and the limits on source execution and negative licensing. It found no blocking,
major or minor issue. The review did not independently revalidate every
dependency against Git; the primary's pinned-baseline comparison found no
dependency changes. Annotation-license construction, native residual execution,
H, complete Call, soundness, principality and F5 replacement remain OPEN.
