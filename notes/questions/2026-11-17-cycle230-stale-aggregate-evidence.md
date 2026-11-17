# Cycle230: reobserved endpoints leave a stable selected node without total evidence

Status: closed refutation of the exact current V8 EvidenceNode field. Independent
Lean --trust=0 audit PASS. No operational definition, language semantics, or
selection/evidence condition was changed. I34 stop applies.

## First proposal: delay the unrestricted field; retain this regression

Do not continue trying to prove the false current EvidenceNode. Keep the exact
boundary and this counterexample while deciding how a previously installed
packet should relate to its recomputed capture endpoints after reobservation.
Do not weaken Evidence, add inhabitance as a premise, restrict constructor
interpretations, or silently add a selection guard. No repair is implemented.

## Exact statement and positive premises

`GeneralDictionaryUpper230Regression.not_evidenceNode` proves, without premises:

```lean
¬ B4SkeletonV8.EvidenceNode
  (GeneralDictionaryHeadSharingBoundary220.boundary
    GeneralDictionaryJournalRefinement228Source.roles)
```

`stable_selected_without_evidence` bundles the actual V8 Reachable trace,
a concrete full journal model, actual DefaultKernel208 Stable at the saturation
root, actual V8 Local selected with no children, and absence of Evidence for the
selected dictionary in that same model. The initial registry passes the real
declaration checker; reachability includes InitialSource, coverage, point root
and ground source checks from OptionalInitial229. Empty child stability and
ordered child evidence discharge exactly the EvidenceAt requirements.
No stability or packet assembly conclusion is assumed.

This negates the assigned EvidenceNode bridge, NOT automatically B4 Statement,
compiler correctness, language consistency, or the source-language specification.
The composition theorem uses EvidenceNode as a sufficient premise, not an
equivalence.

## Small source-level picture

Schematic Yulang notation (not a parser-tested program):

```text
W = empty width-record type
E = exact empty record
O = E | exact record { tick: W }
impl P (Foo 'a 'a):
  associated Result = O
request P (Foo W W), with Result at source 4
```

The exact formal term is
`O = union exactEmpty (record 0 emptyRecord exactEmpty)`.
It is strictly below W, not bottom, and has no exact normalized Test head.
All of these facts are proved in OptionalOutput229. The expression is compiled
from an existing source Pattern, not introduced as an uninterpreted output.

The source has seed4 and slots0..4:
- 0 and1 denote the same Foo[W,W]. Slot0 initially exposes both intervals(4,2);
  slot1 exposes both point intervals(2,2).
- 2 is W and known; 3 is top; 4 is below2 and later constrained by the
  associated output to O.
- The root is a ground point demand at source0 with associated-output source4.
- There is one terminal declaration, key229; no generated children or merges.

Actual path: initial → install → certified point reobservation → certified
generated-upper refresh. Installation reserves aggregate IDs lo (purpose0) and
hi (purpose1); its old packet entails lo≃O and hi≃W. The actual binder (purpose8)
is W, so shared head arguments agree. Reobservation changes the inspected
endpoints to (2,2) without reallocating lo/hi. The new six-slot refresh exposes
hi as known W using the full trusted-input certificate.

At the final snapshot:
- Head/output/sharing checks select the declaration in V8. Both actual Foo
  arguments are W; this is NOT the earlier unequal-head-sharing counterexample.
- Any current Frame is the one current plan. Its repeated bindings require
  lo≃source2≃W, contradicting the retained full-journal lo≃O.
- Thus no current full packet can coexist with any full journal model, no
  current install is enabled, and no current-frame total evidence exists.
- Supported raw IDs are only0,1,2,3,4,lo,hi. Known are0,1,2,hi.
  Remaining3/4/lo cannot gain a justified exact head (top/O have none).
  Nominal descriptors are point-closed; generated demand is only the root;
  no enqueue, merge, reobserve, refresh or install step remains.
- Equate is also exhausted, not omitted: the concrete full model partitions
  supported IDs into four distinct meanings Foo/W/top/O; every same-class pair
  is already equivalent in every raw current model. EqualityClosed plus the
  exhaustive Step cases proves actual Stable.

## Decision needed, without preselecting a repair

1. Delay the unrestricted EvidenceNode and retain this negative regression
   while the supervisor decides what journal/Frame correspondence is intended.
2. Investigate operational rebasing or versioned capture allocation on
   reobservation, preserving old journal meaning without forcing new packet
   equations onto old aggregate IDs. This requires checking source-identity,
   sharing, monotonicity, termination and all twelve boundary laws.
3. Investigate a semantically justified historical-certificate transport rule
   with explicit endpoint/context correspondence. Merely ignoring the current
   Frame or dropping total packet conditions is not justified.
4. If rejection for this mismatch is intended, that is a design decision to
   state explicitly, not an automatic guard added by this cycle.

Question for the supervisor/owner: should recomputed capture endpoints allocate
a fresh/versioned aggregate, or should a retained certificate be transported
under an explicit correspondence? Is a genuine rejection intended instead?
No option has been adopted; spec, boundaries and previous definitions untouched.

## Verification

Cycle230Completion:60 constants/4 modules; PostRefresh:97/10; Final:53/2.
All independent --trust=0 audits exit0; only propext, Classical.choice, Quot.sound
allowed. Focused build status is recorded in the cycle report. No full gate or
Yulang2 oracle was run. Frozen Audit.lean and README.md match integration.
