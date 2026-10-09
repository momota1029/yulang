# Executable annotated Value formal construction gate

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Baseline: `f3a5a7e50bed3dedb45c822301bc67564f97423c`
Status: bounded primitive formal slice integrated; focused checks/reviews complete
Authority: annotation-effect-hygiene-integration §1/§4, charter §21,
active Simple-sub legacy withdrawal and ordinary source inference objective
Mode: M2; semantic and source/test conformance reviewers
Verification owner: primary; one Cargo process, timeout 180, -j 2 --offline
Measurement budget: zero; structural accounting before any measurements

## Confirmed source constructor

Pinned Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`,
annotation/constraints.rs::connect_value_detailed:124–138 emits both directions
from one annotation-bound environment:

```text
annotation_positive <= formal_row_negative
formal_row_positive <= annotation_negative
```

Ordinary value annotations use that operation at
connect_parameter_computation_detailed:263–282. `x:int` and `x:()` therefore
supply positive information for body inference and negative checking constraints
for every actual argument, including ignored parameters. Entry stays Value;
lookup and lambda construction stay pure. Both comparisons belong to the
actual source formal boundary before body synthesis, through existing checked
admission, provenance and transactions. No annotation is silently dropped.

## Bounded first implementation

Retain the actual grouped identifier's annotation node on the admitted formal,
then parse it at its owner into `LocalSourceParameter.annotation`. Keep formal
identity, identifier source and annotation position distinct. Narrowly reuse
source annotation depth/recovery parsing. Top-level and local named functions
must retain the same formal owner discipline. Validate whole-local-binding
annotations separately from formal annotations rather than removing all checks.

Implement the Int and Unit leaf cases now through existing value constructors
and both ordinary row constraints. The source schedule executes their action
before body actions; generated fact counters, source primitive preparation,
source level metadata and transaction rollback account for both edges. This
is an executable primitive slice of the full formal gate, not its completion.

Function/variable/computation/effect-bearing formal syntax remains explicitly
unavailable in this slice. This is an unchanged incomplete implementation
boundary, not a selected permanent source restriction. Do not introduce unused
permission records for those cases.

## Required regressions

Actual top-level and local grouped annotations; inferred Int/Unit body/results;
wrong argument rejection and compatible controls; ignored annotated formal
checks; multiple parameters attach to the correct lambda layers; fresh uses
preserve result fibers; source parameter/annotation identity and annotation range;
unsupported effectful formals, other patterns and whole-local annotations retain
explicit refusal; failure after the first boundary edge restores complete state
and publishes no partial result. Preserve old test names and expectations unless
pre-write conformance adjudication finds an actual obsolete premise.

The HIR carrier/parser and solver source action/constructor are one coherent
artifact, frozen before M2 review. Work is linear in actual formal annotations;
there is no context worklist expansion in the primitive slice.

## Remaining full gate

Function omitted ports must not reuse current closed-empty defaults blindly:
Oracle pure_effect_bounds:492–497 contains a negative open row tail. Exact
source output/entry correspondence must be resolved before accepting Function
formals. Explicit effect formals require authentic attachment and output
projection plus contextual transport; they are still required by the full goal.
A separate source pass found that completed Oracle defined lambdas choose a
public negative formal interface before scheme publication, preventing incoming
callback providers from bypassing subtraction through a raw body formal row.
Its old calledness/local projection selection is not adopted as a mandatory
successor decision rule. Source-owned interface construction must replace it
with verified ordinary constraint/body checking correspondence.

Neither this primitive gate nor the repaired finite filter checker closes Call,
effect hygiene, soundness/principality, owned public schemes or default migration.

## Primitive slice closure

The [primitive delivery](2026-10-10-annotated-primitive-formal-integration.md)
records nine new owning regressions and the 83-test coherent phase, owning/
workspace/default checks, initial test import failure, accepted annotation-only
coverage repair and fresh delta closure. Source interface/effect/Function work
above remains required; no proof node or full formal gate is closed here.
