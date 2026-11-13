# Cycle 167: actual Shared trusted-readiness countermodel

## Result

At `GeneralDictionarySharedCapturedResumption.observed`, reached by the actual
producer installation followed by the actual scalar refresh, source 2 is raw
ready but **not** `GeneralNominalSharedSupport.ReadyAt`. The consumer's
`DecisionGuard` is therefore absent. This is a theorem about this fixture and
this state, not about every future extension or every possible program.

## Model and proof strategy

1. Start from the existing string-tail novelty model. Override only the
   generated producer target with `int`; captured source 2 remains `str`.
2. Verify source constraints, parent input facts, producer input facts, and
   producer output facts for this same assignment. Producer merge allocations
   are proved different from the overridden parent target.
3. The companion settlement-boundary theorem proves the consumer is not
   discharged and the parent output cannot occur in any Trusted slice.
4. Every Trusted fact is recorded in the actual state. Classifying those
   recorded facts leaves only the three validated fact kinds. Therefore the
   countermodel satisfies **every** Trusted slice of `observed`, including all
   support alternatives, not just a chosen small slice.
5. Every current head at source 2 is scalar `int`. Any supporting scalar head
   observation entails the corresponding scalar equivalence. The countermodel
   contradicts that equivalence for every Trusted slice, ruling out ReadyAt.

The smaller `GeneralDictionaryCapturedAliasCountermodel` module also records
the source-plus-output slice test. That slice is explicitly not asserted
Trusted. The stronger `GeneralDictionaryCapturedInputCountermodel` resolves
this limitation by validating inputs and quantifying over every Trusted slice.

## Verified scope

Focused compilation and dedicated audits with `--trust=0` pass for both new
modules. Audit declarations include parent_inputs, Producer.inputs,
every_trusted_slice, consumer_input_not_ready, consumer_decision_guard_absent,
and raw_ready_not_trusted. Only standard propext/Classical.choice/Quot.sound
occur. No new axiom, sorry, native_decide, semantic rule change, or full repo
build is used. Existing published modules are untouched.

## Consequence and limits

A full-journal scalar consequence and raw refresh do not supply the trusted
consumer guard in this actual trace. Reusing the parent output is circular
because that output requires the consumer already settled. This does not
assert global nontermination, impossibility after arbitrary future steps,
logical inconsistency, or closure of general V5. Any execution fix belongs to
the supervisor-owned semantics/guard lane; none is made here.
