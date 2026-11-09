# Cycle 42: scalar propagation is absorbed by structural closure

Data: arbitrary actual State n and directed scalar Fact n. Independent judgments are DirectedBounds.Derived and StructuralCarrierCoverage.Derives.

Goal: every directed fact has a structural derivation. Therefore inserting directed normalization before or after structural closure does not change structural closure membership. Under an explicit input model, this gives equality of actual endpoint observations and ordered diagnostic trees after structural normalization. This is a comparison of implemented fragments, not general semantic completeness or role feedback termination.

No language choice is changed. Structural closure can expose new scalar facts, so raw directed and structural outputs are not asserted equal.
