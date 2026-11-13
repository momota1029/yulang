# Historical materialization semantics under value reobservation

Status: conditional soundness transport, cycle 154, 2026-11-13.

The new Value transition relation cannot in general project to FeedbackSteps:
its administrative descriptor reobservation is a separate actual rule. Use its
proved ReobservationSteps projection. This rule changes descriptors but leaves
constructors and interpretation unchanged. Schema equality remains definitional,
while the existing certified transition carries every final model backwards.

Thus any fixed finite batch structurally observed earlier satisfies the final
materialization constraints after arbitrary actual Value steps. The proof retains
one final assignment throughout. It neither keeps syntactic observations alive
nor proves fresh request coverage or the complete current dictionary Instance.
This extends the historical feedback result to the current value-support layer.
