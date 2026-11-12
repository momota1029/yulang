# Cycle142: key-local evidence under actual descriptor replacement

Scope: I-25 item5, auxiliary soundness invariants, not a completed V5 bridge.
The current report guard tests all same-role declarations for every recorded
occurrence. A stored Instance only uses its actual key. We restrict the guard
to declarations of that key and then discharge it by the recursive finite
inspection footprint on point revisions (whose normalized view is fixed).

The trace uses the unchanged actual reobservation Step and Certified revisions;
ordinary extensions keep their existing restriction. It does not silently
replace Astra's transition relation. The target is Current at every reached
state, then same-final-model Evidence from child Evidence. No selected-to-recorded
coverage or unconditional refresh preservation is claimed. A separate concrete
nonempty-journal point replacement will check nonvacuity.

Latest integration706f60ce: lazy output-cycle policy belongs to Astra's Step
work; this cycle changes no semantics. Observation completion can preserve Models
while full saturation decreases it. Our revision certificate uses exact Models
only on the observation update, not on full stabilization.
