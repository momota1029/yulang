# Cycle 220 semantic review and SafeKnown correction

## Scope
Reviewed the concrete V8 sharing classifier against I-41: matching stays unchanged; a uniquely selected repeated-variable head imposes equality of actual origins; impossible equality rejects, while ambiguity wins over candidate-specific sharing. Checked root/candidate K2, root/inspection/administrative pending, absent uniqueness, empty journals, multiple frames, and the unchanged materialization Step.

## Intermediate-checkpoint defect and correction
The first cycle-220 checkpoint defined Conflict using Unique plus inhabited journal, available frame, and absence of any feasible frame/model. Unique alone is not selection readiness: its survivor can coexist with another declaration's unfinished inspection, or with an administrative merge still pending. No concrete reachable counterexample was constructed, but the definition lacked the guard needed to exclude this early rejection. This is a classifier-definition defect, not a proved contradiction in the overall target.

The correction adds the existing V7 SafeKnown predicate, without changing matching, survivors, Step, EvidenceNode, or any pre-220 file. It gates sharing rejection exactly as ordinary selected-head diagnostics do: root known, no root/candidate K2, no inspection/administrative pending. Existing output conflicts can still independently reject. GeneralDictionaryHeadSharingSemantic220 proves exact preservation of V7 pending and ambiguous classifications, not merely absence of a particular example. The saturated 218 regression still rejects because its old selection supplies SafeKnown.

## Classification cases
- Root pending: SafeKnown excludes it. The concrete Survivor already excluded raw root pending, but the explicit guard is stronger and directly auditable.
- Root or candidate K2: SafeKnown excludes sharing conflict, so the complete old classification is used. Known K2 retains old rejection priority.
- Inspection or administrative pending: the new guard excludes conflict. Old V7 pending is equivalent to new pending, including its existing merged-output handling.
- No unique survivor: no new conflict is possible. Two different survivor keys cannot be turned into sharing rejection; old and new ambiguity are equivalent. This does not filter a contradictory candidate from the candidate set.
- Empty model set: AtKey deliberately requires an existing model, so empty journals are not newly labelled sharing conflicts. This is a diagnostic convention, not a consistency/existence theorem. Universal evidence may be vacuous on empty journals.
- Missing frame: likewise no new conflict. On checked reachable old selections, the existing availability theorem supplies a frame; arbitrary malformed states have no such promise.
- Multiple eligible frames: Feasible existentially quantifies over both a current journal model and a same-key current frame; AtKey negates that entire existential. One bad choice of frame cannot by itself cause rejection. This is not a claim that all frames have identical sharing truth values. Existing frame-semantics209 lemmas establish checked same-key declaration/binder equality and semantic body/class equivalence under point arguments and held input centers. Stronger frame-independence should be stated with those hypotheses rather than presumed.

## Equations and unchanged Step
Sharing220 enumerates equal-name head-variable origin pairs, including diagonal pairs. HeadEquations and held packets/effects imply these actual-origin equalities. Recorded/Committed packets imply them in every current journal model. Therefore conjoining Holds with those predicates is extensionally redundant, and retaining the existing Step does not lose equality constraints for installed instances. Precision220/Accessible220 additionally show diagonal pairs impose no new obstruction for valid reachable nonrepeating heads; their reachability/source assumptions matter.

This does not prove an installable common witness exists. Feasible means some current model and frame satisfy sharing, not that every current model does, nor that sharing, head matching, protected-overlap constraints, ChoiceCompatible, and output/default effects have one simultaneous witness. Specification220 records the extra protected-overlap requirement. The final composition remains conditional on its original single EvidenceNode hypothesis; no evidence weakening or unconditional installation/completion claim is justified by this review.

## Validation
Focused warning-as-error rebuild covers corrected Conflict, transport, concrete composition, 218 regression, witness/specification, nonrepeating accessibility, prior regressions, and the new Semantic220 invariance lemmas. The exact build outcome is recorded with the cycle publication report. No pre-220 definitions or files were changed by this correction.
