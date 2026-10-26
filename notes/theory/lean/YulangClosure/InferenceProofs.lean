import YulangClosure.BirthLevelSCC
import YulangClosure.SimpleSubConstraintSoundness
import YulangClosure.SimpleSubGeneralizationSoundness
import YulangClosure.SimpleSubRegularSolutions
import YulangClosure.SimpleSubRegularConstraintSoundness
import YulangClosure.SimpleSubScopedPublication
import YulangClosure.SimpleSubRegularPublication
import YulangClosure.SimpleSubRegularDecision

/-!
Checked inference proof components, integrated incrementally.
This import surface does not assert the original SourceProblem.InferenceSoundness
root. Each component records its exact source/native and model-existence boundary.
-/
