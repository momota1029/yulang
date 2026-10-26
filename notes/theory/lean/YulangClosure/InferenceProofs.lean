import YulangClosure.BirthLevelSCC
import YulangClosure.SimpleSubConstraintSoundness

/-!
Checked inference proof components, integrated incrementally.
This import surface does not assert the original SourceProblem.InferenceSoundness
root. Each component records its exact source/native and model-existence boundary.
-/
