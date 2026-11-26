import Yulang.GeneralDeclarativeI65I74StructuralWhereTrace428

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.StructuralWhere428
open StructuralWhere427
open I72 (Event SourcePrimitives SourceTrace LocalMeaning FixedTargets DictionaryEvidence
  DictionaryEvidenceForest DictionarySound)
open CommonRoleOutermostResolver (All₂ Result Summarizes)

/-- Named local semantics must hold for each actual selected event,
regardless of which rule produced a surrounding node. This is a
semantic interface, not input to the classifier. -/
def SelectedLaw428 (R : SourcePrimitives) : Prop :=
  ∀ {s q e needs}, R.elected s q e needs → ∀ m : I72.Model,
    I72.Fits s m → LocalMeaning m e ∧ FixedTargets m e

/-- Fold the actual finite derivation, preserving child order and
the very same State/model. No assumption about which local rule
generated each child, no uniform search bound, and no termination
or completeness of a checker is asserted. The law already verifies
the selected original event including its fixed-target obligations. -/
theorem actual_named_trace_same_model_dictionary428 {R : SourcePrimitives}
    (law : SelectedLaw428 R) {s q t e} (trace : SourceTrace R s q t e)
    (m : I72.Model) (fit : I72.Fits s m) :
    ∀ d, Summarizes t (.selected d) → DictionaryEvidence s m q d := by
  exact SourceTrace.rec (R := R) (s := s)
    (motive_1 := fun q t _ _ => ∀ d, Summarizes t (.selected d) → DictionaryEvidence s m q d)
    (motive_2 := fun qs ts _ => ∀ ds, All₂ Summarizes ts (ds.map Result.selected) →
      DictionaryEvidenceForest s m qs ds)
    (motive_3 := fun _ _ => True)
    (fun _ _ evidence => by cases evidence)
    (fun v _ _ _ _ _ evidence => by cases v <;> cases evidence)
    (fun event _ picked _ _ _ kids dict summary => by
      have localMeaning := law picked m fit
      cases summary with
      | selected ordered combine =>
        cases combine with
        | selected dictionaries =>
          rw [dictionaries] at ordered
          exact .node event localMeaning.1 localMeaning.2 (kids _ ordered))
    (fun ds pairs => by
      cases ds with
      | nil => exact .nil
      | cons => cases pairs)
    (fun _ _ first tail ds pairs => by
      cases ds with
      | nil => cases pairs
      | cons d ds =>
        cases pairs with
        | cons a b => exact .cons (first d a) (tail ds b))
    True.intro (fun _ _ _ _ _ _ => True.intro) trace

theorem dictionary_sound_from_actual_named_local_law428 {R : SourcePrimitives}
    (law : SelectedLaw428 R) : DictionarySound R := by
  rintro s q d ⟨tree,event,⟨trace⟩,summary⟩ m fit
  exact actual_named_trace_same_model_dictionary428 law trace m fit d summary

/-- Union helper for the still-isolated named layer. A combined
trace is allowed to choose different local rules at different nodes.
This is not an installed system and asserts no new diagnostic policy. -/
def ruleUnion428 (L R : SourcePrimitives) : SourcePrimitives where
  elected := fun s q e needs => L.elected s q e needs ∨ R.elected s q e needs
  other := fun s q v needs => L.other s q v needs ∨ R.other s q v needs

theorem union_local_law428 {L R : SourcePrimitives}
    (l : SelectedLaw428 L) (r : SelectedLaw428 R) : SelectedLaw428 (ruleUnion428 L R) :=
  fun chosen m fit => chosen.elim (fun h => l h m fit) (fun h => r h m fit)

theorem dictionary_sound_for_actual_mixed_named_rule_traces428 {L R : SourcePrimitives}
    (l : SelectedLaw428 L) (r : SelectedLaw428 R) : DictionarySound (ruleUnion428 L R) :=
  dictionary_sound_from_actual_named_local_law428 (union_local_law428 l r)

theorem no_output_ordinary_event_same_model_semantics428 {s : I72.State} {q : Request}
    (f : AuthoredBodyFrame393 s.core q) (head : SourceHead s.core q f.decl)
    (noOut : q.demand.outputs = []) (m : I72.Model) (fit : I72.Fits s m) :
    LocalMeaning m (originalNoOutputEvent427 s.b6 f head noOut) ∧
    FixedTargets m (originalNoOutputEvent427 s.b6 f head noOut) := by
  refine ⟨⟨source_head_sound head m fit,?_⟩,?_⟩ <;>
    (intro i; exact Fin.elim0 (Fin.cast (congrArg List.length noOut) i))

end Yulang.GeneralDeclarativeI65.StructuralWhere428
