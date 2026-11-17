import Yulang.GeneralDictionaryUpper230Closure
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryUpper230Equality
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229 GeneralDictionaryOptionalInstall229
open GeneralDictionaryUpper230Snapshot GeneralDictionaryUpper230Step
open GeneralDictionaryOptionalCycles229 (Form)
open GeneralDictionaryInspectionHeads215
open CommonNominalFullCarrier

private theorem top_ne (tagged : Tagged value tag) : ¬ Equivalent .top value := by
  intro equal
  let env : CommonNominalFullDemand.Environment Row := ⟨fun _ => .bottom,fun _ => [tag]⟩
  have held := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (equal.1 0) 0 env (.role 0)
    ((tagged env).mpr (List.mem_singleton_self _))
  exact held

private theorem records_ne_nominal (tagged : Tagged value .records)
    (equal : Equivalent value foo) : False := by
  have tags := tag_subtype tagged (tagged_nominal 0 _) equal.1
  cases tags

theorem form_injective (a b : Form) (equal : Equivalent a.value b.value) : a = b := by
  cases a <;> cases b <;> try rfl
  · exact False.elim (top_ne (tagged_shape (.record []) [] rfl) equal)
  · exact False.elim (top_ne GeneralDictionaryOptionalOutput229.tagged equal)
  · exact False.elim (top_ne (tagged_nominal 0 _) equal)
  · exact False.elim (top_ne (tagged_shape (.record []) [] rfl) ⟨equal.2,equal.1⟩)
  · exact False.elim (GeneralDictionaryOptionalOutput229.not_width ⟨equal.2,equal.1⟩)
  · exact False.elim (records_ne_nominal (tagged_shape (.record []) [] rfl) equal)
  · exact False.elim (top_ne GeneralDictionaryOptionalOutput229.tagged ⟨equal.2,equal.1⟩)
  · exact False.elim (GeneralDictionaryOptionalOutput229.not_width equal)
  · exact False.elim (records_ne_nominal GeneralDictionaryOptionalOutput229.tagged equal)
  · exact False.elim (top_ne (tagged_nominal 0 _) ⟨equal.2,equal.1⟩)
  · exact False.elim (records_ne_nominal (tagged_shape (.record []) [] rfl) ⟨equal.2,equal.1⟩)
  · exact False.elim (records_ne_nominal GeneralDictionaryOptionalOutput229.tagged ⟨equal.2,equal.1⟩)

inductive Index where
 | zero | one | two | three | four | lower | upper

def Index.identity : Index → Nat
 | .zero => 0 | .one => 1 | .two => 2 | .three => 3 | .four => 4 | .lower => lo | .upper => hi

def Index.form : Index → Form
 | .zero | .one => .foo
 | .two | .upper => .width
 | .three => .top
 | .four | .lower => .exact

def canonical : Form → Nat
 | .foo => 0 | .width => 2 | .top => 3 | .exact => 4

theorem index_model (index : Index) : (model index.identity).1 = index.form.value := by
  cases index
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact lower_value
  · exact upper_value

theorem supported_index (member : identity ∈ GeneralNominalState.sources extendedSnapshot) :
    ∃ index : Index, index.identity = identity := by
  have within := GeneralDictionaryUpper230Support.support member
  simp only [GeneralDictionaryUpper230Support.pool,List.mem_cons,List.not_mem_nil,or_false] at within
  rcases within with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.zero,rfl⟩
  · exact ⟨.one,rfl⟩
  · exact ⟨.two,rfl⟩
  · exact ⟨.three,rfl⟩
  · exact ⟨.four,rfl⟩
  · exact ⟨.lower,rfl⟩
  · exact ⟨.upper,rfl⟩


theorem raw_canonical (index : Index) (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models extendedSnapshot m) :
    Equivalent (m index.identity).1 (m (canonical index.form)).1 := by
  have old := (GeneralDictionaryUpper230Models.raw_exact m).mp valid |>.1
  have privateValid := (GeneralDictionaryJournalRefinement228Reobserve.extended_models_iff
    GeneralDictionaryOptionalStage229.allocated GeneralDictionaryOptionalStage229.reserved
    GeneralDictionaryOptionalStage229.ordinary m).mp old
  have parts := (GeneralNominalPacketSupport.private_exact packet m).mp privateValid
  cases index
  · exact ⟨subtype_refl _,subtype_refl _⟩
  · exact ⟨(alias_zero m parts.1).2,(alias_zero m parts.1).1⟩
  · exact ⟨subtype_refl _,subtype_refl _⟩
  · exact ⟨subtype_refl _,subtype_refl _⟩
  · exact ⟨subtype_refl _,subtype_refl _⟩
  · have merges := parts.2.2.1
    rw [bindings_exact] at merges
    exact GeneralDictionaryDefaultMergeRevisionProbe210.repeated_lower_value
      (name := 0) (by simp [GeneralDeclarations.Declaration.inputNames,
        GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.normalizeArgs,
        GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.Pattern.variables]) merges
  · have upper := valid.1.2.1 (5 : Fin 6) .emptyRecord rfl
    have width := valid.1.2.1 (2 : Fin 6) .emptyRecord rfl
    exact ⟨subtype_trans upper.1 width.2,subtype_trans width.1 upper.2⟩

theorem equality_closed : GeneralDictionaryUpper230Closure.EqualityClosed := by
  intro first last one two equal
  obtain ⟨a,rfl⟩ := supported_index one
  obtain ⟨b,rfl⟩ := supported_index two
  have same := equal model GeneralDictionaryUpper230Step.inhabited
  rw [index_model,index_model] at same
  have forms := form_injective a.form b.form same
  intro m valid
  have left := raw_canonical a m valid
  have right := raw_canonical b m valid
  rw [forms] at left
  exact ⟨subtype_trans left.1 right.2,subtype_trans right.1 left.2⟩

theorem stable : GeneralDictionaryDefaultKernel208.Stable registry after root :=
  GeneralDictionaryUpper230Closure.stable_of_equality_closed equality_closed

end Yulang.GeneralDictionaryUpper230Equality

