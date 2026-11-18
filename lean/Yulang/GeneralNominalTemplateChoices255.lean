import Yulang.GeneralNominalRebaseEffectView243
namespace Yulang.GeneralNominalTemplateChoices255
open Core.PresenceGeneration (TyTerm)
open GeneralNominalMaterialization (Mode)
abbrev Raw := GeneralNominalCenteredHeadMatExpressions.Expr
abbrev Materialized := GeneralNominalRebaseEffectView243.Expr

/- Finite overapproximation; occurrences of the same binder may choose
independently. Completeness is claimed, not exact realizability of every entry. -/
mutual
 def choices (pool : List (TyTerm Nat)) : Raw → List Materialized
 | .variable _ => pool.map .source
 | .primitive constructor arguments => (choicesMany pool arguments).map (.primitive constructor)
 | .nominal name arguments => (choicesMany pool arguments).map (.nominal name)
 | .record label payload tail => (choices pool payload).flatMap fun first => (choices pool tail).map (.record label first)
 | .variant tag payload => (choices pool payload).map (.variant tag)
 | .join first last => (choices pool first).flatMap fun a => (choices pool last).map (.join a)
 def choicesMany (pool : List (TyTerm Nat)) : List Raw → List (List Materialized)
 | [] => [[]]
 | first :: rest => (choices pool first).flatMap fun head => (choicesMany pool rest).map (head :: ·)
end

mutual
 def reads (mode : Mode) : Raw → List (Mode × Nat)
 | .variable name => [(mode,name)]
 | .primitive _ arguments => readsMany mode arguments
 | .nominal _ arguments => readsMany .actual arguments
 | .record _ payload tail | .join payload tail => reads mode payload ++ reads mode tail
 | .variant _ payload => reads mode payload
 def readsMany (mode : Mode) : List Raw → List (Mode × Nat)
 | [] => []
 | first :: rest => reads mode first ++ readsMany mode rest
end

mutual
 theorem compiled_mem (pool : List (TyTerm Nat)) (variables : Mode → Nat → TyTerm Nat)
 (mode : Mode) (term : Raw)
 (supported : ∀ entry ∈ reads mode term, variables entry.1 entry.2 ∈ pool) :
 GeneralNominalRebaseEffectView243.compile variables mode term ∈ choices pool term := by
 cases term with
 | «variable» name => exact List.mem_map.mpr ⟨_,supported (mode,name) (List.mem_singleton_self _),rfl⟩
 | primitive constructor arguments =>
   exact List.mem_map.mpr ⟨_,compiledMany_mem pool variables mode arguments supported,rfl⟩
 | nominal name arguments =>
   exact List.mem_map.mpr ⟨_,compiledMany_mem pool variables .actual arguments supported,rfl⟩
 | record label payload tail =>
   exact List.mem_flatMap.mpr ⟨_,compiled_mem pool variables mode payload (fun entry member => supported entry (List.mem_append_left _ member)),
     List.mem_map.mpr ⟨_,compiled_mem pool variables mode tail (fun entry member => supported entry (List.mem_append_right _ member)),rfl⟩⟩
 | variant tag payload => exact List.mem_map.mpr ⟨_,compiled_mem pool variables mode payload supported,rfl⟩
 | join first last =>
   exact List.mem_flatMap.mpr ⟨_,compiled_mem pool variables mode first (fun entry member => supported entry (List.mem_append_left _ member)),
     List.mem_map.mpr ⟨_,compiled_mem pool variables mode last (fun entry member => supported entry (List.mem_append_right _ member)),rfl⟩⟩
 theorem compiledMany_mem (pool : List (TyTerm Nat)) (variables : Mode → Nat → TyTerm Nat)
 (mode : Mode) (terms : List Raw)
 (supported : ∀ entry ∈ readsMany mode terms, variables entry.1 entry.2 ∈ pool) :
 GeneralNominalRebaseEffectView243.compileMany variables mode terms ∈ choicesMany pool terms := by
 cases terms with
 | nil => exact List.mem_singleton_self _
 | cons first rest =>
   exact List.mem_flatMap.mpr ⟨_,compiled_mem pool variables mode first (fun entry member => supported entry (List.mem_append_left _ member)),
     List.mem_map.mpr ⟨_,compiledMany_mem pool variables mode rest (fun entry member => supported entry (List.mem_append_right _ member)),rfl⟩⟩
end
end Yulang.GeneralNominalTemplateChoices255
