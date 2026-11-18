import Yulang.GeneralDictionarySourceAtom255
import Yulang.GeneralNominalViewNormal255
namespace Yulang.GeneralDictionaryViewNormal255
open Core.PresenceGeneration
open GeneralDictionaryOutputDepth252
open GeneralNominalPublicBasis253
open GeneralPresenceCheckedNormal252 (Side)
abbrev view := GeneralNominalRebaseRawView243.compile snapshot CompTerm.var

theorem constant_consumer : (TyTerm.base .int : TyTerm Nat) ∈ GeneralNominalViewTypeTerms255.terms view :=
 GeneralNominalViewTypeTerms255.ordinary_mem view _ GeneralDictionarySourceAtom255.ordinary_member
   (List.mem_cons_of_mem _ (List.mem_cons_self ..))

theorem var_basis_fails (keys : List (Nat × Nat)) (side : Side) :
 GeneralNominalViewNormal255.prepare side (basis registry context keys) view = none := by
 apply (GeneralNominalViewNormal255.prepare_none ..).mpr
 intro supported
 have included := supported _ constant_consumer
 apply GeneralDictionarySourceAtom255.constant_not_basis keys
 apply included
 cases side <;> exact List.mem_singleton_self _

/-- A concrete repair candidate retains source constructor atoms as well as
public references. It succeeds on the whole initial raw View and preserves
all its Models, without assuming the desired support conclusion. -/
theorem source_basis_repairs (keys : List (Nat × Nat)) (side : Side) :
 ∃ result,
 GeneralNominalViewNormal255.prepare side
   (GeneralNominalViewTypeTerms255.pool view ++ basis registry context keys) view = some result ∧
 ∀ assignment, result.Models assignment ↔ GeneralNominalState.Models snapshot assignment := by
 refine ⟨_,GeneralNominalViewNormal255.expanded_source_success side view _,?_⟩
 intro assignment
 rw [GeneralNominalViewNormal255.prepare_models _ _ _ _
   (GeneralNominalViewNormal255.expanded_source_success side view _) assignment,
   GeneralNominalRebaseRawView243.compile_exact]
 rfl

theorem inhabited_repair (keys : List (Nat × Nat)) (side : Side) :
 (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root initial ∧
 ∃ result,
 GeneralNominalViewNormal255.prepare side
   (GeneralNominalViewTypeTerms255.pool view ++ basis registry context keys) view = some result ∧
 result.Models model := by
 obtain ⟨result,ready,exactModels⟩ := source_basis_repairs keys side
 exact ⟨initial_source,result,ready,(exactModels model).mpr source_model⟩
end Yulang.GeneralDictionaryViewNormal255
