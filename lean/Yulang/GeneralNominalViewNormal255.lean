import Yulang.GeneralNominalViewTypeMap255
import Yulang.GeneralPresenceNormalFinite252
namespace Yulang.GeneralNominalViewNormal255
open Core.PresenceGeneration
open GeneralNominalRebaseRawView243
open GeneralPresenceCheckedNormal252 (Side)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalViewTypeTerms255 (terms pool supported)

def Supported (side : Side) (basis : List (TyTerm Nat)) (view : View) : Prop :=
 ∀ term ∈ terms view, GeneralPresenceCheckedNormal252.atoms side term ⊆ basis

def check (side : Side) (basis : List (TyTerm Nat)) (view : View) : Bool :=
 (terms view).all (GeneralPresenceCheckedNormal252.check side basis)

def rewrite (side : Side) (basis : List (TyTerm Nat)) (view : View) : View :=
 GeneralNominalViewTypeMap255.map (GeneralPresenceCheckedNormal252.normalize side basis) view

/-- A fixed-basis checked rewrite of all type-valued raw View fields. Rows,
shape and indices are retained literally. This is not a source scheduler Step. -/
def prepare (side : Side) (basis : List (TyTerm Nat)) (view : View) : Option View :=
 if check side basis view then some (rewrite side basis view) else none

theorem check_exact (side : Side) (basis : List (TyTerm Nat)) (view : View) :
 check side basis view = true ↔ Supported side basis view := by
 simp only [check,List.all_eq_true,GeneralPresenceCheckedNormal252.check_exact,Supported]

theorem prepare_exact (side : Side) (basis : List (TyTerm Nat)) (view result : View) :
 prepare side basis view = some result ↔ Supported side basis view ∧ result = rewrite side basis view := by
 unfold prepare
 by_cases yes : check side basis view = true
 · simp [yes,(check_exact ..).mp yes,eq_comm]
 · have no : ¬ Supported side basis view := fun h => yes ((check_exact ..).mpr h)
   simp [yes,no]

theorem rewrite_models (side : Side) (basis : List (TyTerm Nat)) (view : View)
 (closure : Supported side basis view) (assignment : Assignment) :
 (rewrite side basis view).Models assignment ↔ view.Models assignment := by
 apply GeneralNominalViewTypeMap255.models_exact
 intro term member
 exact GeneralPresenceCheckedNormal252.equivalent _ _ _ _
   ((GeneralPresenceCheckedNormal252.prepare_exact ..).mpr ⟨closure term member,rfl⟩) assignment

theorem prepare_models (side : Side) (basis : List (TyTerm Nat)) (view result : View)
 (success : prepare side basis view = some result) (assignment : Assignment) :
 result.Models assignment ↔ view.Models assignment := by
 obtain ⟨closure,rfl⟩ := (prepare_exact ..).mp success
 exact rewrite_models side basis view closure assignment

/-- The actual finite initial consumer vocabulary supplies closure, rather
than assuming a var-only basis contains every source atom. The pool is per
view here, not yet a single invariant pool for all future source states. -/
theorem source_pool_success (side : Side) (view : View) :
 prepare side (pool view) view = some (rewrite side (pool view) view) :=
 (prepare_exact ..).mpr ⟨fun term member => supported view side term member,rfl⟩

theorem source_pool_models (side : Side) (view : View) (assignment : Assignment) :
 (rewrite side (pool view) view).Models assignment ↔ view.Models assignment :=
 prepare_models side (pool view) view _ (source_pool_success side view) assignment

theorem compiled_source_models (side : Side) (source : GeneralNominalState.State) (assignment : Assignment) :
 let view := GeneralNominalRebaseRawView243.compile source CompTerm.var
 (rewrite side (pool view) view).Models assignment ↔ GeneralNominalState.Models source assignment := by
 dsimp only
 rw [source_pool_models,GeneralNominalRebaseRawView243.compile_exact]
 rfl

theorem rows_unchanged (side : Side) (basis : List (TyTerm Nat)) (view : View) (index : Fin view.slots) :
 ((rewrite side basis view).slot index).row = (view.slot index).row := rfl

theorem slots_unchanged (side : Side) (basis : List (TyTerm Nat)) (view : View) :
 (rewrite side basis view).slots = view.slots := rfl

theorem intervals_unchanged (side : Side) (basis : List (TyTerm Nat)) (view : View) :
 (rewrite side basis view).intervals = view.intervals := rfl
theorem prepare_none (side : Side) (basis : List (TyTerm Nat)) (view : View) :
 prepare side basis view = none ↔ ¬ Supported side basis view := by
 unfold prepare
 by_cases yes : check side basis view = true
 · simp [yes,(check_exact ..).mp yes]
 · have no : ¬ Supported side basis view := fun h => yes ((check_exact ..).mpr h)
   simp [yes,no]

theorem supported_mono (side : Side) (view : View) (small large : List (TyTerm Nat))
 (included : small ⊆ large) (before : Supported side small view) : Supported side large view :=
 fun term member _atom present => included (before term member present)

theorem expanded_source_success (side : Side) (view : View) (extra : List (TyTerm Nat)) :
 prepare side (pool view ++ extra) view = some (rewrite side (pool view ++ extra) view) :=
 (prepare_exact ..).mpr ⟨supported_mono side view _ _ (List.subset_append_left ..)
   (fun term member => supported view side term member),rfl⟩
end Yulang.GeneralNominalViewNormal255
