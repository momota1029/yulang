import Yulang.GeneralNominalRebaseRawView243
import Yulang.GeneralPresenceCheckedNormal252
namespace Yulang.GeneralNominalViewTypeTerms255
open Core.PresenceGeneration
open GeneralNominalRebaseRawView243
open GeneralPresenceCheckedNormal252 (Side)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

/-- Type-valued fields rewritten by the candidate normalizer. Row fields are
kept unchanged, not silently erased or claimed finite across future states. -/
def parameter : Parameter → List (TyTerm Nat)
 | .type lower upper => [lower,upper]
 | .row _ _ => []
def descriptor (entry : Descriptor) : List (TyTerm Nat) := entry.arguments.flatMap parameter
def ordinary : PresenceNormalForm.Atom Nat → List (TyTerm Nat)
 | .tyLe first last => [first,last]
 | .rowLe _ _ => []
def slot (view : View) (index : Fin view.slots) : List (TyTerm Nat) :=
 [(view.slot index).ty] ++ (view.heads index).toList ++
 (view.nominals index).toList.flatMap descriptor
def terms (view : View) : List (TyTerm Nat) :=
 view.ordinary.flatMap ordinary ++ (List.ofFn (slot view)).flatten

def pool (view : View) : List (TyTerm Nat) :=
 (terms view).flatMap fun term => GeneralPresenceUnionNormal252.atoms term ++ GeneralPresenceInterNormal252.atoms term

theorem slot_mem (view : View) (index : Fin view.slots) : slot view index ⊆ terms view := by
 intro term member
 exact List.mem_append_right _ (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨index,rfl⟩,member⟩)

theorem ordinary_mem (view : View) (atom : PresenceNormalForm.Atom Nat) (member : atom ∈ view.ordinary) :
 ordinary atom ⊆ terms view := by
 intro term present
 exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨atom,member,present⟩)

theorem supported (view : View) (side : Side) (term : TyTerm Nat) (member : term ∈ terms view) :
 GeneralPresenceCheckedNormal252.atoms side term ⊆ pool view := by
 intro atom present
 apply List.mem_flatMap.mpr
 refine ⟨term,member,?_⟩
 cases side
 · exact List.mem_append_left _ present
 · exact List.mem_append_right _ present

theorem prepare_success (view : View) (side : Side) (term : TyTerm Nat) (member : term ∈ terms view) :
 GeneralPresenceCheckedNormal252.prepare side (pool view) term =
 some (GeneralPresenceCheckedNormal252.normalize side (pool view) term) :=
 (GeneralPresenceCheckedNormal252.prepare_exact ..).mpr ⟨supported view side term member,rfl⟩

theorem normalize_equivalent (view : View) (side : Side) (term : TyTerm Nat)
 (member : term ∈ terms view) (assignment : Assignment) :
 Equivalent ((GeneralPresenceCheckedNormal252.normalize side (pool view) term).eval model assignment)
   (term.eval model assignment) :=
 GeneralPresenceCheckedNormal252.equivalent _ _ _ _ (prepare_success view side term member) assignment
end Yulang.GeneralNominalViewTypeTerms255
