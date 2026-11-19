import Yulang.GeneralRebaseDisplayFrame276
import Yulang.GeneralNominalOutputGrowth

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 7800000
namespace Yulang.GeneralRebaseTowerSemantics276
open GeneralNominalOutputGrowth (tower tower_equivalent)
open GeneralNominalRecursiveInspection CommonNominalFullCarrier
open GeneralNominalOriginTerms (arity project)
open GeneralDictionaryInspectionHeads215 GeneralNominalFiniteHeadInversion
open GeneralNominalCommonBridge (Assignment)

theorem no_structural (depth : Nat) (size : values.length = shape.arity) :
 ¬ Equivalent (tower depth) (shapeValue shape values) := by
 intro same
 cases depth with
 | zero => exact GeneralNominalCenteredHeadMatPairCycles.scalar_no_shape size same
 | succ depth =>
   have tag := tag_subtype (tagged_nominal 0 _) (tagged_shape shape values size) same.1
   cases shape <;> cases tag

theorem nominal_projection (depth : Nat) {arguments : List Argument} {actual : Ty} {index : Nat}
 (equal : Equivalent (tower depth) (nominal name arguments))
 (found : arguments[index]? = some ((Sum.inl actual) : Argument)) :
 ∃ k : Nat, k < depth ∧ Equivalent actual (tower k) := by
 cases depth with
 | zero => exact False.elim (GeneralNominalPeelingOrigins.base_not_nominal .int name arguments equal.1)
 | succ k =>
   have info := (nominal_regular_invariant_exact _ _ _ _).mp equal.1
   have bound := (List.getElem?_eq_some_iff.mp found).1
   have length := info.2.1
   change 1 = arguments.length at length
   have first : index = 0 := by omega
   subst index
   have meaning := info.2.2 0 (.inl (tower k)) (.inl actual) rfl found
   exact ⟨k,by omega,meaning.2,meaning.1⟩

theorem observed_depth {m : Assignment}
 (source : ∀ id, ∃ d, (m id).1 = tower d) (seen : Observes m origin actual) :
 ∃ d, Equivalent actual (tower d) := by
 induction seen with
 | source id =>
   obtain ⟨d,equal⟩ := source id
   exact ⟨d,equal ▸ ⟨subtype_refl _,subtype_refl _⟩⟩
 | nominal parent equality located ih =>
   obtain ⟨d,h⟩ := ih
   obtain ⟨k,_,result⟩ := nominal_projection d
     ⟨subtype_trans h.2 equality.1,subtype_trans equality.2 h.1⟩ located
   exact ⟨k,result⟩
 | structural parent size equality _ ih =>
   obtain ⟨d,h⟩ := ih
   exact False.elim (no_structural d size ⟨subtype_trans h.2 equality.1,subtype_trans equality.2 h.1⟩)

theorem smaller {m : Assignment} (depth : Nat)
 (found : ∀ value, Observes m origin value → Equivalent value (tower depth))
 (test : Test) (index : Fin (arity test)) (seen : Observes m (project origin test index) actual) :
 ∃ k, k < depth ∧ Equivalent actual (tower k) := by
 cases test with
 | scalar => exact Fin.elim0 index
 | nominal =>
   cases seen with
   | nominal parent equal atIndex =>
     have h := found _ parent
     exact nominal_projection depth ⟨subtype_trans h.2 equal.1,subtype_trans equal.2 h.1⟩ atIndex
 | structural _ =>
   cases seen with
   | structural parent size equal _ =>
     have h := found _ parent
     exact False.elim (no_structural depth size ⟨subtype_trans h.2 equal.1,subtype_trans equal.2 h.1⟩)

def Realizes (m : Assignment) (origin : Origin) (d : Nat) : Prop :=
 ∃ actual, Observes m origin actual ∧ Equivalent actual (tower d)

noncomputable def rank (m : Assignment) (origin : Origin) : Nat := by
 classical
 exact if h : ∃ d, Realizes m origin d then Classical.choose h else 0

theorem rank_exact {m : Assignment} (real : Realizes m origin d)
 (unique : GeneralNominalReadbackFunctionality.Unique m origin) : rank m origin = d := by
 classical
 have someDepth : ∃ n, Realizes m origin n := ⟨d,real⟩
 rw [rank,dite_eq_left someDepth]
 obtain ⟨a,seenA,left⟩ := Classical.choose_spec someDepth
 obtain ⟨b,seenB,right⟩ := real
 have equal := unique a b seenA seenB
 exact (tower_equivalent _ _).mp
   ⟨subtype_trans left.2 (subtype_trans equal.1 right.1),subtype_trans right.2 (subtype_trans equal.2 left.1)⟩

end Yulang.GeneralRebaseTowerSemantics276
