import Yulang.GeneralRebaseTypedNominalWindow269
import Yulang.GeneralNominalStructuralReadback
import Yulang.GeneralNominalReadbackFunctionality

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseStructuralOrigin270
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Head Equal Edge)
open GeneralNominalRecursiveInspection (Origin Test Observes shapeValue)
open GeneralNominalOriginTerms (arity project source_self)
open GeneralNominalCommonBridge (Assignment assignment)
open GeneralNormalizedObservation (Shape)
open GeneralRebaseNominalOrigin269 (Raw origin)
open GeneralNominalReadbackFunctionality (projection_unique source_unique)
open GeneralNominalFiniteHeadInversion renaming head → tag
open GeneralDictionaryInspectionHeads215 (tagged_test tag_subtype tagged_shape tagged_scalar)
open CommonNominalFullCarrier

abbrev Slots (state : State roles) := Fin (Raw state).base.slots
abbrev Kind (state : State roles) := Fin (Raw state).view.kinds
abbrev shape (state : State roles) (kind : Kind state) := (Raw state).view.shapes kind

def Rigid : Shape → Bool
 | .pair | .variant _ => true
 | _ => false

def kids (state : State roles) {kind : Kind state} (m : Assignment) (children : Fin (shape state kind).arity → Slots state) :
 List Ty := List.ofFn (fun i => (m ((Raw state).base.source (children i))).1)

theorem root_shape (state : State roles) (s : Slots state) (kind : Kind state)
 (children : Fin (shape state kind).arity → Slots state)
 (recorded : (Raw state).view.heads s = .structural kind children) (m : Assignment) (valid : Models state m) :
 Equivalent (m ((Raw state).base.source s)).1 (shapeValue (shape state kind) (kids state m children)) := by
 have raw : GeneralNominalState.Models (Raw state) m := valid.1.1
 have known := GeneralNominalState.normalized_models (Raw state) m raw s ((shape state kind).term children)
   (by rw [recorded]; rfl)
 rw [show shapeValue (shape state kind) (kids state m children) =
      ((shape state kind).term children).eval CommonNominalFullCarrier.model (assignment (Raw state).base m)
      from GeneralNominalStructuralReadback.shape_values (shape state kind) children (assignment (Raw state).base m)]
 exact known

theorem shape_head (state : State roles) (s : Slots state) (kind : Kind state)
 (children : Fin (shape state kind).arity → Slots state)
 (recorded : (Raw state).view.heads s = .structural kind children) :
 Head state (origin state s) (.structural (shape state kind)) := by
 intro m valid
 refine ⟨⟨_,.source _⟩,?_⟩
 intro t seen
 cases seen
 exact ⟨kids state m children,List.length_ofFn ..,root_shape state s kind children recorded m valid⟩

theorem scalar_head (state : State roles) (s : Slots state) (base : Inference.Base)
 (recorded : (Raw state).view.heads s = .scalar base) :
 Head state (origin state s) (.scalar base) := by
 intro m valid
 refine ⟨⟨_,.source _⟩,?_⟩
 intro t seen
 cases seen
 exact GeneralNominalState.normalized_models _ _ valid.1.1 s (.base base) (by rw [recorded]; rfl)

theorem projected_equals (state : State roles) (s : Slots state) (kind : Kind state)
 (children : Fin (shape state kind).arity → Slots state) (recorded : (Raw state).view.heads s = .structural kind children)
 (i : Fin (shape state kind).arity) :
 Equal state (project (origin state s) (.structural (shape state kind)) i) (origin state (children i)) := by
 intro m valid
 let v := (m ((Raw state).base.source (children i))).1
 have found : (kids state m children)[i.val]? = some v := by
   unfold kids
   rw [List.getElem?_ofFn]
   split
   · rfl
   · rename_i no
     exact False.elim (no i.isLt)
 have seen : Observes m (project (origin state s) (.structural (shape state kind)) i) v :=
   .structural (.source _) (List.length_ofFn ..) (root_shape state s kind children recorded m valid) found
 refine ⟨⟨v,seen⟩,⟨v,.source _⟩,?_⟩
 intro left right atL atR
 cases atR
 exact projection_unique (source_unique m _) (.structural (shape state kind)) ((Raw state).view.canonical kind) i _ _ atL seen

theorem same_tag (state : State roles) (s : Slots state) (inhabited : ∃ m, Models state m)
 (first last : Test) (one : Head state (origin state s) first) (two : Head state (origin state s) last) :
 tag first = tag last := by
 obtain ⟨m,valid⟩ := inhabited
 exact tag_subtype (tagged_test first ((one m valid).2 _ (.source _)))
   (tagged_test last ((two m valid).2 _ (.source _))) (subtype_refl _)

theorem rigid_test (s : Shape) (known : Rigid s = true) (t : Test)
 (equal : tag (.structural s) = tag t) : t = .structural s := by
 cases s with
 | record _ | exactEmpty => cases known
 | pair | variant _ =>
   cases t with
   | scalar _ | nominal _ _ => cases equal
   | structural shape =>
     cases shape <;> cases equal <;> rfl

theorem scalar_no_edge (state : State roles) (s : Slots state) (base : Inference.Base)
 (recorded : (Raw state).view.heads s = .scalar base) (inhabited : ∃ m, Models state m) (dest : Origin) :
 ¬ Edge state (origin state s) dest := by
 intro actual
 obtain ⟨_,t,i,head,_⟩ := (GeneralRebaseOriginCongruence269.edge_normal state _ _).mp actual
 have equal := same_tag state s inhabited (.scalar base) t (scalar_head state s base recorded) head
 cases t with
 | scalar _ => exact Fin.elim0 i
 | nominal _ _ => cases equal
 | structural shape => cases shape <;> cases equal

theorem rigid_edge_iff (state : State roles) (s : Slots state) (kind : Kind state)
 (children : Fin (shape state kind).arity → Slots state)
 (recorded : (Raw state).view.heads s = .structural kind children)
 (rigid : Rigid (shape state kind) = true) (inhabited : ∃ m, Models state m) (dest : Origin) :
 Edge state (origin state s) dest ↔ ∃ i, Equal state (origin state (children i)) dest := by
 have canonical := shape_head state s kind children recorded
 constructor
 · intro e
   obtain ⟨_live,t,i,known,there⟩ := (GeneralRebaseOriginCongruence269.edge_normal state _ _).mp e
   cases rigid_test (shape state kind) rigid t (same_tag state s inhabited _ _ canonical known)
   exact ⟨i,GeneralRebaseOriginCongruence269.equal_trans
    (GeneralRebaseOriginCongruence269.equal_symm (projected_equals state s kind children recorded i)) there⟩
 · rintro ⟨i,witness⟩
   exact ⟨origin state s,.structural (shape state kind),i,canonical,fun m _ => source_self m _,
     GeneralRebaseOriginCongruence269.equal_trans (projected_equals state s kind children recorded i) witness⟩

end Yulang.GeneralRebaseStructuralOrigin270
