import Yulang.GeneralRebaseUnaryRank271

namespace Yulang.GeneralRebaseUnaryReadback271
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Origin Observes shapeValue)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Cyclic)
open GeneralNominalFiniteMeaning (At project_value)
open GeneralRebaseUnaryRank271 (Unary value has_tag)
open GeneralDictionaryInspectionHeads215 (tag_subtype tagged_shape tagged_nominal)
open GeneralRebasePartialBool268 (Answer Reflect)

inductive Result where
 | unknown
 | absent
 | found (term : Unary)

def Meaning (m : Assignment) (o : Origin) : Result → Prop
 | .unknown => True
 | .absent => ∀ v, ¬ Observes m o v
 | .found t => At m .actual o (value t)

def stepNom (name index : Nat) : Result → Result
 | .unknown => .unknown
 | .absent | .found (.scalar _) => .absent
 | .found (.wrapper n child) => if name = n ∧ index = 0 then .found child else .absent

def stepStruct : Result → Result
 | .unknown => .unknown
 | _ => .absent

theorem no_structural (m : Assignment) (p : Origin) (t : Unary) (known : At m .actual p (value t))
 (s : GeneralNormalizedObservation.Shape) (j : Nat) :
 ∀ v, ¬ Observes m (.structural p s j) v := by
 intro v seen
 cases seen with
 | structural parent length rel found =>
   have h := known.2 _ parent
   have tags := tag_subtype (has_tag t) (tagged_shape s _ length) (subtype_trans h.2 rel.1)
   cases t <;> cases s <;> cases tags

theorem no_nominal_scalar (m : Assignment) (p : Origin) (b : Inference.Base)
 (known : At m .actual p (value (.scalar b))) (name j : Nat) :
 ∀ v, ¬ Observes m (.nominal p name j) v := by
 intro v seen
 cases seen with
 | nominal parent related found =>
   have h := known.2 _ parent
   have tags := tag_subtype (has_tag (.scalar b)) (tagged_nominal name _) (subtype_trans h.2 related.1)
   cases tags

theorem no_wrong_index (m : Assignment) (p : Origin) (n name index : Nat) (kid : Unary)
 (known : At m .actual p (value (.wrapper n kid))) (wrong : ¬ (name = n ∧ index = 0)) :
 ∀ v, ¬ Observes m (.nominal p name index) v := by
 intro v event
 cases event with
 | nominal parent rel selected =>
   have left := known.2 _ parent
   have agrees := (nominal_regular_invariant_exact ..).mp (subtype_trans left.2 rel.1)
   have len := (List.getElem?_eq_some_iff.mp selected).1
   have count : 1 = _ := agrees.2.1
   have zero : index = 0 := by omega
   exact wrong ⟨agrees.1.symm,zero⟩

theorem nominal_sound (m : Assignment) (p : Origin) (n j : Nat) (r : Result)
 (cert : Meaning m p r) : Meaning m (.nominal p n j) (stepNom n j r) := by
 cases r with
 | unknown => trivial
 | absent =>
   intro value event
   cases event with
   | nominal parent _ _ => exact cert _ parent
 | found t =>
   cases t with
   | scalar b => exact no_nominal_scalar m p b cert n j
   | wrapper name child =>
     change Meaning m (.nominal p n j) (if n = name ∧ j = 0 then .found child else .absent)
     split
     · rename_i good
       obtain ⟨one,two⟩ := good
       subst n
       subst j
       exact project_value (.nominal name 1) (by trivial) (fun _ => value child) cert ⟨0,by change (0 : Nat) < 1; decide +kernel⟩
     · exact no_wrong_index m p name n j child cert (by assumption)

theorem structure_sound (m : Assignment) (p : Origin) (s : GeneralNormalizedObservation.Shape)
 (j : Nat) (r : Result) (cert : Meaning m p r) : Meaning m (.structural p s j) (stepStruct r) := by
 cases r with
 | unknown => trivial
 | absent =>
   intro value event
   cases event with
   | structural parent _ _ _ => exact cert _ parent
 | found u => exact no_structural m p u cert s j

def run (source : Nat → Option Unary) : Origin → Result
 | .source id => match source id with
   | some value => .found value
   | none => .unknown
 | .nominal parent name index => stepNom name index (run source parent)
 | .structural parent _ _ => stepStruct (run source parent)

theorem run_sound (m : Assignment) (source : Nat → Option Unary)
 (cert : ∀ n ty, source n = some ty → Equivalent (m n).1 (value ty)) (o : Origin) :
 Meaning m o (run source o) := by
 induction o with
 | source id =>
   unfold run
   split
   · rename_i ty found
     exact GeneralRebaseInstalledReadback271.source_at m id _ (cert id ty found)
   · trivial
 | nominal p n j ih => exact nominal_sound m p n j _ ih
 | structural p s i ih => exact structure_sound m p s i _ ih

def cycle (source : Nat → Option Unary) (o : Origin) : Answer :=
 match run source o with
 | .unknown => none
 | _ => some false

theorem cycle_sound (state : State roles) (m : Assignment) (valid : Models state m)
 (source : Nat → Option Unary) (cert : ∀ n ty, source n = some ty → Equivalent (m n).1 (value ty)) (o : Origin) :
 Reflect (Cyclic state o) (cycle source o) := by
 have h := run_sound m source cert o
 unfold cycle
 split
 · trivial
 · rename_i different
   cases q : run source o with
   | unknown => exact False.elim (different q)
   | absent =>
     rw [q] at h
     rintro ⟨⟨_,edge,_⟩,_⟩
     obtain ⟨v,seen⟩ := (GeneralRebaseOriginCongruence269.edge_left_live edge m valid).1
     exact h _ seen
   | found value =>
     rw [q] at h
     exact GeneralRebaseUnaryRank271.acyclic state m valid o value h

end Yulang.GeneralRebaseUnaryReadback271
