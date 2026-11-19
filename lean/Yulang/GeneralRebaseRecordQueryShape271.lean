import Yulang.GeneralRebaseRecordAlignment271
import Yulang.GeneralRebaseRecordEdge271

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseRecordQueryShape271
open CommonNominalFullCarrier
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Equal)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Origin Observes shapeValue)
open GeneralRebaseNominalOrigin269 (Raw origin)
open GeneralRebaseStructuralOrigin270 (Slots Kind shape kids root_shape)
open GeneralRebaseRecordIndices271 (Shadowed)
open GeneralRebaseRecordAlignment271 (visibleSet visibleSet_exact)
open GeneralRebaseRecordEdge271 (slot_payload)

theorem layout (state : State roles) (k : Kind state) (keys : List Nat)
 (known : shape state k = .record keys) : keys.Nodup := by
 have sorted := (Raw state).view.canonical k
 change (shape state k).Canonical at sorted
 rw [known] at sorted
 exact sorted.imp Nat.ne_of_lt

theorem held (state : State roles) (s : Slots state) (k : Kind state) (keys : List Nat)
 (children : Fin (shape state k).arity → Slots state)
 (known : shape state k = .record keys) (recorded : (Raw state).view.heads s = .structural k children)
 (m : Assignment) (valid : Models state m) :
 (kids state m children).length = keys.length ∧
 Equivalent (m ((Raw state).base.source s)).1 (shapeValue (.record keys) (kids state m children)) := by
 constructor
 · calc
    _ = (shape state k).arity := List.length_ofFn ..
    _ = _ := by rw [known]; rfl
 · have h := root_shape state s k children recorded m valid
   rw [known] at h
   exact h

theorem query_over (state : State roles) (s : Slots state) (k : Kind state) (keys read : List Nat)
 (children : Fin (shape state k).arity → Slots state)
 (known : shape state k = .record keys) (recorded : (Raw state).view.heads s = .structural k children)
 (i : Fin (shape state k).arity) (j key : Nat) (target : keys[i.val]? = some key) (query : read[j]? = some key)
 (checked : visibleSet keys read = true) (visible : ¬ Shadowed read j key) :
 Equal state (.structural (origin state s) (.record read) j) (origin state (children i)) := by
 intro m valid
 have h := held state s k keys children known recorded m valid
 exact GeneralRebaseRecordAlignment271.same_at m _ _ keys read (kids state m children) h.1 h.2 i.val j key
   target query (layout state k keys known) visible (slot_payload state k m children i) checked

def Dead (state : State roles) (o : Origin) : Prop := ∀ target, ¬ Equal state o target

theorem out_of_range (state : State roles) (source : Origin) (read : List Nat) (i : Nat)
 (missing : read[i]? = none) (full : ∃ m, Models state m) :
 Dead state (.structural source (.record read) i) := by
 intro dest e
 obtain ⟨m,valid⟩ := full
 obtain ⟨v,present⟩ := (e m valid).1
 cases present with
 | structural parent length value found =>
   have bound := (List.getElem?_eq_some_iff.mp found).1
   have impossible := List.getElem?_eq_none_iff.mp missing
   rw [length] at bound
   exact (Nat.not_lt_of_ge impossible) bound

theorem hidden (state : State roles) (source : Origin) (read : List Nat) (i key : Nat)
 (found : read[i]? = some key) (absent : Shadowed read i key) (full : ∃ m, Models state m) :
 Dead state (.structural source (.record read) i) := by
 intro dest e
 obtain ⟨m,valid⟩ := full
 exact GeneralRebaseRecordReadback271.hidden_not_same m source dest read i key found absent (e m valid)

theorem different_set (state : State roles) (s : Slots state) (k : Kind state) (keys read : List Nat)
 (children : Fin (shape state k).arity → Slots state)
 (known : shape state k = .record keys) (recorded : (Raw state).view.heads s = .structural k children)
 (j : Nat) (apart : visibleSet keys read = false) (full : ∃ m, Models state m) :
 Dead state (.structural (origin state s) (.record read) j) := by
 intro dest e
 obtain ⟨m,valid⟩ := full
 obtain ⟨val,saw⟩ := (e m valid).1
 cases saw with
 | structural prev len shapeOK good =>
   cases prev
   have h := held state s k keys children known recorded m valid
   have all := GeneralRebaseRecordReadback271.same_fields keys read (kids state m children) _ h.1 len
      ⟨subtype_trans h.2.2 shapeOK.1,subtype_trans shapeOK.2 h.2.1⟩
   have yes := (visibleSet_exact _ _).mpr all
   rw [apart] at yes
   cases yes

end Yulang.GeneralRebaseRecordQueryShape271
