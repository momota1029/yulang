import Yulang.GeneralRebasePhaseLoop281

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
namespace Yulang.GeneralRebasePhaseCache281
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalCenters (Plan)
open GeneralRebasePhaseKeys281 (Codec Key owner Seen Added)

def planKey (codec : Codec roles Q) (p : Plan roles) : Option (Key Q) :=
  (codec.classify p).map (fun tag => (owner p,tag))

def keys [DecidableEq Q] (codec : Codec roles Q) (s : State roles) : List (Key Q) :=
  (s.plans.filterMap (planKey codec)).eraseDups

def qualifies [DecidableEq Q] (codec : Codec roles Q) (s : State roles) (p : Plan roles) : Bool :=
  match planKey codec p with
  | none => false
  | some key => !(keys codec s).contains key

theorem encoded {codec : Codec roles Q} {p : Plan roles} {key : Key Q} :
    planKey codec p = some key ↔ owner p = key.1 ∧ codec.classify p = some key.2 := by
  cases key with
  | mk id key =>
    unfold planKey
    cases codec.classify p <;> simp

theorem member [DecidableEq Q] (codec : Codec roles Q) (s : State roles) (key : Key Q) :
    key ∈ keys codec s ↔ Seen codec s key := by
  unfold keys Seen
  simp only [List.mem_eraseDups,List.mem_filterMap,encoded]

theorem qualifies_exact [DecidableEq Q] (codec : Codec roles Q) (s : State roles) (e : Effect roles) :
    qualifies codec s e.plan = true ↔ Added codec s (GeneralNominalVersionedInstall232.install s e) := by
  unfold qualifies
  rw [GeneralRebasePhaseKeys281.fresh_iff]
  cases target : planKey codec e.plan with
  | none =>
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨tag,found,_⟩
    have hit := (encoded (codec := codec) (p := e.plan) (key := (owner e.plan,tag))).mpr ⟨rfl,found⟩
    rw [target] at hit
    cases hit
  | some found =>
    obtain ⟨ownerEq,tagEq⟩ := encoded.mp target
    constructor
    · intro yes
      change (!(keys codec s).contains found) = true at yes
      have absent : found ∉ keys codec s := by
        intro contained
        rw [List.contains_iff_mem.mpr contained] at yes
        cases yes
      refine ⟨found.2,tagEq,?_⟩
      rw [ownerEq]
      cases found with
      | mk o q => exact fun seen => absent ((member ..).mpr seen)
    · rintro ⟨tag,seen,absent⟩
      have same : tag = found.2 := Option.some.inj (seen.symm.trans tagEq)
      rw [same,ownerEq] at absent
      have absent' : ¬ Seen codec s found := by cases found <;> exact absent
      have out : found ∉ keys codec s := fun recorded => absent' ((member ..).mp recorded)
      change (!(keys codec s).contains found) = true
      cases h : (keys codec s).contains found with
      | false => rfl
      | true => exact False.elim (out (List.contains_iff_mem.mp h))

def prepend [DecidableEq Q] (codec : Codec roles Q) (cache : List (Key Q)) (p : Plan roles) :
    List (Key Q) :=
  match planKey codec p with
  | none => cache
  | some key => if key ∈ cache then cache else key :: cache

theorem prepend_mem [DecidableEq Q] (codec : Codec roles Q) (cache : List (Key Q))
    (p : Plan roles) (key : Key Q) :
    key ∈ prepend codec cache p ↔ key ∈ cache ∨ planKey codec p = some key := by
  unfold prepend
  cases found : planKey codec p with
  | none => simp
  | some x =>
    by_cases old : x ∈ cache
    · simp only [ite_eq_left old,Option.some.injEq]
      constructor
      · exact Or.inl
      · rintro (seen|rfl)
        · exact seen
        · exact old
    · simp only [ite_eq_right old,Option.some.injEq,List.mem_cons]
      constructor
      · rintro (rfl|seen)
        · exact Or.inr rfl
        · exact Or.inl seen
      · rintro (seen|rfl)
        · exact Or.inr seen
        · exact Or.inl rfl

theorem next_exact [DecidableEq Q] (codec : Codec roles Q) (s : State roles) (e : Effect roles)
    (cache : List (Key Q)) (sound : ∀ k, k ∈ cache ↔ Seen codec s k) (key : Key Q) :
    key ∈ prepend codec cache e.plan ↔ Seen codec (GeneralNominalVersionedInstall232.install s e) key := by
  rw [prepend_mem,sound,encoded]
  constructor
  · rintro (⟨p,old,id,tag⟩|⟨same,present⟩)
    · exact ⟨p,List.mem_cons_of_mem _ old,id,tag⟩
    · exact ⟨e.plan,List.mem_cons_self,same,present⟩
  · rintro ⟨p,recorded,id,tag⟩
    rcases List.mem_cons.mp recorded with rfl|older
    · exact Or.inr ⟨id,tag⟩
    · exact Or.inl ⟨p,older,id,tag⟩

theorem prepend_nodup [DecidableEq Q] (codec : Codec roles Q) (cache : List (Key Q)) (p : Plan roles)
    (nodup : cache.Nodup) : (prepend codec cache p).Nodup := by
  unfold prepend
  split
  · exact nodup
  · rename_i key found
    split
    · exact nodup
    · exact List.nodup_cons.mpr ⟨by assumption,nodup⟩

end Yulang.GeneralRebasePhaseCache281
