import Yulang.GeneralMixedFullControlMinimal306
import Yulang.GeneralMixedFullControlTrace306

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedFullControlMinimalRaw306
open GeneralMixedFullControlCode306 (Code Event Action code fire)
open GeneralMixedFullControlUnlabelled306 (ControlClass classify classTargets raw_class_exact targets raw_exact all_codes)
open GeneralMixedFullControlMinimal306 (CodeBisim each_bisim_respects_classes)
open GeneralMixedFullControlTrace306 (all_constructible)
open GeneralMixedControlMask306 (get)
open GeneralDictionaryOutputDepth252 (initial roles registry root)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralRebaseDepthPathRank285 (ActualPath)

def Reach (s : State roles) : Prop := ∃ n, ActualPath initial s n

def RawBisim (rel : State roles → State roles → Prop) : Prop :=
  ∀ s t, Reach s → Reach t → rel s t →
    (∀ s', Step registry root s s' → ∃ t', Step registry root t t' ∧ rel s' t') ∧
    (∀ t', Step registry root t t' → ∃ s', Step registry root s s' ∧ rel s' t')

theorem bisim_on_codes {rel : State roles → State roles → Prop} (b : RawBisim rel) :
    CodeBisim (fun x y => ∃ s t, Reach s ∧ Reach t ∧ rel s t ∧ code s = x ∧ code t = y) := by
  rintro x y ⟨s,t,⟨ns,ps⟩,⟨nt,pt⟩,linked,rfl,rfl⟩
  have two := b s t ⟨ns,ps⟩ ⟨nt,pt⟩ linked
  constructor
  · intro a member
    obtain ⟨s',hop,same⟩ := (raw_exact ps a).mp (List.mem_filter.mp member).2
    obtain ⟨t',copied,witness⟩ := two.1 s' hop
    exact ⟨code t',List.mem_filter.mpr ⟨all_codes _,(raw_exact pt _).mpr ⟨t',copied,rfl⟩⟩,
      s',t',⟨_,.more ps hop⟩,⟨_,.more pt copied⟩,witness,same,rfl⟩
  · intro b member
    obtain ⟨t',hop,same⟩ := (raw_exact pt b).mp (List.mem_filter.mp member).2
    obtain ⟨s',copied,witness⟩ := two.2 t' hop
    exact ⟨code s',List.mem_filter.mpr ⟨all_codes _,(raw_exact ps _).mpr ⟨s',copied,rfl⟩⟩,
      s',t',⟨_,.more ps copied⟩,⟨_,.more pt hop⟩,witness,rfl,same⟩

theorem any_raw_bisim_respects_classes {rel : State roles → State roles → Prop}
    (b : RawBisim rel) {s t : State roles} (ps : Reach s) (pt : Reach t) (h : rel s t) :
    classify (code s) = classify (code t) :=
  each_bisim_respects_classes (bisim_on_codes b) _ _ ⟨s,t,ps,pt,h,rfl,rfl⟩

theorem raw_classes_bisim : RawBisim (fun s t => classify (code s) = classify (code t)) := by
  rintro s t ⟨ns,ps⟩ ⟨nt,pt⟩ same
  constructor
  · intro s' hop
    have edge := (raw_class_exact ps _).mp ⟨s',hop,rfl⟩
    rw [same] at edge
    obtain ⟨t',step,tag⟩ := (raw_class_exact pt _).mpr edge
    exact ⟨t',step,tag.symm⟩
  · intro t' hop
    have edge := (raw_class_exact pt _).mp ⟨t',hop,rfl⟩
    rw [← same] at edge
    obtain ⟨s',step,tag⟩ := (raw_class_exact ps _).mpr edge
    exact ⟨s',step,tag⟩

def representative : ControlClass → Code
  | .halted => ⟨true,⟨true,true⟩⟩
  | .oneLeft => ⟨false,⟨true,true⟩⟩
  | .batchable => ⟨true,⟨false,false⟩⟩
  | .separate => ⟨false,⟨true,false⟩⟩
  | .threeLeft => ⟨false,⟨false,false⟩⟩

theorem each_class_reached (c : ControlClass) : ∃ s : State roles, Reach s ∧ classify (code s) = c := by
  obtain ⟨s,n,real,same⟩ := all_constructible (representative c)
  refine ⟨s,⟨n,real⟩,?_⟩
  rw [same]
  cases c <;> rfl

theorem enable_install (x : Code) :
    (∃ y, fire .install x y = true) ↔ x.installed = false := by
  constructor
  · rintro ⟨y,step⟩
    have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp step).1).1
    simpa only [Bool.not_eq_true'] using h
  · intro openNow
    exact ⟨⟨true,x.scalars⟩,by simp [fire,openNow]⟩

theorem enable_scalar (x : Code) (q : Fin 2) :
    (∃ y, fire (.scalar q) x y = true) ↔ get x.scalars q = false := by
  constructor
  · rintro ⟨y,edge⟩
    exact ((GeneralMixedControlMask306.fire_exact q x.scalars y.scalars).mp
      (Bool.and_eq_true_iff.mp edge).2).2.1
  · intro missing
    exact ⟨⟨x.installed,GeneralMixedControlLiveness306.full⟩,
      Bool.and_eq_true_iff.mpr ⟨decide_eq_true rfl,
        (GeneralMixedControlLiveness306.full_triggers _ q).mpr missing⟩⟩

theorem label_signature_exact (x y : Code) :
    (∀ e : Event, (∃ t, fire e x t = true) ↔ (∃ t, fire e y t = true)) ↔ x = y := by
  constructor
  · intro same
    apply Code.ext
    · have v := (enable_install x).symm.trans ((same .install).trans (enable_install y))
      cases hx : x.installed <;> cases hy : y.installed <;> simp [hx,hy] at v ⊢
    · apply GeneralMixedControlBisim306.is_equal_of_bits
      intro q
      have v := (enable_scalar x q).symm.trans ((same (.scalar q)).trans (enable_scalar y q))
      cases hx : get x.scalars q <;> cases hy : get y.scalars q <;> simp [hx,hy] at v ⊢
  · rintro rfl _
    exact Iff.rfl

theorem raw_label_signature {s t : State roles} (ps : Reach s) (pt : Reach t) :
    (∀ e : Event, (∃ x, Action e s x) ↔ (∃ x, Action e t x)) ↔ code s = code t := by
  obtain ⟨ns,ps⟩ := ps
  obtain ⟨nt,pt⟩ := pt
  have eq {u : State roles} {n : Nat} (path : ActualPath initial u n) (e : Event) :
      (∃ dest, Action e u dest) ↔ (∃ c, fire e (code u) c = true) := by
    constructor
    · rintro ⟨d,h⟩
      exact ⟨_,GeneralMixedFullControlStep306.forward path h⟩
    · rintro ⟨c,h⟩
      obtain ⟨d,ok,_⟩ := GeneralMixedFullControlStep306.lifts path e c h
      exact ⟨d,ok⟩
  rw [← label_signature_exact]
  exact ⟨fun h e => (eq ps e).symm.trans ((h e).trans (eq pt e)),
    fun h e => (eq ps e).trans ((h e).trans (eq pt e).symm)⟩

end Yulang.GeneralMixedFullControlMinimalRaw306
