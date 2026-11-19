import Yulang.GeneralRebaseChildPorts280

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebasePortMeaning280
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceState (Interval)
open GeneralNominalCaptureMerges (Fits equations_exact)
open GeneralNominalAllocation (equations)
open CommonNominalFullCarrier (Ty Equivalent subtype_trans subtype_refl)
open GeneralRebaseChildPorts280 (fixedSite fixed_center nonvariable_unchanged bare_capture)
open GeneralNominalVersionedFrame231 (childSite)
open GeneralDeclarationPatterns (normalize)
open PresenceNormalForm (Atom All)

def Matches (m : Assignment) (fixed original : Interval) : Prop :=
  Equivalent (m fixed.1).1 (m original.1).1 ∧
  Equivalent (m fixed.2).1 (m original.2).1

def atoms (fixed original : Interval) : List (Atom Nat) :=
  equations fixed.1 (.var original.1) ++ equations fixed.2 (.var original.2)

theorem matches_refl (m : Assignment) (p : Interval) : Matches m p p := by
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> exact subtype_refl _

theorem matches_symm (h : Matches m p q) : Matches m q p :=
  ⟨⟨h.1.2,h.1.1⟩,⟨h.2.2,h.2.1⟩⟩

theorem matches_trans (first : Matches m p q) (last : Matches m q r) : Matches m p r :=
  ⟨⟨subtype_trans first.1.1 last.1.1,subtype_trans last.1.2 first.1.2⟩,
    ⟨subtype_trans first.2.1 last.2.1,subtype_trans last.2.2 first.2.2⟩⟩

theorem atoms_exact (m : Assignment) (first last : Interval) :
    All CommonNominalFullCarrier.model m (atoms first last) ↔ Matches m first last := by
  unfold atoms Matches
  rw [PresenceNormalForm.all_append, equations_exact, equations_exact]
  rfl

theorem interval_exact (same : Matches m fixed original) (actual : Ty) :
    Fits m fixed actual ↔ Fits m original actual := by
  constructor
  · intro fit
    exact ⟨subtype_trans same.1.2 fit.1,subtype_trans fit.2 same.2.1⟩
  · intro fit
    exact ⟨subtype_trans same.1.1 fit.1,subtype_trans fit.2 same.2.2⟩

def SiteMatches (m : Assignment) (p : Plan roles) (c : Clause) (ok : c.Signature roles) : Prop :=
  ∀ i : Fin (roles c.role).arity,
    Matches m ((fixedSite p c ok).occurrence.demand.arguments i)
      ((childSite p c ok).occurrence.demand.arguments i)

def byArgAtoms (p : Plan roles) (c : Clause) (ok : c.Signature roles) (i : Fin (roles c.role).arity) :
    List (Atom Nat) :=
  match normalize (c.arguments[i.val]'(by rw [ok.1]; exact i.isLt)) with
  | .var _ => atoms ((fixedSite p c ok).occurrence.demand.arguments i)
      ((childSite p c ok).occurrence.demand.arguments i)
  | _ => []

def clauseAtoms (p : Plan roles) (c : Clause) (ok : c.Signature roles) : List (Atom Nat) :=
  (List.finRange (roles c.role).arity).flatMap (byArgAtoms p c ok)

theorem arg_atoms (m : Assignment) (p : Plan roles) (c : Clause) (ok : c.Signature roles)
    (i : Fin (roles c.role).arity) :
    All CommonNominalFullCarrier.model m (byArgAtoms p c ok i) ↔
      Matches m ((fixedSite p c ok).occurrence.demand.arguments i)
        ((childSite p c ok).occurrence.demand.arguments i) := by
  unfold byArgAtoms
  cases form : normalize (c.arguments[i.val]'(by rw [ok.1]; exact i.isLt))
  case var => exact atoms_exact ..
  all_goals
    rw [show (fixedSite p c ok).occurrence.demand.arguments i =
        (childSite p c ok).occurrence.demand.arguments i from nonvariable_unchanged _ _ _ _ (by
      intro name contradiction
      rw [form] at contradiction
      cases contradiction)]
    exact ⟨fun _ => matches_refl _ _,fun _ => PresenceNormalForm.all_nil _ _⟩

theorem clause_atoms (m : Assignment) (p : Plan roles) (c : Clause) (ok : c.Signature roles) :
    All CommonNominalFullCarrier.model m (clauseAtoms p c ok) ↔ SiteMatches m p c ok := by
  constructor
  · intro held i
    apply (arg_atoms ..).mp
    intro atom used
    exact held atom (List.mem_flatMap.mpr ⟨i,List.mem_finRange i,used⟩)
  · intro held atom present
    obtain ⟨i,_,member⟩ := List.mem_flatMap.mp present
    exact (arg_atoms ..).mpr (held i) atom member

theorem site_holds (matchArgs : SiteMatches m p c ok) :
    (fixedSite p c ok).Holds m ↔ (childSite p c ok).Holds m := by
  constructor <;> intro holds i
  · exact (interval_exact (matchArgs i) _).mp (holds i)
  · exact (interval_exact (matchArgs i) _).mpr (holds i)

theorem actual_origins (p : Plan roles) (c : Clause) (ok : c.Signature roles) :
    (fixedSite p c ok).observed.inputs = (childSite p c ok).observed.inputs := rfl

theorem observed_holds (matchArgs : SiteMatches m p c ok) :
    GeneralNominalSaturationState.SiteHolds (fixedSite p c ok).observed m ↔
      GeneralNominalSaturationState.SiteHolds (childSite p c ok).observed m := by
  constructor <;> intro holds i origin entry
  · obtain ⟨nonempty,fit⟩ := holds i origin entry
    exact ⟨nonempty,fun value read => (interval_exact (matchArgs i) value).mp (fit value read)⟩
  · obtain ⟨nonempty,fit⟩ := holds i origin entry
    exact ⟨nonempty,fun value read => (interval_exact (matchArgs i) value).mpr (fit value read)⟩

theorem nonvariable_no_atoms (p : Plan roles) (c : Clause) (ok : c.Signature roles)
    (i : Fin (roles c.role).arity)
    (nonvariable : ∀ name, normalize (c.arguments[i.val]'(by rw [ok.1]; exact i.isLt)) ≠ .var name) :
    byArgAtoms p c ok i = [] := by
  unfold byArgAtoms
  split
  · rename_i name found
    exact False.elim (nonvariable name found)
  all_goals rfl

end Yulang.GeneralRebasePortMeaning280
