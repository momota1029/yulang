import Yulang.GeneralDeclarativeI65I74ListFrameHead449

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ListSites449.Frame
open Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWitnessConstructorModes357 (readUse)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open PresenceNormalForm (Atom)
open List410 (listPoint410 invariantValue410)

def readSite (s : GeneralDeclarativeI65.State) (arg : Capture) (h : Pattern)
    (position : Nat) : Option (WrittenListSite s arg h) := do
  match authored : h with
  | .app key [.var binder] =>
    match originalAt : s.origins[position]? with
    | some origin =>
      match proof : origin.endpoint with
      | .nominal n [.inl (.point (.ordinary (.var payload)))] =>
        if slots : n = key ∧ origin.slot = arg.lower ∧ origin.slot = arg.center ∧ origin.slot = arg.upper then
          let action ← readUse s.current.environment key 1
          if mode : names action.mode 1 = some [invariantValue410] then
            if table : s.modes[key]? = some [invariantValue410] then
              if atom : (Atom.tyLe (.var payload) (.var payload) : Atom Nat) ∈ s.current.ordinary.normal.ordinary then
                some ⟨key,binder,authored,origin,List.mem_of_getElem? originalAt,slots.2.1,slots.2.2.1,
                  slots.2.2.2,payload,by rw [proof,slots.1]; rfl,action,mode,table,atom⟩
              else none
            else none
          else none
        else none
      | _ => none
    | none => none
  | _ => none

theorem read_exact_site_data449 {s arg h} (a : WrittenListSite s arg h) (i : Nat)
    (original : s.origins[i]? = some a.origin) :
    readSite s arg h i = some a := by
  cases a with
  | mk key bind head origin present low center upper payload endpoint use mode table atom =>
    subst h
    unfold readSite
    dsimp only
    split
    · rename_i atOrigin got
      have same := Option.some.inj (got.symm.trans original)
      subst atOrigin
      split
      · rename_i name atPayload read
        change origin.endpoint = listPoint410 name atPayload at read
        have exactPair := CommonRecursiveNominalIntervals.Endpoint.nominal.inj
          (read.symm.trans endpoint)
        have kEq := exactPair.1
        have pEq := Core.PresenceGeneration.TyTerm.var.inj
          (CommonRecursiveNominalIntervals.Endpoint.ordinary.inj
            (CommonRecursiveNominalIntervals.Bounds.point.inj
              (Sum.inl.inj (List.singleton_inj.mp exactPair.2))))
        subst name
        subst atPayload
        rw [dite_eq_left (show key = key ∧ _ from ⟨rfl,low,center,upper⟩)]
        rw [RetainedFull445.read_use_reconstructs_exact_placement445 use]
        simp only [Bind.bind,Option.bind]
        rw [dite_eq_left mode,dite_eq_left table,dite_eq_left atom]
      · rename_i wrong
        exact (wrong _ _ endpoint).elim
    · rename_i miss
      rw [original] at miss
      cases miss

def readAuthoredFrame (s : GeneralDeclarativeI65.State) :
    (args : List Capture) → (heads : List Pattern) → List Nat → Option (AuthoredFrame s args heads)
  | [],[],[] => some .nil
  | arg::args,head::heads,source::origins => do
    let hit ← readSite s arg head source
    let rest ← readAuthoredFrame s args heads origins
    pure (.cons hit rest)
  | _,_,_ => none

theorem independent_frame_has_exact_origin_indices449 {s args heads} (a : AuthoredFrame s args heads) :
    ∃ positions : List Nat, readAuthoredFrame s args heads positions = some a := by
  induction a with
  | nil => exact ⟨[],rfl⟩
  | cons site tail ih =>
    obtain ⟨i,found⟩ := List.mem_iff_getElem?.mp site.authored
    obtain ⟨positions,rest⟩ := ih
    refine ⟨i :: positions,?_⟩
    simp [readAuthoredFrame,read_exact_site_data449 site i found,rest,
      Bind.bind,Option.bind,Option.pure_def]

end Yulang.GeneralDeclarativeI65.I72.ListSites449.Frame
