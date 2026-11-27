import Yulang.GeneralDeclarativeI65I74RecordOrigin455

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordTrail455
open Yulang.GeneralDeclarativeI65
open RecordTraversal455 (OpenOps Trail TrailPath)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open Core.PresenceGeneration (TyTerm)

def checkOriginalRoute (s : GeneralDeclarativeI65.State) (o : Origin)
    (logical : Nat) : Bool :=
  (logical == o.slot) || s.routes.any fun r =>
    (r.logical == logical) && (r.physical == o.slot) && (r.issuer == o.issuer)

theorem original_route_iff_data455 (s : GeneralDeclarativeI65.State) (o : Origin)
    (logical : Nat) : checkOriginalRoute s o logical = true ↔ OriginRoute s o logical := by
  simp only [checkOriginalRoute,Bool.or_eq_true,List.any_eq_true,Bool.and_eq_true,beq_iff_eq]
  constructor
  · rintro (direct|⟨r,atRoute,⟨a,b⟩,c⟩)
    · subst logical
      exact .direct
    · cases r with
      | mk lo ph issuerPath =>
        dsimp only at a b c
        subst lo
        subst ph
        subst issuerPath
        exact .authored atRoute
  · intro support
    cases support with
    | direct => exact .inl rfl
    | authored found => exact .inr ⟨_,found,⟨rfl,rfl⟩,rfl⟩

def RoutedOpen (s : GeneralDeclarativeI65.State) (logical : Nat) (row : Equation) : Prop :=
  ∃ o ∈ s.origins, OriginRoute s o logical ∧ ∃ term : TyTerm Nat,
    o.slot = row.left ∧ o.endpoint = .ordinary term ∧ closedRecordTerm term = some row.right

def checkRoutedOpen (s : GeneralDeclarativeI65.State) (logical : Nat) (row : Equation)
    (ordinal : Nat) : Bool :=
  checkSourceOpen s row ordinal &&
    ((s.origins[ordinal]?).map fun orig => checkOriginalRoute s orig logical).getD false

theorem routed_open_iff_finite_same_origin_wire455
    (s : GeneralDeclarativeI65.State) (logical : Nat) (row : Equation) :
    (∃ i, checkRoutedOpen s logical row i = true) ↔ RoutedOpen s logical row := by
  constructor
  · rintro ⟨i,accept⟩
    obtain ⟨read,route⟩ := Bool.and_eq_true_iff.mp accept
    cases there : s.origins[i]? with
    | none => simp [checkSourceOpen,there] at read
    | some o =>
      have actual : OriginRoute s o logical := (original_route_iff_data455 ..).mp
        (by simpa [there] using route)
      cases typed : o.endpoint with
      | nominal key args => simp [checkSourceOpen,there,typed] at read
      | ordinary term =>
        have exact : o.slot = row.left ∧ closedRecordTerm term = some row.right := by
          simpa [checkSourceOpen,there,typed] using read
        exact ⟨o,List.mem_of_getElem? there,actual,term,exact.1,typed,exact.2⟩
  · rintro ⟨o,seen,route,term,address,typed,rowEq⟩
    obtain ⟨i,atI⟩ := List.mem_iff_getElem?.mp seen
    refine ⟨i,?_⟩
    have actual := (original_route_iff_data455 ..).mpr route
    simp [checkRoutedOpen,checkSourceOpen,atI,address,typed,rowEq,actual]

def routedOps (s : GeneralDeclarativeI65.State) : OpenOps where
  Token := Nat
  allowed := RoutedOpen s
  check := checkRoutedOpen s
  exactCheck := routed_open_iff_finite_same_origin_wire455 s

theorem routed_read_keeps_original_physical_owner_and_source_in_each_fit455
    {s : GeneralDeclarativeI65.State} {logical : Nat} {row : Equation}
    (auth : RoutedOpen s logical row) (m : I72.Model) (fit : GeneralDeclarativeI65.Fits s m) :
    ∃ o ∈ s.origins, OriginRoute s o logical ∧ o.slot = row.left ∧ ∃ ty,
      m.nativeSyntax row.left = some (.ordinary ty) ∧ closedRecordTerm ty = some row.right := by
  obtain ⟨o,seen,linked,term,owner,typed,exact⟩ := auth
  exact ⟨o,seen,linked,owner,term,by simpa only [owner,typed] using fit.2 o seen,exact⟩

theorem independent_routed_trail_observes_same_model455
    {s : GeneralDeclarativeI65.State} {root code path site}
    (actual : Trail s.current.ordinary (routedOps s) root code path site)
    (m : I72.Model) (fit : GeneralDeclarativeI65.Fits s m) :
    ModelTrail s m root code path site := by
  induction actual with
  | stop inspect => exact .stop inspect
  | down _ step _ ih =>
    obtain ⟨row,atRow,fs,rawAlias,shape,source,field,pattern⟩ := step
    obtain ⟨o,seen,route,owner,ty,native,rowEq⟩ :=
      routed_read_keeps_original_physical_owner_and_source_in_each_fit455 source m fit
    exact .down ⟨row,atRow,fs,ty,rawAlias,native,rowEq,fit.1.1.2 row atRow,shape,field,pattern⟩ ih

end Yulang.GeneralDeclarativeI65.I72.RecordTrail455
