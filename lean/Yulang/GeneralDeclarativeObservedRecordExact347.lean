import Yulang.GeneralDeclarativeObservedRecordPair347

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeObservedRecordExact347
open GeneralNominalState (State Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeOrigins321 (Supported Origin)
open GeneralDeclarativeObservedSupport347 (arg attach)
open GeneralDeclarativeObservedRecord347 (Walk)
open GeneralDeclarativeWherePairView346 (extendBounds preserve)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeEndpointRecord336 (Read)
open GeneralDeclarativeEndpointProgram336 (ready list_sound template)
open GeneralNominalCenters (Site)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleCanonicalRows (Row normalize)
open GeneralDeclarativeExactOverlay337 (ModelsExact approved)
open GeneralDeclarativeEndpointOverlay336 (receipts spans footprintKeep span_order)
open GeneralDeclarativeEndpointBatch336 (prepare)
open GeneralDeclarativeFootprint321 (stateNames)

theorem materializes {raw : State} {base : GeneralDeclarativeHead320.State}
    {author : Equation → Origin → Prop} (prior : Supported base done)
    (site : Site rs) (index : Fin (rs site.occurrence.demand.role).arity)
    {ls us : Row Expr} {le ue : Expr} {lsRows usRows : List Equation}
    (lower : Walk raw done author (arg site index).lower ls le lsRows)
    (upper : Walk raw done author (arg site index).upper us ue usRows)
    (shape : List (Nat × Nat)) (tail : Nat) (distinct : (shape.map Prod.fst).Nodup)
    (loKeys : shape.map Prod.fst ⊆ (normalize ls).map Prod.fst)
    (hiKeys : shape.map Prod.fst ⊆ (normalize us).map Prod.fst)
    (m : Assignment) (typed : site.Holds m) (rawFit : Models raw m)
    (fit : GeneralDeclarativeHead320.Models base m) (protect : List Nat) :
    let cap := arg site index
    let rows := lsRows ++ usRows
    let observed := appendFacts (extendBounds base cap) rows
    let supported := attach (preserve prior cap) raw author rows
    ∃ l h jobs n,
      Read supported cap (shape.map Prod.fst) ls us l h le ue ∧
      ready cap shape tail ls us l h le ue = some jobs ∧
      ModelsExact (prepare observed (footprintKeep protect jobs) jobs.length)
        (receipts observed (footprintKeep protect jobs) jobs) n ∧
      (spans observed (footprintKeep protect jobs) jobs).map Prod.fst = (template shape tail).variables ∧
      ∀ v ∈ stateNames observed ++ protect, n v = m v := by
  dsimp only
  obtain ⟨l,h,jobs,auth,built,grown⟩ := GeneralDeclarativeObservedRecordPair347.produces
    prior site index lower upper shape tail distinct loKeys hiKeys m typed rawFit fit
  obtain ⟨n,legal,guard⟩ := approved auth built m grown protect
  refine ⟨l,h,jobs,n,auth,built,legal,?_,?_⟩
  · rw [span_order]
    exact (list_sound auth built).1
  · intro k mem
    apply guard k
    exact (List.mem_append.mp mem).elim (List.mem_append_left _)
      (fun bit => List.mem_append_right _ (List.mem_append_right _ bit))

end Yulang.GeneralDeclarativeObservedRecordExact347
