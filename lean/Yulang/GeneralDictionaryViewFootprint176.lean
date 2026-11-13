import Yulang.GeneralDictionaryFinishedRefresh
import Yulang.GeneralDictionaryRefinementInspectionFacts

namespace Yulang.GeneralDictionaryViewFootprint176
open GeneralNominalInspection (Query Bounds)
open GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates (Context)
open GeneralDictionaryInspectionTransport
open GeneralDictionaryInspectionLocality
open GeneralDictionaryRefreshDescriptors
open GeneralDictionaryRefinementInspectionFacts
open GeneralDictionaryFinishedRefresh

/-- Fixed carrier and shape catalogue; source heads and nominal descriptors
may change. The normalization and opacity certificates remain mandatory. -/
structure HeadObservation (state : GeneralNominalState.State) where
  heads : Fin state.base.slots → GeneralNormalizedObservation.Head state.view.shapes state.base.slots
  checked : ∀ slot term, (heads slot).term = some term →
    GeneralNormalizedObservation.Rewrites state.base (.var slot) term
  nominals : Fin state.base.slots → Option (GeneralNominalState.Descriptor state.base.slots)
  catalogue : ∀ slot descriptor, nominals slot = some descriptor →
    state.constructors descriptor.constructor = some descriptor.declaration
  bodiesOpaque : ∀ slot descriptor, nominals slot = some descriptor →
    heads slot = .deferred .unresolved

def HeadObservation.view (next : HeadObservation state) : GeneralNormalizedObservation.Snapshot state.base :=
  {state.view with heads := next.heads, checked := next.checked}

def HeadObservation.observation (next : HeadObservation state) : Observation state :=
  ⟨next.view,next.nominals,next.catalogue,next.bodiesOpaque⟩
instance : Coe (HeadObservation state) (Observation state) := ⟨HeadObservation.observation⟩

/-! Finite recursive equality guard for normalized observations. The shape catalogue stays fixed globally. Only scalar
lower heads and structural endpoint heads traversed by the query are compared. Nominal descriptors are preserved by Refines; variable
leaves inspect no view. This is conservative, not a minimal footprint. -/
mutual
 def Agrees (context : Context) (next : HeadObservation context.state)
     (query : Query) (bounds : Bounds context.state) : Prop :=
   match query with
   | .variables _ | .deferred _ => True
   | .scalar _ => next.heads bounds.1 = context.state.view.heads bounds.1
   | .node _ patterns =>
       next.heads bounds.1 = context.state.view.heads bounds.1 ∧
       next.heads bounds.2 = context.state.view.heads bounds.2 ∧
       match context.state.view.heads bounds.1, context.state.view.heads bounds.2 with
       | .structural lower children, .structural upper targets =>
         AgreeMany context next patterns ((List.ofFn children).zip (List.ofFn targets))
       | _,_ => True
   | .nominal _ patterns =>
       (∀ descriptor, context.state.nominals bounds.1 = some descriptor →
         ∀ arguments, typeArguments descriptor.arguments = some arguments →
           AgreeMany context next patterns arguments) ∧
       (∀ descriptor, context.state.nominals bounds.2 = some descriptor →
         ∀ arguments, typeArguments descriptor.arguments = some arguments →
           AgreeMany context next patterns arguments)
 termination_by sizeOf query
 def AgreeMany (context : Context) (next : HeadObservation context.state) :
     List Query → List (Bounds context.state) → Prop
   | query :: queries, bound :: bounds => Agrees context next query bound ∧ AgreeMany context next queries bounds
   | _,_ => True
 termination_by queries _ => sizeOf queries
end

mutual
 theorem inspect_finished (context : Context) (next : HeadObservation context.state)
        (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (query : Query) (bounds : Bounds context.state) (origin : Option Origin)
    (same : Agrees context next query bounds)
    (finished : Finished (inspect context.state query bounds origin)) :
    inspect (reobserve context next).state query bounds origin =
      transferReport context next (inspect context.state query bounds origin) := by
  cases query with
  | variables names => simp only [inspect,transferReport,capture,List.map_map,Function.comp_def]
  | deferred term => exact False.elim (block_not_finished bounds (by simpa only [inspect] using finished))
  | scalar expected =>
    simp only [Agrees] at same
    cases recorded : context.state.nominals bounds.1 with
    | some descriptor => simp [inspect,recorded,Finished,Report.visit] at finished
    | none =>
      cases head : context.state.view.heads bounds.1 with
      | deferred reason => simp [inspect,recorded,head,Finished,Report.visit,block] at finished
      | structural kind children => simp [inspect,recorded,head,Finished,Report.visit] at finished
      | scalar actual =>
        have none : next.nominals bounds.1 = none := by
          cases found : next.nominals bounds.1 with
          | none => rfl
          | some descriptor =>
            have hidden := next.bodiesOpaque bounds.1 descriptor found
            rw [show next.heads bounds.1 = context.state.view.heads bounds.1 from same,head] at hidden
            cases hidden
        simp only [inspect,reobserve,HeadObservation.observation,HeadObservation.view,recorded,none,show next.heads bounds.1 = context.state.view.heads bounds.1 from same,head]
        split <;> rfl
  | node expected patterns =>
    simp only [Agrees] at same
    have low := same.1
    have high := same.2.1
    have rest := same.2.2
    simp only [inspect] at finished
    simp only [inspect,reobserve,HeadObservation.observation,HeadObservation.view,low,high]
    split
    · rename_i lower children upper targets observed
      simp only [observed,targets] at rest
      split
      · rename_i shapes
        have recursive := inspectMany_finished context next refinement patterns _ (fun index => origin.map fun parent => .structural parent expected index) 0 rest
          (by simpa only [observed,targets,shapes,and_self,ite_true,finished_visit] using finished)
        dsimp only [reobserve,HeadObservation.observation,HeadObservation.view] at recursive
        rw [recursive]
        rfl
      · rfl
    · rfl
    · rfl
  | nominal expected patterns =>
    simp only [Agrees] at same
    obtain ⟨lower,recorded⟩ := finished_nominal_lower context.state expected patterns bounds origin finished
    obtain ⟨upper,upperRecorded⟩ := finished_nominal_upper context.state expected patterns bounds origin finished
    have low := descriptor_preserved context next refinement bounds.1 lower recorded
    have high := descriptor_preserved context next refinement bounds.2 upper upperRecorded
    dsimp only [HeadObservation.observation] at low high
    simp only [inspect,recorded,upperRecorded] at finished
    simp only [inspect,reobserve,HeadObservation.observation,HeadObservation.view,recorded,upperRecorded,low,high]
    split
    · rename_i lowName
      split
      · rfl
      · rename_i arguments arguments_eq
        split
        · rename_i point
          have recursive := inspectMany_finished context next refinement patterns arguments (fun index => some (.nominal (origin.getD (.source (context.state.base.source bounds.1))) expected index)) 0 (same.1 lower recorded arguments arguments_eq) (by simpa only [lowName,arguments_eq,point,ite_true,finished_visit] using finished)
          dsimp only [reobserve,HeadObservation.observation,HeadObservation.view] at recursive
          rw [recursive]
          rfl
        · rename_i nonpoint
          split
          · rename_i highName
            split
            · rfl
            · rename_i targets targets_eq
              simp only [lowName,highName,arguments_eq,nonpoint,ite_false,targets_eq,ite_true,finished_visit] at finished
              have both := (finished_append _ _).mp finished
              have left := inspectMany_finished context next refinement patterns arguments (fun index => some (.nominal (origin.getD (.source (context.state.base.source bounds.1))) expected index)) 0 (same.1 lower recorded arguments arguments_eq) both.1
              have right := inspectMany_finished context next refinement patterns targets (fun index => some (.nominal (origin.getD (.source (context.state.base.source bounds.2))) expected index)) 0 (same.2 upper upperRecorded targets targets_eq) both.2
              dsimp only [reobserve,HeadObservation.observation,HeadObservation.view] at left right
              rw [left,right]
              simp only [transfer_visit,transfer_append]
          · rfl
    · rfl
 termination_by sizeOf query
 theorem inspectMany_finished (context : Context) (next : HeadObservation context.state)
        (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (queries : List Query) (bounds : List (Bounds context.state)) (origins : Nat → Option Origin) (index : Nat)
    (same : AgreeMany context next queries bounds)
    (finished : Finished (inspectMany context.state queries bounds origins index)) :
    inspectMany (reobserve context next).state queries bounds origins index =
      transferReport context next (inspectMany context.state queries bounds origins index) := by
  cases queries with
  | nil => cases bounds <;> simp only [inspectMany,transferReport] <;> rfl
  | cons query queries =>
    cases bounds with
    | nil => simp only [inspectMany,transferReport]; rfl
    | cons bound bounds =>
      simp only [AgreeMany] at same
      simp only [inspectMany] at finished
      have both := (finished_append _ _).mp finished
      rw [inspectMany,inspectMany,
        inspect_finished context next refinement query bound (origins index) same.1 both.1,
        inspectMany_finished context next refinement queries bounds origins (index+1) same.2 both.2,transfer_append]
 termination_by sizeOf queries
end


open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalRecursiveCandidates (arguments report RequestReady)
open GeneralNominalCommonBridge (Assignment)
theorem report_finished (context : Context) (next : HeadObservation context.state)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (declaration : Declaration) (bounds : List (GeneralNominalInspection.Bounds context.state))
    (same : AgreeMany context next
      (GeneralNominalInspection.queries context.state context.interpretation declaration) bounds)
    (finished : Finished (report context declaration bounds)) :
    report (reobserve context next) declaration bounds = transferReport context next (report context declaration bounds) := by
  unfold report at finished ⊢
  have queries : GeneralNominalInspection.queries (reobserve context next).state
      (reobserve context next).interpretation declaration =
      GeneralNominalInspection.queries context.state context.interpretation declaration := rfl
  rw [queries]
  rw [inspectMany_finished context next refinement _ bounds (fun _ => none) 0 same finished]
  rfl

/-- The target model is explicit. The guard is finite query/head equality,
not semantic evidence; unqueried source heads remain unconstrained. -/
theorem instance_refinement (registry : Registry) (context : Context) (next : HeadObservation context.state)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (model : Assignment) (valid : GeneralNominalState.Models (reobserve context next).state model)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (same : ∀ declaration ∈ registry.declarations, declaration.role = root.demand.role →
      ∀ bounds, arguments context root = some bounds → AgreeMany context next
        (GeneralNominalInspection.queries context.state context.interpretation declaration) bounds)
    (old : GeneralDictionaryRecursiveEvidence.Instance registry context model root key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry (reobserve context next) model root key children := by
  obtain ⟨declaration,visible,checked,identity,role,bounds,located,finished,ready,emitted,metadata,branch⟩ := old
  have reports := report_finished context next refinement declaration bounds (same declaration visible role bounds located) finished
  refine ⟨declaration,visible,checked,identity,role,bounds,located,?_,?_,?_,metadata,
    branch_of_report registry context next root declaration checked bounds model reports valid branch⟩
  · rw [reports,transferred_finished]
    exact finished
  · unfold RequestReady at ready ⊢
    rw [generated_eq registry context next root declaration checked bounds reports]
    exact ready
  · rw [reports,transferred_bindings]
    exact emitted


end Yulang.GeneralDictionaryViewFootprint176
