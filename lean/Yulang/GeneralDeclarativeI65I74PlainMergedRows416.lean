import Yulang.GeneralDeclarativeI65I74ClosedResidualReconstruct415

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PlainMerged416
open GeneralDeclarativeI65
open GeneralDeclarationPatterns (Pattern merge mergePayload normalize variantRow rowPattern)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeK2Graph321 (View)
open GeneralDeclarativeInspect321 (Visit PatternK2)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open Checker408 (Problem)

def sourceX6 (tag a b : Nat) : Pattern :=
  .join (.variant tag (.var a)) (.variant tag (.var b))

def mergedCode (tag a b : Nat) : Expr :=
  .variant tag (.join (.variable a) (.variable b))

theorem two_literal_plain_arms_normalize_to_one_actual_tag416 (tag a b : Nat)
    (different : a ≠ b) :
    normalize (sourceX6 tag a b) = .variant tag (.join (.var a) (.var b)) := by
  simp [sourceX6,normalize,merge,mergePayload,variantRow,rowPattern,Variants.Merged.normalize,
    Variants.Merged.Raw.insert,different]

theorem a_plain_merged_payload_does_not_enter_either_arm416
    {v : View} {root tag a b site : Nat}
    (visit : Visit v root (mergedCode tag a b) site) : site = root := by
  change Visit v root (.variant tag (.join (.variable a) (.variable b))) site at visit
  cases visit with
  | here => rfl
  | variant _ child =>
    cases child with
    | here inspect => cases inspect

def originX6 (tag payload : Nat) : CommonRecursiveNominalIntervals.Endpoint Nat :=
  .ordinary (.variant tag (.var payload))

def variantRow416 (root tag payload : Nat) : Equation :=
  ⟨root,.variant tag (.variable payload)⟩

def idempotentRow (payload : Nat) : Equation :=
  ⟨payload,.join (.variable payload) (.variable payload)⟩

def variantPayload (root tag : Nat) (row : Equation) : Bool :=
  match row.right with
  | .variant other (.variable _) => decide (row.left = root ∧ tag = other)
  | _ => false

structure PlainRows (s : I72.State) (q : I72.Request) where
  root : Nat
  tag : Nat
  payload : Nat
  different : root ≠ payload
  requested : q.demand.arguments = [point root]
  noOutputs : q.demand.outputs = []
  source : Origin
  actualSource : source ∈ s.core.origins
  sourceRoot : source.slot = root
  originalCount : (s.core.origins.filter (fun src => src.slot == root)).length = 1
  literal : source.endpoint = originX6 tag payload
  rootRow : variantRow416 root tag payload ∈ s.core.current.ordinary.equations
  uniquePayload : s.core.current.ordinary.equations.filter (variantPayload root tag) =
    [variantRow416 root tag payload]
  intRow : OpenTail414.intRow payload ∈ s.core.current.ordinary.equations
  selfRow : idempotentRow root ∈ s.core.current.ordinary.equations

def chosenPoint416 (a b same : Nat) (n : Nat) : GeneralDeclarativeWhere319.Capture :=
  if n = a ∨ n = b then point same else emptyCapture403

theorem two_binders_use_identical_actual_point416 (a b same : Nat) :
    chosenPoint416 a b same a = point same ∧ chosenPoint416 a b same b = point same := by
  simp [chosenPoint416]

theorem normalization_has_only_the_actual_variant_visit416 {s q} (r : PlainRows s q)
    {a b} (safe : ¬ AliasCycle s.core.current.ordinary (observed s.core.current.ordinary) r.root) :
    ¬ PatternK2 s.core.current.ordinary r.root (mergedCode r.tag a b) := by
  rintro ⟨atSite,visit,cycle⟩
  have exactSite := a_plain_merged_payload_does_not_enter_either_arm416 visit
  exact safe (exactSite ▸ cycle)

end Yulang.GeneralDeclarativeI65.I72.PlainMerged416
