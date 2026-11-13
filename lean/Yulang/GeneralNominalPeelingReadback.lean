import Yulang.GeneralNominalPeelingAccessibility
import Yulang.GeneralNominalSharedEnumeration

/-! The peeling subclass has closed input readbacks from a fixed finite list.
Their shape is preserved under every actual update, so no source-hole
elimination or bound on associated-output growth is needed for this subclass. -/
namespace Yulang.GeneralNominalPeelingReadback
open GeneralNominalPeelingOrigins GeneralNominalPeelingAccessibility
open GeneralNominalOriginTerms GeneralNominalSharedEnumeration
open GeneralNominalRecursiveInspection GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualInspectionSteps
open GeneralSourceDictionaries CommonNominalFullCarrier

def expression (name : Nat) (base : Inference.Base) : Nat → Expr Origin
  | 0 => .node (.scalar base) Fin.elim0
  | depth+1 => .node (.nominal name 1) (fun _ => expression name base depth)

theorem expression_closed (name : Nat) (base : Inference.Base) (depth : Nat) :
    (expression name base depth).leaves = [] := by
  induction depth with
  | zero => simp [expression,Expr.leaves,arity]
  | succ depth ih => simp [expression,Expr.leaves,arity,ih]

theorem expression_bounded (name : Nat) (base : Inference.Base) (depth : Nat) :
    Bounded [] [.scalar base,.nominal name 1] (depth+1) (expression name base depth) := by
  induction depth with
  | zero => exact .node (.scalar base) Fin.elim0 (by simp) (fun index => Fin.elim0 index)
  | succ depth ih => exact .node (.nominal name 1) (fun _ => expression name base depth) (by simp) (fun _ => ih)

theorem expression_holds {model : GeneralNominalCommonBridge.Assignment} (depth : Nat)
    (existsValue : ∃ value, Observes model origin value)
    (values : ∀ value, Observes model origin value → Equivalent value (tower name base depth)) :
    Holds model (expression name base depth) origin := by
  induction depth generalizing origin with
  | zero => exact ⟨⟨existsValue,values⟩,fun index => Fin.elim0 index⟩
  | succ depth ih =>
    refine ⟨⟨existsValue,fun value seen => ⟨[.inl (tower name base depth)],rfl,values value seen⟩⟩,?_⟩
    intro index
    have zero : index.val = 0 := by have small := index.isLt; change index.val < 1 at small; omega
    change Holds model (expression name base depth) (.nominal origin name index.val)
    rw [zero]
    apply ih
    · obtain ⟨value,seen⟩ := existsValue
      exact ⟨tower name base depth,.nominal seen (values value seen) rfl⟩
    · intro value seen
      cases seen with
      | nominal parent equal found =>
        have known := values _ parent
        have same := (nominal_regular_invariant_exact _ _ _ _).mp (subtype_trans known.2 equal.1)
        have child := same.2.2 0 (.inl (tower name base depth)) (.inl value) rfl found
        exact ⟨child.2,child.1⟩

theorem tower_injective (equal : Equivalent (tower name base first) (tower name base last)) : first = last := by
  induction first generalizing last with
  | zero =>
    cases last with
    | zero => rfl
    | succ last => exact False.elim (base_not_nominal base name _ equal.1)
  | succ first ih =>
    cases last with
    | zero => exact False.elim (base_not_nominal base name _ equal.2)
    | succ last =>
      have same := (nominal_regular_invariant_exact _ _ _ _).mp equal.1
      have child := same.2.2 0 (.inl (tower name base first)) (.inl (tower name base last)) rfl rfl
      exact congrArg Nat.succ (ih child)

theorem equal_paths_equal_depth {model : GeneralNominalCommonBridge.Assignment}
    (rootValue : Equivalent (model identity).1 (tower name base length))
    (same : Same model (path name (.source identity) first) (path name (.source identity) last)) : first = last := by
  obtain ⟨⟨a,one⟩,⟨b,two⟩,equal⟩ := same
  obtain ⟨left,leftCount,leftValue⟩ := observed_path rootValue one
  obtain ⟨right,rightCount,rightValue⟩ := observed_path rootValue two
  have paired := equal a b one two
  have tail : Equivalent (tower name base left) (tower name base right) :=
    ⟨subtype_trans leftValue.2 (subtype_trans paired.1 rightValue.1),
      subtype_trans rightValue.2 (subtype_trans paired.2 leftValue.1)⟩
  have equal := tower_injective tail
  omega

def expressions (name : Nat) (base : Inference.Base) (length : Nat) : List (Expr Origin) :=
  (List.range (length+1)).map (expression name base)

theorem site_readback (peeling : Peeling roles registry context active name)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (live : active root.demand.role)
    (rootOrigin : (GeneralNominalDemandMerging.pointSite root).inputs[0]? = some (some (.source identity)))
    (ground : ∀ model, GeneralNominalState.Models context.state model →
      Equivalent (model identity).1 (tower name base length))
    (steps : B4Target.Steps (Step registry root) (GeneralNominalSupport.initial context root) state)
    (site : GeneralNominalDemandMerging.Site roles) (member : site ∈ state.current.sites) :
    ∃ depth, GeneralNominalInvocationAncestry.AtDepth registry context.state.seed root.identity depth site.occurrence.identity ∧
      site.inputs[0]? = some (some (path name (.source identity) depth)) ∧
      expression name base (length-depth) ∈ expressions name base length ∧
      ∀ model, Models state.current model → depth ≤ length ∧
        Holds model (expression name base (length-depth)) (path name (.source identity) depth) := by
  obtain ⟨siteActive,depth,ancestry,retained⟩ := sites_paths peeling source live rootOrigin steps site member
  refine ⟨depth,ancestry,retained,List.mem_map.mpr ⟨length-depth,List.mem_range.mpr (by omega),rfl⟩,?_⟩
  intro model valid
  have old : Models (GeneralNominalSupport.initial context root).current model := by
    clear member
    induction steps with
    | refl => exact valid
    | tail steps step ih => exact ih (GeneralNominalSharedSteps.step_models (step_shared step) model valid)
  let index : Fin (roles site.occurrence.demand.role).arity := ⟨0,by rw [peeling.unary _ siteActive]; omega⟩
  have observed := (valid.2.2 site member index _ retained).1
  have rootValue := ground model old.1
  obtain ⟨value,seen⟩ := observed
  refine ⟨observed_depth rootValue seen,expression_holds _ ⟨value,seen⟩ ?_⟩
  intro actual observed
  obtain ⟨remaining,count,same⟩ := observed_path rootValue observed
  have rest : length-depth = remaining := by omega
  simpa only [rest] using same

end Yulang.GeneralNominalPeelingReadback
