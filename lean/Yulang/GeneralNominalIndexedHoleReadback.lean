import Yulang.GeneralNominalHolePhaseSimulation

/-! Source-indexed opaque leaves and actual-step substitution. A source
identity always uses its first frontier index, so repeated uses share a leaf.
No finite closed meaning of an unresolved leaf is required. -/
namespace Yulang.GeneralNominalIndexedHoleReadback
open GeneralNominalOriginTerms GeneralNominalRecursiveInspection GeneralNominalHoleElimination
open GeneralNominalSaturationState GeneralNominalSupport GeneralNominalActualInspectionSteps
open GeneralSourceDictionaries

variable {roles : Roles.RoleDecls}

def origin (frontier : List Origin) (index : Nat) : Origin :=
  (frontier[index]?).getD (.source 0)

def holes (frontier : List Origin) : List Nat := List.range frontier.length

def index (frontier : List Origin) (source : Nat) : Nat := frontier.idxOf (.source source)

def interpret (origins : Nat → Origin) (term : Expr Nat) : Expr Origin :=
  term.bind (fun name => .leaf (origins name))

def Readback (models : GeneralNominalCommonBridge.Assignment → Prop) (origins : Nat → Origin)
    (remaining : List Nat) (root : Origin) (term : Expr Nat) : Prop :=
  (∀ model, models model → Holds model (interpret origins term) root) ∧ Closed remaining term

theorem index_origin (member : Origin.source source ∈ frontier) :
    origin frontier (index frontier source) = .source source := by
  have bounded := List.idxOf_lt_length_of_mem member
  simp only [origin,index,List.getElem?_eq_getElem bounded,Option.getD_some]
  exact List.getElem_idxOf bounded

theorem source_leaf (member : Origin.source source ∈ frontier) :
    Readback models (origin frontier) (holes frontier) (.source source) (.leaf (index frontier source)) := by
  constructor
  · intro model valid
    change Same model (.source source) (origin frontier (index frontier source))
    rw [index_origin member]
    exact source_self model source
  · intro name present
    cases List.mem_singleton.mp present
    exact List.mem_range.mpr (List.idxOf_lt_length_of_mem member)

theorem initial_root {root : Occurrence roles}
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (position : Fin (roles root.demand.role).arity) :
    Readback (Models (GeneralNominalSupport.initial context root).current)
      (origin (GeneralNominalSourceFrontier.frontier context.state))
      (holes (GeneralNominalSourceFrontier.frontier context.state))
      (.source (root.demand.arguments position).1)
      (.leaf (index (GeneralNominalSourceFrontier.frontier context.state) (root.demand.arguments position).1)) :=
  source_leaf (GeneralNominalSourceFrontier.initial_inputs source position).1

theorem same_source_index (same : first = last) : index frontier first = index frontier last := by rw [same]

theorem restrict (readback : Readback before origins remaining root term)
    (restriction : ∀ model, after model → before model) : Readback after origins remaining root term :=
  ⟨fun model valid => readback.1 model (restriction model valid),readback.2⟩

theorem step_preserves (step : Step registry focus before after)
    (readback : Readback (Models before.current) origins remaining root term) :
    Readback (Models after.current) origins remaining root term :=
  restrict readback (GeneralNominalSharedSteps.step_models (step_shared step))

theorem replace_holds (term : Expr Nat)
    (old : Holds model (interpret origins term) root)
    (replacement : Holds model (interpret origins value) (origins hole)) :
    Holds model (interpret origins (replace hole value term)) root := by
  induction term generalizing root with
  | leaf name =>
    by_cases same : name = hole
    · subst name
      simpa only [replace,substitute,Expr.bind,ite_true] using
        holds_transport (same_symm old) replacement
    · simpa only [replace,substitute,Expr.bind,same,ite_false] using old
  | node test children ih =>
    exact ⟨old.1,fun position => ih position (old.2 position)⟩

theorem eliminate_readback (readback : Readback models origins remaining root term)
    (replacement : Readback models origins (remaining.erase hole) (origins hole) value) :
    Readback models origins (remaining.erase hole) root (replace hole value term) :=
  ⟨fun model valid => replace_holds term (readback.1 model valid) (replacement.1 model valid),
    replacement_closed readback.2 replacement.2⟩

/-- The same substitution is applied to every represented origin, including
aliases and repeated declaration-variable uses. Only the replacement's actual
readback is a premise; its extraction from an update is not supplied here. -/
theorem actual_elimination {represented : Origin → Expr Nat → Prop} (step : Step registry focus before after)
    (readbacks : ∀ root term, represented root term → Readback (Models before.current) origins remaining root term)
    (replacement : Readback (Models after.current) origins (remaining.erase hole) (origins hole) value) :
    ∀ root term, represented root term →
      Readback (Models after.current) origins (remaining.erase hole) root (replace hole value term) :=
  fun root term recorded => eliminate_readback (step_preserves step (readbacks root term recorded)) replacement

theorem project (readback : Readback models origins remaining root (.node test children))
    (position : Fin (arity test)) :
    Readback models origins remaining (GeneralNominalOriginTerms.project root test position) (children position) := by
  refine ⟨fun model valid => (readback.1 model valid).2 position,?_⟩
  intro name present
  apply readback.2 name
  simp only [Expr.leaves,List.mem_flatten,List.mem_ofFn]
  exact ⟨_,⟨position,rfl⟩,present⟩

theorem alias (readback : Readback models origins remaining first term)
    (same : ∀ model, models model → Same model first last) : Readback models origins remaining last term :=
  ⟨fun model valid => holds_transport (same model valid) (readback.1 model valid),readback.2⟩

end Yulang.GeneralNominalIndexedHoleReadback
