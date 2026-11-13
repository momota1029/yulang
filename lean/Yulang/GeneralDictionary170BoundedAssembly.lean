import Yulang.GeneralDictionary170NamedAccessible

/-! Fuel-bounded assembly from local structural coverage. The bound concerns a
fixed dictionary graph, never saturation steps or arbitrary language inputs. -/
namespace Yulang.GeneralDictionary170BoundedAssembly
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionaryReadback GeneralDictionary170NamedCoverage
open GeneralDictionary170NamedAccessible
open CommonRoleOutermostResolver (All₂)
open GeneralDictionary169NamedTree (NamedTree)
variable {roles : Roles.RoleDecls}

/-- Traverse in source child order; one failed child makes the node fail. -/
def collect (sites : List (Occurrence roles))
    (run : ∀ child, child ∈ sites → Option Payload) : Option (List Payload) :=
  match sites with
  | [] => some []
  | child :: rest => do
      let payload ← run child (by simp)
      let payloads ← collect rest (fun next member => run next (by simp [member]))
      pure (payload :: payloads)

def assemble (coverage : Coverage registry state domain) : Nat → Subtype domain → Option Payload
  | 0, _ => none
  | fuel + 1, focus => do
      let node := coverage.node focus.val focus.property
      let payloads ← collect node.children (fun child member =>
        assemble coverage fuel ⟨child,coverage.closed focus.val focus.property child member⟩)
      pure (.node node.key payloads)

private theorem collect_complete (sites : List (Occurrence roles))
    (run : ∀ child, child ∈ sites → Option Payload)
    (works : ∀ child member, ∃ payload, run child member = some payload ∧
      NamedTree registry state child payload) :
    ∃ payloads, collect sites run = some payloads ∧ All₂ (NamedTree registry state) sites payloads := by
  induction sites with
  | nil => exact ⟨[],rfl,.nil⟩
  | cons child rest ih =>
    obtain ⟨payload,computed,tree⟩ := works child (by simp)
    obtain ⟨payloads,computedRest,trees⟩ := ih
      (fun next member => run next (by simp [member]))
      (fun next member => works next (by simp [member]))
    refine ⟨payload :: payloads,?_,.cons tree trees⟩
    simp only [collect,computed,computedRest]
    rfl

theorem enough_fuel (coverage : Coverage registry state domain) (fuel : Nat)
    (focus : Subtype domain) (enough : rank state focus.val < fuel) :
    ∃ payload, assemble coverage fuel focus = some payload ∧ NamedTree registry state focus.val payload := by
  induction fuel generalizing focus with
  | zero => omega
  | succ fuel ih =>
    let node := coverage.node focus.val focus.property
    obtain ⟨payloads,computed,trees⟩ := collect_complete node.children
      (fun child member => assemble coverage fuel ⟨child,coverage.closed focus.val focus.property child member⟩)
      (by
        intro child member
        apply ih
        have decrease := child_rank coverage ⟨child,coverage.closed focus.val focus.property child member⟩ focus member
        omega)
    refine ⟨.node node.key payloads,?_,node_tree node payloads trees⟩
    simp only [assemble]
    change (collect node.children _ >>= fun ps => pure ((.node node.key ps) : Payload)) = _
    rw [computed]
    rfl

private theorem collect_sound (sites : List (Occurrence roles))
    (run : ∀ child, child ∈ sites → Option Payload)
    (valid : ∀ child member payload, run child member = some payload → NamedTree registry state child payload)
    (computed : collect sites run = some payloads) :
    All₂ (NamedTree registry state) sites payloads := by
  induction sites generalizing payloads with
  | nil => simp only [collect,Option.some.injEq] at computed; subst payloads; exact .nil
  | cons child rest ih =>
    cases first : run child (by simp) with
    | none => simp [collect,first] at computed
    | some payload =>
      cases remaining : collect rest (fun next member => run next (by simp [member])) with
      | none => simp [collect,first,remaining] at computed
      | some tail =>
        simp only [collect,first,remaining] at computed
        change some (payload :: tail) = some payloads at computed
        have same := Option.some.inj computed
        clear computed
        subst payloads
        exact .cons (valid child (by simp) payload first)
          (ih _ (fun next member value eq => valid next (by simp [member]) value eq) remaining)

theorem successful_tree (coverage : Coverage registry state domain) (fuel : Nat)
    (focus : Subtype domain) (computed : assemble coverage fuel focus = some payload) :
    NamedTree registry state focus.val payload := by
  induction fuel generalizing focus payload with
  | zero => simp [assemble] at computed
  | succ fuel ih =>
    let node := coverage.node focus.val focus.property
    cases values : collect node.children (fun child member =>
      assemble coverage fuel ⟨child,coverage.closed focus.val focus.property child member⟩) with
    | none =>
      simp only [assemble] at computed
      change (collect node.children _ >>= fun ps => pure ((.node node.key ps) : Payload)) = _ at computed
      rw [values] at computed
      cases computed
    | some payloads =>
      have trees := collect_sound node.children _ (fun child member value eq => ih _ eq) values
      have exactResult : payload = .node node.key payloads := by
        simp only [assemble] at computed
        change (collect node.children _ >>= fun ps => pure ((.node node.key ps) : Payload)) = _ at computed
        rw [values] at computed
        exact (Option.some.inj computed).symm
      rw [exactResult]
      exact node_tree node payloads trees

def build (coverage : Coverage registry state domain) (focus : Subtype domain) : Option Payload :=
  assemble coverage (rank state focus.val + 1) focus

theorem build_succeeds (coverage : Coverage registry state domain) (focus : Subtype domain) :
    ∃ payload, build coverage focus = some payload ∧ NamedTree registry state focus.val payload :=
  enough_fuel coverage _ focus (Nat.lt_succ_self _)

theorem build_dictionary (coverage : Coverage registry state domain) (focus : Subtype domain)
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state) :
    ∃ payload, build coverage focus = some payload ∧ NamedTree registry state focus.val payload ∧
      ∀ model, Models state.current model →
        GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model focus.val payload := by
  obtain ⟨payload,computed,tree⟩ := build_succeeds coverage focus
  exact ⟨payload,computed,tree,fun model valid => GeneralDictionary169NamedTree.current_evidence formed tree model valid⟩

theorem zero_fuel (coverage : Coverage registry state domain) (focus : Subtype domain) :
    assemble coverage 0 focus = none := rfl

open GeneralDictionaryFiniteObservedExample

theorem actual_build : build actual_coverage ⟨root,rfl⟩ = some (.node declaration.id []) := by
  rfl

end Yulang.GeneralDictionary170BoundedAssembly
