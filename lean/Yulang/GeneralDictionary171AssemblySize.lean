import Yulang.GeneralDictionary171BoundedAssembly

/-! Total output-tree node count for successful bounded assembly. This counts
expanded dictionary nodes, including repeated children, not shared graph nodes,
bytes, Lean resources, or saturation execution steps. -/
namespace Yulang.GeneralDictionary171AssemblySize
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionaryReadback GeneralDictionary171SpineCoverage
open GeneralDictionary171BoundedAssembly
variable {roles : Roles.RoleDecls}

mutual
  def nodes : Payload → Nat
    | .node _ children => 1 + nodesList children
  def nodesList : List Payload → Nat
    | [] => 0
    | child :: rest => nodes child + nodesList rest
end

def branching (state : Tracked roles) : Nat :=
  (state.current.packets.map fun packet => packet.children.length).foldr max 0

private theorem member_max (values : List Nat) (value : Nat) (member : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => cases member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

theorem node_degree {registry : Registry} {state : Tracked roles} {occurrence : Occurrence roles}
    (node : Node registry state occurrence) : node.children.length ≤ branching state := by
  cases node with
  | old previous =>
    cases previous with
    | recorded packet member relocation =>
      exact member_max _ _ (List.mem_map.mpr ⟨packet,member,rfl⟩)
    | scalar => exact Nat.zero_le _
    | spine => exact Nat.zero_le _
    | named => exact Nat.zero_le _
  | namedSpine => exact Nat.zero_le _

def cap (branch : Nat) : Nat → Nat
  | 0 => 0
  | fuel + 1 => 1 + branch * cap branch fuel

theorem collect_bound (sites : List (Occurrence roles))
    (run : ∀ child, child ∈ sites → Option Payload) (bound : Nat)
    (valid : ∀ child member payload, run child member = some payload → nodes payload ≤ bound)
    (computed : collect sites run = some payloads) :
    nodesList payloads ≤ sites.length * bound := by
  induction sites generalizing payloads with
  | nil =>
    simp only [collect,Option.some.injEq] at computed
    subst payloads
    simp [nodesList]
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
        subst payloads
        have headBound := valid child (by simp) payload first
        have tailBound := ih _ (fun next member value eq => valid next (by simp [member]) value eq) remaining
        simp only [nodesList,List.length_cons,Nat.add_mul,Nat.one_mul]
        omega

theorem successful_bound (coverage : Coverage registry state domain) (fuel : Nat)
    (focus : Subtype domain) (computed : assemble coverage fuel focus = some payload) :
    nodes payload ≤ cap (branching state) fuel := by
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
      have childBound := collect_bound node.children _ (cap (branching state) fuel)
        (fun child member value eq => ih ⟨child,_⟩ eq) values
      have degree := node_degree node
      have total := Nat.mul_le_mul_right (cap (branching state) fuel) degree
      have exactResult : payload = .node node.key payloads := by
        simp only [assemble] at computed
        change (collect node.children _ >>= fun ps => pure ((.node node.key ps) : Payload)) = _ at computed
        rw [values] at computed
        exact (Option.some.inj computed).symm
      rw [exactResult]
      simp only [nodes,cap]
      omega

theorem build_bound (coverage : Coverage registry state domain) (focus : Subtype domain) :
    ∃ payload, build coverage focus = some payload ∧
      nodes payload ≤ cap (branching state) (GeneralDictionary171SpineAccessible.rank state focus.val + 1) := by
  obtain ⟨payload,computed,_⟩ := build_succeeds coverage focus
  exact ⟨payload,computed,successful_bound coverage _ focus computed⟩

end Yulang.GeneralDictionary171AssemblySize
