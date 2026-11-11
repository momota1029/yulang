import Yulang.GeneralCanonicalChildOrder
import Yulang.GeneralDictionarySemanticUniqueness

/-!
# Deterministic dictionary child plans from actual checked declarations

A fixed resolved frame supplies per-key capture/allocation data. The actual
checked registry selects a unique full declaration by key, and canonicalEmit
supplies every child. A caller-provided source-ID map is retained explicitly;
no freshness, allocator, head matching or feasibility theorem is asserted.
Plan is NOT the missing general Survivor judgment.
-/
namespace Yulang.GeneralDictionaryEmissionPlans
open GeneralDeclarations GeneralDeclarationDemands GeneralCanonicalChildOrder
open GeneralRegistryReordering GeneralSourceDictionaries GeneralDictionaryReadback
open GeneralDictionarySemanticUniqueness

structure Frame (roles : Roles.RoleDecls) where
  capture : Nat → Capture
  allocation : Nat → (clause : Clause) → Allocation roles clause
  /-- Stable invocation/declaration/clause identities, not enumeration positions.
  Freshness and consistency with the actual source allocator remain unproved. -/
  identity : Nat → Nat → Nat → Nat

def occurrence (frame : Frame roles) (emission : Emission roles) : Occurrence roles :=
  ⟨frame.identity emission.invocation emission.declaration emission.clause, emission.demand⟩

def children (frame : Frame roles) (root : Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked constructors roles declaration) : List (Occurrence roles) :=
  (canonicalEmit root.identity declaration checked (frame.capture declaration.id)
    (frame.allocation declaration.id)).map (occurrence frame)

/-- A declaration emission plan does not establish that its head is applicable,
that its constraints are feasible, or that its output equations are recorded. -/
def Plan (registry : Registry) (checked : Checked registry) (frame : Frame registry.roles) :
    LocalInstance registry.roles :=
  fun root key demands => ∃ declaration, ∃ present : declaration ∈ registry.declarations,
    declaration.id = key ∧ declaration.role = root.demand.role ∧
      demands = children frame root declaration (checked.2 declaration present)

private theorem unique_key (key : α → Nat) (xs : List α)
    (unique : (xs.map key).Nodup) (a b : α) (left : a ∈ xs) (right : b ∈ xs)
    (same : key a = key b) : a = b := by
  induction xs with
  | nil => cases left
  | cons head rest ih =>
    have pair := List.nodup_cons.mp unique
    rcases List.mem_cons.mp left with equalA | tailA
    · subst a
      rcases List.mem_cons.mp right with equalB | tailB
      · subst b; rfl
      · exact False.elim (pair.1 (List.mem_map.mpr ⟨b, tailB, same.symm⟩))
    · rcases List.mem_cons.mp right with equalB | tailB
      · subst b
        exact False.elim (pair.1 (List.mem_map.mpr ⟨a, tailA, same⟩))
      · exact ih pair.2 tailA tailB

/-- Full declaration identity follows from the actual checked visible-ID list. -/
theorem declaration_key_unique (registry : Registry) (checked : Checked registry)
    (first last : Declaration) (one : first ∈ registry.declarations) (two : last ∈ registry.declarations)
    (same : first.id = last.id) : first = last :=
  unique_key Declaration.id registry.declarations checked.1 first last one two same

/-- This discharges the representation part of child coherence, given a fixed
resolved capture/allocation frame. Deriving that frame remains item3 work. -/
theorem plan_children_functional (registry : Registry) (checked : Checked registry)
    (frame : Frame registry.roles) : ChildrenFunctional (Plan registry checked frame) := by
  intro root key first last one two
  obtain ⟨declaration₁, present₁, key₁, _, children₁⟩ := one
  obtain ⟨declaration₂, present₂, key₂, _, children₂⟩ := two
  have same := declaration_key_unique registry checked declaration₁ declaration₂ present₁ present₂
    (key₁.trans key₂.symm)
  subst declaration₂
  exact children₁.trans children₂.symm

/-- Actual visible declarations supply their complete plans without a solver. -/
theorem visible_plan (registry : Registry) (checked : Checked registry) (frame : Frame registry.roles)
    (root : Occurrence registry.roles) (declaration : Declaration)
    (present : declaration ∈ registry.declarations) (role : declaration.role = root.demand.role) :
    Plan registry checked frame root declaration.id
      (children frame root declaration (checked.2 declaration present)) :=
  ⟨declaration, present, rfl, role, rfl⟩

/-- The supplied source map is unchanged while complete emission data canonicalize. -/
theorem children_reorders (frame : Frame roles) (root : Occurrence roles)
    (order : DeclarationReorders first last)
    (firstChecked : DeclarationChecked constructors roles first)
    (lastChecked : DeclarationChecked constructors roles last) :
    children frame root first firstChecked = children frame root last lastChecked := by
  unfold children
  have emitted := canonicalEmit_reorders root.identity order firstChecked lastChecked
    (frame.capture first.id) (frame.allocation first.id)
  rw [order.id] at emitted
  rw [order.id]
  exact congrArg (List.map (occurrence frame)) emitted

/-- Actual registry order transport, with identical constructor/role catalogues
and the same resolved frame. Final-state or candidate-inspection invariance is
not smuggled into this fixed-input theorem. -/
theorem plan_reorders_forward (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors, roles, first⟩) (two : Checked ⟨constructors, roles, last⟩)
    (order : Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (frame : Frame roles) (root : Occurrence roles) (key : Nat) (demands : List (Occurrence roles))
    (plan : Plan ⟨constructors, roles, first⟩ one frame root key demands) :
    Plan ⟨constructors, roles, last⟩ two frame root key demands := by
  obtain ⟨declaration, present, identity, role, generated⟩ := plan
  obtain ⟨other, member, reordered⟩ := reorders_visible order declaration present
  refine ⟨other, member, reordered.id.symm.trans identity, reordered.role.symm.trans role, ?_⟩
  exact generated.trans (children_reorders frame root reordered (one.2 declaration present) (two.2 other member))

theorem plan_reorders_iff (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors, roles, first⟩) (two : Checked ⟨constructors, roles, last⟩)
    (order : Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (frame : Frame roles) (root : Occurrence roles) (key : Nat) (demands : List (Occurrence roles)) :
    Plan ⟨constructors, roles, first⟩ one frame root key demands ↔
      Plan ⟨constructors, roles, last⟩ two frame root key demands :=
  ⟨plan_reorders_forward constructors roles first last one two order frame root key demands,
    plan_reorders_forward constructors roles last first two one
      (GeneralRegistryChildOrder.reorders_symm order) frame root key demands⟩

/-- Unique selected keys plus actual plan coherence give the exact local premise
for source dictionary uniqueness. The selected-key premise remains explicit. -/
theorem selected_plan_functional (registry : Registry) (checked : Checked registry)
    (frame : Frame registry.roles) (selected : Occurrence registry.roles → Nat → Prop)
    (unique : ∀ root first last, selected root first → selected root last → first = last) :
    NodeFunctional (fun root key children => selected root key ∧ Plan registry checked frame root key children) := by
  intro root key₁ key₂ first last one two
  have keys := unique root key₁ key₂ one.1 two.1
  subst key₂
  exact ⟨rfl, (plan_children_functional registry checked frame root key₁ first last one.2 two.2).symm ▸ List.Perm.refl first⟩

end Yulang.GeneralDictionaryEmissionPlans
