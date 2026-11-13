import Yulang.GeneralDictionary170BoundedAssembly
import Yulang.GeneralDictionary170NamedCoveragePersistence

/-! Exact equality of fuel-bounded assembly under preservation of the chosen
ordered children and declaration keys. No semantic or language selection rule
is added; insufficient fuel returns the same failure on both sides. -/
namespace Yulang.GeneralDictionary170AssemblyPersistence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionaryReadback GeneralDictionary170NamedCoverage
open GeneralDictionary170BoundedAssembly
variable {roles : Roles.RoleDecls}

theorem collect_congr (left right : List (Occurrence roles)) (same : left = right)
    (first : ∀ child, child ∈ left → Option Payload)
    (second : ∀ child, child ∈ right → Option Payload)
    (equal : ∀ child memberLeft memberRight, first child memberLeft = second child memberRight) :
    collect left first = collect right second := by
  subst right
  have functions : first = second := by
    funext child member
    exact equal child member member
  rw [functions]

theorem assemble_congr {registry : Registry} {before after : Tracked roles}
    (first : Coverage registry before domain) (second : Coverage registry after domain)
    (children : ∀ occurrence present, (first.node occurrence present).children = (second.node occurrence present).children)
    (keys : ∀ occurrence present, (first.node occurrence present).key = (second.node occurrence present).key)
    (fuel : Nat) (focus : Subtype domain) :
    assemble first fuel focus = assemble second fuel focus := by
  induction fuel generalizing focus with
  | zero => rfl
  | succ fuel ih =>
    have collected := collect_congr
      (first.node focus.val focus.property).children (second.node focus.val focus.property).children
      (children focus.val focus.property)
      (fun child member => assemble first fuel ⟨child,first.closed focus.val focus.property child member⟩)
      (fun child member => assemble second fuel ⟨child,second.closed focus.val focus.property child member⟩)
      (fun child _ _ => ih ⟨child,_⟩)
    simp only [assemble]
    rw [collected,keys]

theorem extension_assemble {registry : Registry} {before after : Tracked roles}
    (members : ∀ packet ∈ before.current.packets, packet ∈ after.current.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension before.current.context after.current.context)
    (coverage : Coverage registry before domain) (fuel : Nat) (focus : Subtype domain) :
    assemble (GeneralDictionary170NamedCoveragePersistence.extension members growth coverage) fuel focus =
      assemble coverage fuel focus := by
  apply assemble_congr
  · intro occurrence present
    exact GeneralDictionary170NamedCoveragePersistence.node_children members growth _
  · intro occurrence present
    exact GeneralDictionary170NamedCoveragePersistence.node_key members growth _

theorem ordinary_assemble {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (path : B4Target.Steps (GeneralDictionarySharedEvidenceTrace.OrdinaryStep registry root) before after)
    (coverage : Coverage registry before domain) (fuel : Nat) (focus : Subtype domain) :
    assemble (GeneralDictionary170NamedCoveragePersistence.ordinarySteps path coverage) fuel focus =
      assemble coverage fuel focus :=
  extension_assemble _ _ _ _ _

theorem collect_unique (sites : List (Occurrence roles))
    (first second : ∀ child, child ∈ sites → Option Payload)
    (unique : ∀ child member value other, first child member = some value →
      second child member = some other → value = other)
    (left : collect sites first = some values) (right : collect sites second = some others) :
    values = others := by
  induction sites generalizing values others with
  | nil => simpa [collect] using left.symm.trans right
  | cons child rest ih =>
    cases a : first child (by simp) with
    | none => simp [collect,a] at left
    | some value =>
      cases b : second child (by simp) with
      | none => simp [collect,b] at right
      | some other =>
        cases c : collect rest (fun next member => first next (by simp [member])) with
        | none => simp [collect,a,c] at left
        | some tail =>
          cases d : collect rest (fun next member => second next (by simp [member])) with
          | none => simp [collect,b,d] at right
          | some tail' =>
            have head := unique child (by simp) value other a b
            have tails := ih _ _ (fun next member => unique next (by simp [member])) c d
            simp [collect,a,c] at left
            simp [collect,b,d] at right
            rw [← left,← right,head,tails]

theorem successful_fuel_unique (coverage : Coverage registry state domain)
    (first second : Nat) (focus : Subtype domain)
    (left : assemble coverage first focus = some value)
    (right : assemble coverage second focus = some other) : value = other := by
  induction first generalizing second focus value other with
  | zero => simp [assemble] at left
  | succ fuel ih =>
    cases second with
    | zero => simp [assemble] at right
    | succ remaining =>
      let node := coverage.node focus.val focus.property
      cases a : collect node.children (fun child member =>
        assemble coverage fuel ⟨child,coverage.closed focus.val focus.property child member⟩) with
      | none => simp [assemble,node,a] at left
      | some values =>
        cases b : collect node.children (fun child member =>
          assemble coverage remaining ⟨child,coverage.closed focus.val focus.property child member⟩) with
        | none => simp [assemble,node,b] at right
        | some others =>
          have equal := collect_unique node.children _ _
            (fun child member value other one two => ih remaining ⟨child,_⟩ one two) a b
          simp only [assemble] at left right
          change (collect node.children _ >>= fun ps => pure ((.node node.key ps) : Payload)) = _ at left right
          rw [a] at left
          rw [b] at right
          change some (.node node.key values) = some value at left
          change some (.node node.key others) = some other at right
          rw [← Option.some.inj left,← Option.some.inj right,equal]

theorem extension_build {registry : Registry} {before after : Tracked roles}
    (members : ∀ packet ∈ before.current.packets, packet ∈ after.current.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension before.current.context after.current.context)
    (coverage : Coverage registry before domain) (focus : Subtype domain) :
    build (GeneralDictionary170NamedCoveragePersistence.extension members growth coverage) focus =
      build coverage focus := by
  let next := GeneralDictionary170NamedCoveragePersistence.extension members growth coverage
  obtain ⟨value,first,_⟩ := build_succeeds coverage focus
  obtain ⟨other,second,_⟩ := build_succeeds next focus
  have first' : assemble next (GeneralDictionary170NamedAccessible.rank before focus.val + 1) focus = some value := by
    rw [extension_assemble]
    exact first
  have equal := successful_fuel_unique next _ _ focus first' second
  rw [first,second,equal]

theorem ordinary_build {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (path : B4Target.Steps (GeneralDictionarySharedEvidenceTrace.OrdinaryStep registry root) before after)
    (coverage : Coverage registry before domain) (focus : Subtype domain) :
    build (GeneralDictionary170NamedCoveragePersistence.ordinarySteps path coverage) focus =
      build coverage focus :=
  extension_build _ _ _ _
end Yulang.GeneralDictionary170AssemblyPersistence
