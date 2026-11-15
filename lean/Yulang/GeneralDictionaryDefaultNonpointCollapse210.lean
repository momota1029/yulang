import Yulang.GeneralDictionaryDefaultBinderShape210

/-! A two-to-one capture collapse with a nonpoint retained interval preserves
all actual binder names, hence all total output bodies at the retained center.
This is strictly a body result: changed endpoint equations may still prevent
new packet Holds, and no global completion theorem is inferred. -/
namespace Yulang.GeneralDictionaryDefaultNonpointCollapse210
open GeneralDeclarations GeneralNominalAllocation GeneralNominalCenters
open GeneralNominalCenteredHeadMatEffects
variable {roles : Roles.RoleDecls} {first last : Plan roles}
variable {model : GeneralNominalCommonBridge.Assignment}

 theorem aggregate_nonpoint (state : GeneralNominalState.State) (registry : Registry)
    (root key name : Nat) :
    source state registry root (origin root key 0 name 0) ≠
      source state registry root (origin root key 1 name 0) := by
  intro same
  have equal := (source_identity state registry root _ _).mp same
  have purpose := congrArg (fun p : GeneralNominalIdentities.Origin => p.2.2.1) equal
  cases purpose

 theorem repeated_nonpoint (state : GeneralNominalState.State) (registry : Registry)
    (root key binder name : Nat) (a b : GeneralSourceState.Interval) :
    ((capture state registry root key [(binder,a),(binder,b)]).inputs name).1 ≠
      ((capture state registry root key [(binder,a),(binder,b)]).inputs name).2 := by
  by_cases same : binder = name
  · subst binder
    simpa [capture,occurrences] using aggregate_nonpoint state registry root key name
  · simpa [capture,occurrences,same] using aggregate_nonpoint state registry root key name

 theorem retained_nonpoint (state : GeneralNominalState.State) (registry : Registry)
    (root key binder name : Nat) (a : GeneralSourceState.Interval) (nonpoint : a.1 ≠ a.2) :
    ((capture state registry root key [(binder,a)]).inputs name).1 ≠
      ((capture state registry root key [(binder,a)]).inputs name).2 := by
  by_cases same : binder = name
  · subst binder
    simpa [capture,occurrences] using nonpoint
  · simpa [capture,occurrences,same] using aggregate_nonpoint state registry root key name

 theorem shape
    (before : first.packet.bindings = [(binder,a),(binder,b)])
    (after : last.packet.bindings = [(binder,a)]) (nonpoint : a.1 ≠ a.2) (name : Nat) :
    GeneralDictionaryDefaultBinderShape210.InputShape first last name := by
  right
  constructor
  · unfold GeneralNominalPacketSupport.capture
    rw [before]
    exact repeated_nonpoint _ _ _ _ _ _ _ _
  · unfold GeneralNominalPacketSupport.capture
    rw [after]
    exact retained_nonpoint _ _ _ _ _ _ _ nonpoint

 theorem body_iff
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration)
    (constructors : first.packet.registry.constructors = last.packet.registry.constructors)
    (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
    (input : first.input = last.input)
    (before : first.packet.bindings = [(binder,a),(binder,b)])
    (after : last.packet.bindings = [(binder,a)]) (nonpoint : a.1 ≠ a.2) :
    BodyHolds first target model body ↔ BodyHolds last target model body :=
  GeneralDictionaryDefaultBinderShape210.body_iff seed identity declaration constructors interpretation input
    (fun name _ => shape before after nonpoint name)
end Yulang.GeneralDictionaryDefaultNonpointCollapse210
