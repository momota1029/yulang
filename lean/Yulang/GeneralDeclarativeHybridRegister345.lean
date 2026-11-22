import Yulang.GeneralDeclarativeCurrentSeed345

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeHybridRegister345
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Site)
open GeneralWhereVersionInstall317 (Journal InstallStep installCore ordered emitted)
open GeneralWhereVersionCompiler317 (children)
open GeneralNominalVersionedMixedTrace235 (Registered Centered Covered Invariant)

theorem registered {before after : Journal rs} {root : Occurrence rs}
    (old : Registered before.mixed root) (step : InstallStep r before after) :
    Registered after.mixed root := by
  cases step with
  | whereRow ctx p _ _ _ _ _ _ _ =>
    constructor
    · obtain ⟨site,member,same⟩ := old.1
      exact ⟨site,List.mem_append_left _ member,same⟩
    · intro edge member
      rcases List.mem_append.mp member with prior|recent
      · obtain ⟨site,present,same⟩ := old.2 edge prior
        exact ⟨site,List.mem_append_left _ present,same⟩
      · obtain ⟨child,fromPlan,rfl⟩ := List.mem_map.mp recent
        rw [← ordered] at fromPlan
        obtain ⟨site,present,rfl⟩ := List.mem_map.mp fromPlan
        exact ⟨site.observed,List.mem_append_right _ (List.mem_map.mpr ⟨site,present,rfl⟩),rfl⟩

theorem centered {before after : Journal rs} (old : Centered before.mixed) (step : InstallStep r before after) :
    Centered after.mixed := by
  cases step with
  | whereRow ctx p _ _ _ _ _ _ _ =>
    intro center member
    rcases List.mem_append.mp member with prior|recent
    · obtain ⟨site,present,same⟩ := old center prior
      exact ⟨site,List.mem_append_left _ present,same⟩
    · exact ⟨center.observed,List.mem_append_right _ (List.mem_map.mpr ⟨center,recent,rfl⟩),rfl⟩

theorem covered {before after : Journal rs} (old : Covered before.mixed) (step : InstallStep r before after) :
    Covered after.mixed := by
  cases step with
  | whereRow ctx p _ _ _ _ _ _ _ =>
    intro site member
    rcases List.mem_append.mp member with prior|recent
    · obtain ⟨center,present,same⟩ := old site prior
      exact ⟨center,List.mem_append_left _ present,same⟩
    · obtain ⟨center,present,rfl⟩ := List.mem_map.mp recent
      exact ⟨center,List.mem_append_right _ present,rfl⟩

theorem install {before after : Journal rs} {root : Occurrence rs}
    (old : Invariant before.mixed root) (step : InstallStep r before after) : Invariant after.mixed root :=
  ⟨registered old.1 step,centered old.2.1 step,covered old.2.2 step⟩

end Yulang.GeneralDeclarativeHybridRegister345
