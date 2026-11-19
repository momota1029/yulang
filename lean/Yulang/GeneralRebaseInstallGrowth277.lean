import Yulang.GeneralRebaseQuietBound277

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseInstallGrowth277
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedAllocation231 (keys declarationKeys)
open GeneralNominalVersionedInstallation231 (reserved)
open GeneralNominalVersionedMixedKernel234 (Installable)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable reachable_step split)
open GeneralNominalAllocation (Bindings)
open GeneralNominalState (sources)
open GeneralRebaseMixedOwnedTrace277 (raw)
open GeneralRebaseQuietBasis277 (sourceNames centerNames budget)
variable {roles : Roles.RoleDecls}

theorem nodup_names (xs : List Nat) : xs.eraseDups.Nodup := by
  cases xs with
  | nil => exact List.nodup_nil
  | cons first rest =>
    rw [List.eraseDups_cons]
    exact List.nodup_cons.mpr ⟨by simp,nodup_names (rest.filter fun x => !x == first)⟩
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le ..)

def reserveBudget (r : Registry) : Nat := (keys r 0 []).length

def centerBudget (r : Registry) : Nat :=
  (r.declarations.map fun d => d.requirements.length).foldr max 0

theorem declaration_key_count (root : Nat) (d : Declaration) (bs : Bindings) :
    (declarationKeys root d bs).length = (declarationKeys 0 d []).length := by
  simp [declarationKeys,List.length_flatMap]

theorem key_count (r : Registry) (root : Nat) (bs : Bindings) :
    (keys r root bs).length = reserveBudget r := by
  simp only [keys,reserveBudget,List.length_flatMap]
  congr 1
  exact List.map_congr_left fun d _ => declaration_key_count root d bs

theorem reserve_length (p : GeneralNominalSaturationState.Packet roles) :
    (reserved p).length = reserveBudget p.registry := by
  simp only [reserved,GeneralNominalVersionedAllocation231.reserved,List.length_map,key_count]

theorem emitted_bound (e : Effect roles) (enabled : Installable r s e) :
    (GeneralNominalVersionedChildren232.emitted e.plan).length ≤ centerBudget r := by
  rw [GeneralNominalVersionedChildren232.emitted_length]
  apply GeneralNominalAllocation.member_le_max
  exact List.mem_map.mpr ⟨e.plan.packet.declaration,enabled.registry_eq ▸ e.frame.visible,rfl⟩

theorem install_sources (e : Effect roles) (enabled : Installable r s e) :
    (sourceNames (install s e)).length ≤ (sourceNames s).length + reserveBudget r := by
  have ctx : e.plan.packet.context = s.core.erased.current.context :=
    e.frame.context_eq.trans (congrArg (fun core => core.erased.current.context) enabled.snapshot_eq)
  have rawEq : e.plan.packet.context.state = raw s := congrArg GeneralNominalCandidates.Context.state ctx
  have seen : e.plan.packet.declaration ∈ e.plan.packet.registry.declarations :=
    e.frame.registry_eq.symm ▸ e.frame.visible
  have subset : sourceNames (install s e) ⊆ sourceNames s ++ reserved e.plan.packet := by
    intro name member
    unfold sourceNames at member
    have used := List.mem_eraseDups.mp member
    change name ∈ sources (GeneralNominalVersionedInstallation231.replayPlan e.plan).packet.context.state at used
    rcases List.mem_append.mp (GeneralRebaseOwnedSupport277.replay_support e.plan seen used) with old | new
    · exact List.mem_append_left _ (List.mem_eraseDups.mpr (rawEq ▸ old))
    · exact List.mem_append_right _ new
  have bound := (nodup_names (sources (raw (install s e)))).length_le_of_subset subset
  rw [List.length_append,reserve_length,e.frame.registry_eq,enabled.registry_eq] at bound
  exact bound

theorem install_centers (e : Effect roles) (enabled : Installable r s e) :
    (centerNames (install s e)).length ≤ (centerNames s).length + centerBudget r := by
  let added := (GeneralNominalVersionedChildren232.emitted e.plan).map
    (fun site => site.occurrence.identity)
  have subset : centerNames (install s e) ⊆ centerNames s ++ added := by
    intro id present
    unfold centerNames at present
    have one := List.mem_eraseDups.mp present
    change id ∈ (s.core.sites ++ GeneralNominalVersionedChildren232.emitted e.plan).map _ at one
    rw [List.map_append] at one
    rcases List.mem_append.mp one with old|new
    · exact List.mem_append_left _ (List.mem_eraseDups.mpr old)
    · exact List.mem_append_right _ new
  have bound := (nodup_names ((install s e).core.sites.map fun site => site.occurrence.identity)).length_le_of_subset subset
  rw [List.length_append] at bound
  simp only [added,List.length_map] at bound
  exact Nat.le_trans bound (Nat.add_le_add_left (emitted_bound e enabled) _)

theorem source_le_of_subset {s t : State roles} (subset : sources (raw t) ⊆ sources (raw s)) :
    (sourceNames t).length ≤ (sourceNames s).length := by
  apply (nodup_names (sources (raw t))).length_le_of_subset
  intro id possible
  exact List.mem_eraseDups.mpr (subset (List.mem_eraseDups.mp possible))

end Yulang.GeneralRebaseInstallGrowth277
