import Yulang.GeneralDeclarativeRootReplay344

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCommitPackage344
open GeneralNominalCenters (Plan Site)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Registry)
open GeneralWhereVersionInstall317 (Journal InstallStep Models install emitted)
open GeneralWhereOriginSupport318 (journalSources)
open GeneralWhereVersionCompiler317 (allocation)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeClauseBatch327 (Port prepare)
open GeneralDeclarativeRawCapture344 (rawCap keep base)
open GeneralDeclarativeRawReplayArgs344 (names)
open GeneralDeclarativeReplayOrder344 (SameBirth logicalChildren committed_order)
open GeneralDeclarativeEffectiveReplay344 (appendModes appendEffective all_effective)
open GeneralDeclarativeAssociatedReplay344 (output_batch)
open GeneralDeclarativeRootReplay344 (actualDemand batch)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativeCommitPosition344 (current_stamp)
open GeneralDeclarativeEntailment320 (appendFacts model_append)
open GeneralDeclarativeStoppedPaired341 (Placement)
open GeneralNominalCenteredHeadMatEffects (Ready)
open CommonRoleOutermostResolver (All₂)

structure Witness {rs : Roles.RoleDecls} (after : Journal rs) (p : Plan rs)
    (m n : Assignment) (protectedNames : List Nat)
    (prepared s : State) (ports : List Port) (whereRows rootRows : List Equation) : Prop where
  raw : Models after n
  preserved : ∀ k ∈ journalSources after, n k = m k
  kept : ∀ k ∈ protectedNames, n k = m k
  inputBatch : prepare p.packet.registry.constructors p.packet.context.interpretation
    (keep p after protectedNames) (rawCap p) (base p) p.packet.declaration.requirements = some (prepared,ports)
  whereBatch : GeneralDeclarativeWhereOutputBatch327.whole p.packet.registry p.packet.context.interpretation
    p.packet.declaration (names p) (fun cl => (allocation p cl).outputs) = some whereRows
  rootBatch : GeneralDeclarativeBatch320.collect
    (one p.packet.registry p.packet.context.interpretation p.packet.declaration
      (actualDemand p after) (rawCap p)) (actualDemand p after).outputs = some rootRows
  literalRootTargets : rootRows.map Equation.left = (actualDemand p after).outputs.map GeneralSourceState.Output.target
  ordinary : GeneralDeclarativeHead320.Models s n
  shape : s = appendFacts (appendFacts (appendFacts prepared whereRows) rootRows)
    (appendModes (emitted p) (logicalChildren p ports))
  birth : All₂ (SameBirth n) (emitted p) (logicalChildren p ports)
  effective : All₂ (fun (site : Site rs) logical => Placement after.mixed s site.occurrence logical)
    (emitted p) (appendEffective after.mixed (emitted p) (logicalChildren p ports))

/-- Genuine install, complete raw where inputs, class-output readiness
and an actual post-model produce the normalized input and associated
compiler batches, rooted literal output list and exact placements in
one journal-preserving ordinary view. This constructs the producer
for a versioned commit, not a source classifier or a stopped-run proof. -/
theorem from_install (r : Registry) (before : Journal rs) (ctx : GeneralNominalCandidates.Context)
    (p : Plan rs) (step : InstallStep r before (install before ctx p))
    (m : Assignment) (fit : Models (install before ctx p) m) (protectedNames : List Nat)
    (sameRoles : p.packet.registry.roles = rs)
    (ready : Ready (install before ctx p).mixed.core p.packet.site.occurrence p) :
    ∃ prepared s ports whereRows rootRows n,
      Witness (install before ctx p) p m n protectedNames prepared s ports whereRows rootRows := by
  let after := install before ctx p
  obtain ⟨prepared,ports,n,ran,inputs,raw,rawFoot,outNames,birth⟩ := committed_order r before ctx p step m fit protectedNames
  have receipt := current_stamp r before ctx p step n raw
  obtain ⟨whereRows,whereCompiled,whereTrue⟩ := output_batch p n receipt.typed
  obtain ⟨rootRows,rootCompiled,targets,rootTrue⟩ := batch p after n sameRoles ready receipt.effects
  let w := appendFacts (appendFacts prepared whereRows) rootRows
  have ordinary : GeneralDeclarativeHead320.Models w n :=
    (model_append n).mpr ⟨(model_append n).mpr ⟨inputs,whereTrue⟩,rootTrue⟩
  have placed := all_effective (raw := after.mixed) birth
    (fun site h => by rw [receipt.sites]; exact List.mem_append_right _ h) ordinary
  exact ⟨prepared,_,ports,whereRows,rootRows,n,raw,rawFoot,outNames,ran,whereCompiled,
    rootCompiled,targets,placed.1,rfl,birth,placed.2⟩

end Yulang.GeneralDeclarativeCommitPackage344
