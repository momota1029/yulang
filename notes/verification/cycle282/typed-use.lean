import Yulang.GeneralRebaseCompiledFixtures282

open Yulang
open GeneralDeclarations GeneralSourceDictionaries
open GeneralRebaseWholeRow282 (Projection initialNames)
open GeneralRebasePrivateStore282 (Joint)
open GeneralRebaseWholeJournal282 (View)
open GeneralRebaseTermCopy281 (Respects)
open GeneralRebaseLiveStore282 (live)
open GeneralRebaseMixedOwnedTrace277 (raw)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralRebaseProspective282 (Compiled)
open GeneralNominalVersionedInstall232 (install InstallationModels)
open GeneralRebaseCompiledStep282 (Driver)
open GeneralRebaseMixedCounts277 (Actual)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)

example {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles} {s : State roles}
    (path : Reachable r root s) (r' : Registry) (focus : Occurrence roles) (data : Payload)
    (outside : Assignment) :
    Projection (initialNames (raw s).seed) (fun m => View s r' focus data m ∧ Respects (live s) m) outside ↔
      Projection (initialNames (raw s).seed) (Joint s r' focus data) outside :=
  GeneralRebaseWholeRow282.initial_projection path r' focus data outside

example {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles}
    {s : State roles} {e : Effect roles} (path : Reachable r root s) (snapshot : e.snapshot = s.core) :
    (∃ m, Compiled (install s e) m) ↔ (∃ m, InstallationModels s e m) :=
  GeneralRebaseProspective282.acceptance_before path snapshot

example {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles}
    {s t : State roles} (path : Reachable r root s) :
    B4Target.Steps (Driver r root) s t ↔ B4Target.Steps (Actual r root) s t :=
  GeneralRebaseCompiledStep282.driver_path path

example (outer : Assignment) (m : GeneralNominalVersionedJournal232.Models GeneralRebaseCompiledDisplay277.after outer) :
    Projection (initialNames (raw GeneralRebaseCompiledDisplay277.after).seed)
      (fun a => View GeneralRebaseCompiledDisplay277.after GeneralRebaseCompiledDisplay277.compiled
        GeneralNominalExamples.displayRoot (.node 1 [.node 3 []]) a ∧ Respects (live GeneralRebaseCompiledDisplay277.after) a) outer :=
  GeneralRebaseCompiledFixtures282.Display.compiled_nonleaf outer m

example :
    GeneralRebaseCompiledEvidenceAt282.EvidenceAt GeneralDictionaryDefaultGap206Source.registry
      GeneralDictionaryMixedGap206Refresh234.refreshed GeneralDictionaryDefaultGap206Source.root :=
  GeneralRebaseCompiledFixtures282.Default.selected_preserved

example :
    GeneralRebaseCompiledEvidenceAt282.EvidenceAt GeneralDictionaryGroundCopy218Source.sourceRegistry
      GeneralDictionaryMixedGround218FinalState235.finalState GeneralDictionaryGroundCopy218Source.root :=
  GeneralRebaseCompiledFixtures282.Ground.selected_preserved

example (n : Nat) (d : Payload) (outer : Assignment) :
    Projection (initialNames 4) (fun m =>
      View (GeneralDictionaryLooseIterationIteration240.state (n+1))
        GeneralDictionaryLooseLoopSource240.registry GeneralDictionaryLooseLoopSource240.root d m ∧
        Respects GeneralRebaseLoopConstant282.Loose.simple m) outer ↔
      GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot outer ∧ d = .node 0 [] :=
  GeneralRebaseLoopView282.Loose.projected_constant n d outer
