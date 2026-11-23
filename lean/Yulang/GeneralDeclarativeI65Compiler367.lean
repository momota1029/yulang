import Yulang.GeneralDeclarativeI65Heads367
import Yulang.GeneralDeclarativeStableAssemble329

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeOpaqueGroup328 (group group_exact)
open GeneralDeclarativeOpaqueCapture328 (choose)
open GeneralDeclarativeOpaqueShared328 (build)
open GeneralDeclarativeStableAssemble329 (merged tieState firsts)
open GeneralDeclarativeAggregate324 (span ready)
open GeneralDeclarativeWitnessCompiler350 (Context preparation portNames execute initial)
open GeneralDeclarativeWitnessDeclaredState357 (context)
open GeneralDeclarations (Declaration)

theorem find_first_group {key : Nat} {uses : List (Nat × Capture)} {cap : Capture}
    (hit : (uses.find? (fun item => item.1 == key)).map Prod.snd = some cap) :
    ∃ rest,group key uses = cap :: rest := by
  induction uses with
  | nil => simp at hit
  | cons head tail ih =>
    obtain ⟨n,x⟩ := head
    by_cases same : n = key
    · subst n
      have h : x = cap := by simpa using hit
      subst x
      exact ⟨group key tail, by simp [group]⟩
    · have h : (tail.find? (fun item => item.1 == key)).map Prod.snd = some cap := by
        simpa [same] using hit
      obtain ⟨rest,success⟩ := ih h
      exact ⟨rest,by simpa [group,same] using success⟩

theorem build_retains_first_center {s : GeneralDeclarativeHead320.State}
    {key : Nat} {keys : List Nat} {uses : List (Nat × Capture)}
    {seed : Capture} {more : List Capture}
    (keep : List Nat) (fallback : Nat → Capture)
    (present : key ∈ keys) (fromOwn : group key uses = seed :: more) :
    ((build keep uses fallback s keys).captures key).center = seed.center := by
  induction keys generalizing s with
  | nil => cases present
  | cons other rest ih =>
    by_cases eq : key = other
    · subst other
      simp [build,fromOwn,span]
    · have remains := (List.mem_cons.mp present).resolve_left eq
      cases read : group other uses with
      | nil => simpa [build,read] using (ih (s := s) remains)
      | cons first later => simpa [build,read,eq] using (ih (s := ready s keep first later) remains)

theorem actual_port_center {c : Context} {ports : List GeneralDeclarativeClauseBatch327.Port}
    {key : Nat} {cap : Capture}
    (head : (c.spans.find? (fun item => item.1 == key)).map Prod.snd = some cap)
    (ordinaryInput : key ∉ c.decl.outputNames) :
    ((portNames c ports).input key).center = cap.center := by
  obtain ⟨more,grouped⟩ := find_first_group head
  have inGroup : cap ∈ group key c.spans := by rw [grouped]; exact List.mem_cons_self
  have listed := (group_exact key c.spans).mp inGroup
  have keyWritten : key ∈ c.spans.map Prod.fst := List.mem_map.mpr ⟨(key,cap),listed,rfl⟩
  have stable := build_retains_first_center (s := tieState c.named c.spans c.fallback)
    c.keep c.fallback keyWritten grouped
  simpa only [portNames,GeneralDeclarativeFrameReadback325.sourceNames,
    GeneralDeclarativeProducedNames325.table,ordinaryInput,ite_false,initial,merged] using stable

end Yulang.GeneralDeclarativeI65
