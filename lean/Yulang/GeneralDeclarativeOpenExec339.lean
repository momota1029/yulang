import Yulang.GeneralDeclarativeOpenReceipt339

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpenExec339
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (InInterval)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeEntailment320 (model_append)
open GeneralDeclarativeEndpointNames336 (Triple)
open GeneralDeclarativeEndpointProgram336 (Projection Jobs)
open GeneralDeclarativeEndpointOverlay336 (Entry Agreement inputs receipts footprintKeep same)
open GeneralDeclarativeEndpointBatch336 (patch patch_values prepare atSlots preserves)
open GeneralDeclarativeCompoundOpenPrefix338 (residuals)
open GeneralDeclarativeCompoundBatch338 (Ticket minted protectedNames after)
open GeneralDeclarativeCompoundRoutes338 (key)
open GeneralDeclarativeExactOverlay337 (eval eval_eq list_sound ModelsExact Holds)
open GeneralDeclarativeExactSupport337 (endpoints_sound receipts_same)
open GeneralDeclarativeEndpointConserve336 (names)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (subtype_trans)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm)

def runOne (j : Projection) (m : Assignment) : Option Triple :=
  match j with
  | .field .. => eval j m
  | .rest a keys _ _ => some (residuals keys m a)

def values (m : Assignment) (jobs : Jobs) : List Triple :=
  jobs.map fun j => (runOne j.2 m).getD (.bottom,.bottom,.bottom)

theorem joined {s : State} {p : Supported s done} (t : Ticket p a fs) (m : Assignment)
    (fit : Models s m) (j) (picked : j ∈ t.jobs) :
    ∃ old actual, eval j.2 m = some old ∧ runOne j.2 m = some actual ∧
      Agreement actual old ∧ InInterval actual.1 actual.2.2 actual.2.1 := by
  obtain ⟨old,yes,bounds⟩ := list_sound t.read t.calculated m fit j picked
  cases view : j.2 with
  | field a label lo hi =>
    rw [view] at yes
    exact ⟨old,old,yes,yes,same old,bounds⟩
  | rest arg keys lo hi =>
    have chosen : ∃ n, (j,n) ∈ t.jobs.zipIdx := by
      have original : j ∈ (t.jobs.zipIdx).map Prod.fst := by simpa using picked
      obtain ⟨⟨i,n⟩,h,equal⟩ := List.mem_map.mp original
      cases equal
      exact ⟨n,h⟩
    obtain ⟨n,jidx⟩ := chosen
    let atJob := GeneralDeclarativeEndpointBatch336.slots s (protectedNames [] [] t.jobs) n
    let actual : Entry := ⟨j.2,atJob⟩
    have there : actual ∈ minted s [] [] t.jobs := List.mem_map.mpr ⟨(j,n),jidx,rfl⟩
    rcases GeneralDeclarativeCompoundReadback338.actual_recipe t there with ⟨tag,l,h,field,_,_⟩|rest
    · rw [show actual.1 = j.2 from rfl,view] at field
      cases field
    · rw [show actual.1 = j.2 from rfl,view] at rest
      cases rest
      have exacts := GeneralDeclarativeOpenReceipt339.endpoints t.read m fit
      have real := GeneralDeclarativeDemand320.bounds_sound t.read.valid m fit
      have lower := GeneralDeclarativeExactDelete337.monotone ((GeneralDeclarativeCompoundPattern338.layout fs).map Prod.fst) real.1
      have upper := GeneralDeclarativeExactDelete337.monotone ((GeneralDeclarativeCompoundPattern338.layout fs).map Prod.fst) real.2
      have eq : _ = old := Option.some.inj (view ▸ yes)
      subst old
      exact ⟨_,residuals ((GeneralDeclarativeCompoundPattern338.layout fs).map Prod.fst) m a,rfl,rfl,⟨exacts.1,eqv_refl _,exacts.2⟩,⟨lower,upper⟩⟩

/-- Allocate the old compiler's exact same state and names, but
evaluate the residual using actual lower, center, and upper values.
Ordinary endpoint rows remain only the independently justified older
form; no syntax is inferred from the new assignment. -/
theorem execute {s : State} {p : Supported s done} (t : Ticket p a fs) (m : Assignment)
    (fit : ModelsExact s old m) (keep : List Nat) :
    let n := patch s (protectedNames old keep t.jobs) (values m t.jobs) m
    ModelsExact (after s old keep t.jobs) (old ++ minted s old keep t.jobs) n ∧
      ∀ x ∈ stateNames s ++ (names old ++ keep), n x = m x := by
  let keepAll := protectedNames old keep t.jobs
  let vs := values m t.jobs
  let n := patch s keepAll vs m
  have unchanged := preserves (s := s) (protect := keepAll) vs m
  have count : vs.length = t.jobs.length := List.length_map _
  have ranges : ∀ triple ∈ vs, InInterval triple.1 triple.2.2 triple.2.1 := by
    intro triple included
    obtain ⟨j,used,rfl⟩ := List.mem_map.mp included
    obtain ⟨_,v,_,h,_,range⟩ := joined t m fit.1 j used
    simpa only [h,Option.getD] using range
  have valid := GeneralDeclarativeEndpointBatch336.fit fit.1 keepAll vs ranges
  rw [count] at valid
  have newReceipts : ∀ e ∈ minted s old keep t.jobs, Holds n e := by
    intro entry listed
    obtain ⟨⟨j,idx⟩,inJobs,rfl⟩ := List.mem_map.mp listed
    have atJob := List.mk_mem_zipIdx_iff_getElem?.mp inJobs
    obtain ⟨previous,v,printed,ran,agrees,_⟩ :=
      joined t m fit.1 j (List.fst_mem_of_mem_zipIdx inJobs)
    have selected : vs[idx]? = some v := by simp [vs,values,List.getElem?_map,atJob,ran]
    have sources : ∀ z ∈ inputs j.2, n z = m z := by
      intro z relevant
      exact unchanged z (List.mem_append_right _ (List.mem_append_left _ (List.mem_flatMap.mpr
        ⟨j,List.fst_mem_of_mem_zipIdx inJobs,relevant⟩)))
    refine ⟨previous,(eval_eq sources).trans printed,?_⟩
    change Agreement (atSlots (patch s keepAll vs m) (GeneralDeclarativeEndpointBatch336.slots s keepAll idx)) previous
    rw [patch_values selected]
    exact agrees
  have protect (x) (h : x ∈ stateNames s ++ (names old ++ keep)) : n x = m x :=
    (List.mem_append.mp h).elim
      (fun first => unchanged x (List.mem_append_left _ first))
      (fun later => unchanged x (List.mem_append_right _ (List.mem_append_right _ later)))
  have oldReceipts := (receipts_same (m := m) (n := n)
    (fun x h => protect x (List.mem_append_right _ (List.mem_append_left _ h)))).mpr fit.2
  refine ⟨⟨(model_append n).mpr ⟨valid,?_⟩,?_⟩,protect⟩
  · intro row appended
    obtain ⟨e,present,source⟩ := List.mem_flatMap.mp appended
    exact endpoints_sound (newReceipts e present) row source
  · intro e present
    exact (List.mem_append.mp present).elim (oldReceipts e) (newReceipts e)

end Yulang.GeneralDeclarativeOpenExec339
