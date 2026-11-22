import Yulang.GeneralDeclarativeEndpointProgram336

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEndpointOverlay336
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWhere319 (Capture InInterval)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeEndpointRecord336 (Read)
open GeneralDeclarativeEndpointProgram336 (Projection Jobs ready list_sound)
open GeneralDeclarativeEndpointNames336 (Triple)
open GeneralDeclarativeEndpointBatch336 (slots atSlots prepare patch patch_values preserves bound)
open GeneralDeclarativeFootprint321 (stateNames value_same)
open GeneralDeclarativeTraceNames321 (names)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Equivalent)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)

abbrev Entry := Projection × Capture

def receipts (s : State) (protect : List Nat) (jobs : Jobs) : List Entry :=
  jobs.zipIdx.map (fun z => (z.1.2,slots s protect z.2))

def spans (s : State) (protect : List Nat) (jobs : Jobs) : List (Nat × Capture) :=
  jobs.zipIdx.map (fun z => (z.1.1,slots s protect z.2))

def Agreement (u v : Triple) : Prop :=
  Equivalent u.1 v.1 ∧ Equivalent u.2.1 v.2.1 ∧ Equivalent u.2.2 v.2.2

theorem same (v : Triple) : Agreement v v :=
  ⟨eqv_refl _,eqv_refl _,eqv_refl _⟩

def Holds (m : Assignment) (e : Entry) : Prop :=
  ∃ ideal, e.1.eval m = some ideal ∧ Agreement (atSlots m e.2) ideal

/-- A projection sidecar is interpreted together with the ordinary
constraint state. It is not a list of newly invented source RHS rows. -/
def ModelsWith (s : State) (reads : List Entry) (m : Assignment) : Prop :=
  Models s m ∧ ∀ x ∈ reads, Holds m x

def inputs : Projection → List Nat
  | .field a _ lo hi | .rest a _ lo hi => a.center :: (names lo ++ names hi)

def footprint (jobs : Jobs) : List Nat :=
  jobs.flatMap (fun j => inputs j.2)

def footprintKeep (protect : List Nat) (jobs : Jobs) : List Nat :=
  footprint jobs ++ protect

theorem program_eq {p : Projection} {m n : Assignment}
    (same : ∀ x ∈ inputs p, n x = m x) : p.eval n = p.eval m := by
  cases p with
  | field arg key lo hi =>
    have h0 := same _ List.mem_cons_self
    have hl := value_same n m .actual lo (fun y used => same _
      (List.mem_cons_of_mem _ (List.mem_append_left _ used)))
    have hh := value_same n m .actual hi (fun y used => same _
      (List.mem_cons_of_mem _ (List.mem_append_right _ used)))
    simp only [Projection.eval,h0,GeneralDeclarativeEndpointRecord336.interp,hl,hh]
  | rest arg keys lo hi =>
    have h0 := same _ List.mem_cons_self
    have hl := value_same n m .actual lo (fun y used => same _
      (List.mem_cons_of_mem _ (List.mem_append_left _ used)))
    have hh := value_same n m .actual hi (fun y used => same _
      (List.mem_cons_of_mem _ (List.mem_append_right _ used)))
    simp only [Projection.eval,h0,GeneralDeclarativeEndpointRecord336.interp,hl,hh]

theorem span_order (s : State) (protect : List Nat) (jobs : Jobs) :
    (spans s protect jobs).map Prod.fst = jobs.map Prod.fst := by
  simpa only [spans,List.map_map,Function.comp_def] using
    congrArg (List.map Prod.fst) (List.zipIdx_map_fst 0 jobs)

theorem spans_ready {s : State} {jobs : Jobs} {entry}
    (used : entry ∈ spans s protect jobs) :
    Bounds (prepare s protect jobs.length) entry.2 := by
  obtain ⟨job,zipped,equal⟩ := List.mem_map.mp used
  cases equal
  exact bound (by simpa using List.snd_lt_of_mem_zipIdx zipped)

def values (m : Assignment) (jobs : Jobs) : List Triple :=
  jobs.map (fun j => (j.2.eval m).getD (.bottom,.bottom,.bottom))

theorem patch_checked {s : State} {jobs : Jobs} (m : Assignment) (valid : Models s m)
    (checked : ∀ j ∈ jobs, ∃ v, j.2.eval m = some v ∧ InInterval v.1 v.2.2 v.2.1)
    (protect : List Nat) :
    ModelsWith (prepare s (footprintKeep protect jobs) jobs.length)
      (receipts s (footprintKeep protect jobs) jobs)
      (patch s (footprintKeep protect jobs) (values m jobs) m) := by
  let keep := footprintKeep protect jobs
  let vs := values m jobs
  let n := patch s keep vs m
  have unchanged := preserves (s := s) (protect := keep) vs m
  have count : vs.length = jobs.length := List.length_map _
  have bounds : ∀ triple ∈ vs, InInterval triple.1 triple.2.2 triple.2.1 := by
    intro triple included
    obtain ⟨j,used,rfl⟩ := List.mem_map.mp included
    obtain ⟨v,h,interval⟩ := checked j used
    simpa only [h,Option.getD] using interval
  have model := GeneralDeclarativeEndpointBatch336.fit valid keep vs bounds
  rw [count] at model
  refine ⟨model,?_⟩
  intro receipt listed
  obtain ⟨⟨j,idx⟩,inJobs,rfl⟩ := List.mem_map.mp listed
  have atJob := List.mk_mem_zipIdx_iff_getElem?.mp inJobs
  obtain ⟨v,h,valid⟩ := checked j (List.fst_mem_of_mem_zipIdx inJobs)
  have selected : vs[idx]? = some v := by
    simp [vs,values,List.getElem?_map,atJob,h]
  have sources : ∀ z ∈ inputs j.2, n z = m z := by
    intro z relevant
    exact unchanged z (List.mem_append_right _ (List.mem_append_left _ (List.mem_flatMap.mpr
      ⟨j,List.fst_mem_of_mem_zipIdx inJobs,relevant⟩)))
  refine ⟨v,(program_eq sources).trans h,?_⟩
  change Agreement (atSlots (patch s keep vs m) (slots s keep idx)) v
  rw [patch_values selected]
  exact same _

theorem realizes {s : State} {jobs : Jobs} (m : Assignment) (valid : Models s m)
    (checked : ∀ j ∈ jobs, ∃ v, j.2.eval m = some v ∧ InInterval v.1 v.2.2 v.2.1)
    (protect : List Nat) :
    ∃ n, ModelsWith (prepare s (footprintKeep protect jobs) jobs.length)
        (receipts s (footprintKeep protect jobs) jobs) n ∧
      ∀ v ∈ stateNames s ++ footprintKeep protect jobs, n v = m v :=
  ⟨_,patch_checked m valid checked protect,preserves _ _⟩

/-- Exact verified finite recording, preserving all old names and
fixed outputs. This is before the selected ties or any associated
equation, so it cannot silently impose I-58 during probing. -/
theorem approved {s : State} {p : Supported s done}
    (r : Read p arg (shape.map Prod.fst) ls us first last le ue)
    (built : ready arg shape tail ls us first last le ue = some jobs)
    (m) (fit : Models s m) (protect : List Nat) :
    ∃ n, ModelsWith (prepare s (footprintKeep protect jobs) jobs.length)
        (receipts s (footprintKeep protect jobs) jobs) n ∧
        ∀ v ∈ stateNames s ++ footprintKeep protect jobs, n v = m v :=
  realizes m fit ((list_sound r built).2 m fit) protect

end Yulang.GeneralDeclarativeEndpointOverlay336
