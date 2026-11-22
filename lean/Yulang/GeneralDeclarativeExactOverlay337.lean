import Yulang.GeneralDeclarativeExactDeleteAuth337
import Yulang.GeneralDeclarativeEndpointOverlay336

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeExactOverlay337
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (InInterval)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeEndpointRecord336 (Read interp field_interval)
open GeneralDeclarativeExactDeleteAuth337 (supported)
open GeneralDeclarativeExactDelete337 (subtract)
open GeneralDeclarativeEndpointProgram336 (Projection Jobs ready fields fields_exact template binders)
open GeneralDeclarativeEndpointNames336 (Triple)
open GeneralDeclarativeEndpointOverlay336 (Entry Agreement inputs footprintKeep receipts same)
open GeneralDeclarativeEndpointBatch336 (patch patch_values prepare atSlots slots preserves)
open GeneralDeclarativeFootprint321 (stateNames value_same)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleCanonicalRows (Row normalize residual)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralNominalCenteredHeadMatExpressions (Expr)

/-- Same literal compiler addresses as C336, but the residual now
denotes the actual standalone subtraction, not its producer mask. -/
def eval (p : Projection) (m : Assignment) : Option Triple :=
  match p with
  | .field .. => p.eval m
  | .rest a keys low high => some (interp m low,subtract keys (m a.center).1,interp m high)

def Holds (m : Assignment) (e : Entry) : Prop :=
  ∃ ideal, eval e.1 m = some ideal ∧ Agreement (atSlots m e.2) ideal

def ModelsExact (s : State) (reads : List Entry) (m : Assignment) : Prop :=
  Models s m ∧ ∀ e ∈ reads, Holds m e

theorem eval_eq {p : Projection} {m n : Assignment}
    (same : ∀ v ∈ inputs p, n v = m v) : eval p n = eval p m := by
  cases p with
  | field a k lo hi =>
    exact GeneralDeclarativeEndpointOverlay336.program_eq same
  | rest a keys lo hi =>
    have root := same _ List.mem_cons_self
    have left := value_same n m .actual lo (fun v h => same _
      (List.mem_cons_of_mem _ (List.mem_append_left _ h)))
    have right := value_same n m .actual hi (fun v h => same _
      (List.mem_cons_of_mem _ (List.mem_append_right _ h)))
    simp only [eval,interp,root,left,right]

theorem list_sound {s : State} {p : Supported s done}
    (r : Read p arg (shape.map Prod.fst) ls us first last le ue)
    (built : ready arg shape tail ls us first last le ue = some jobs) (m) (valid : Models s m) :
    ∀ j ∈ jobs, ∃ v, eval j.2 m = some v ∧ InInterval v.1 v.2.2 v.2.1 := by
  cases computed : fields arg shape first last with
  | none => simp [ready,computed] at built
  | some collected =>
    have eq := Option.some.inj (by simpa [ready,computed] using built)
    change collected ++ [_] = jobs at eq
    subst jobs
    have exactJobs := fields_exact computed
    intro j used
    rcases List.mem_append.mp used with existing|rest
    · obtain ⟨key,a,b,tied,one,two⟩ := exactJobs.2 j existing
      obtain ⟨payload,seen,bounds⟩ := field_interval r one two m valid
      exact ⟨(interp m a,payload,interp m b),by simp [eval,Projection.eval,tied,seen],bounds⟩
    · cases List.mem_singleton.mp rest
      exact ⟨_,rfl,supported r m valid⟩

def values (m : Assignment) (jobs : Jobs) : List Triple :=
  jobs.map fun j => (eval j.2 m).getD (.bottom,.bottom,.bottom)

theorem patch_checked {s : State} {jobs : Jobs} (m : Assignment) (valid : Models s m)
    (checked : ∀ j ∈ jobs, ∃ v, eval j.2 m = some v ∧ InInterval v.1 v.2.2 v.2.1)
    (protect : List Nat) :
    ModelsExact (prepare s (footprintKeep protect jobs) jobs.length)
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
  intro entry listed
  obtain ⟨⟨j,idx⟩,inJobs,rfl⟩ := List.mem_map.mp listed
  have atJob := List.mk_mem_zipIdx_iff_getElem?.mp inJobs
  obtain ⟨v,h,valid⟩ := checked j (List.fst_mem_of_mem_zipIdx inJobs)
  have selected : vs[idx]? = some v := by simp [vs,values,List.getElem?_map,atJob,h]
  have sources : ∀ z ∈ inputs j.2, n z = m z := by
    intro z relevant
    exact unchanged z (List.mem_append_right _ (List.mem_append_left _ (List.mem_flatMap.mpr
      ⟨j,List.fst_mem_of_mem_zipIdx inJobs,relevant⟩)))
  refine ⟨v,(eval_eq sources).trans h,?_⟩
  change Agreement (atSlots (patch s keep vs m) (slots s keep idx)) v
  rw [patch_values selected]
  exact same _

/-- Before candidate-specific I-58 equations, every ordinary source
model extends to those exact standalone reads without changing any
old logical name or caller-protected output. -/
theorem approved {s : State} {p : Supported s done}
    (r : Read p arg (shape.map Prod.fst) ls us first last le ue)
    (built : ready arg shape tail ls us first last le ue = some jobs)
    (m) (fit : Models s m) (protect : List Nat) :
    ∃ n, ModelsExact (prepare s (footprintKeep protect jobs) jobs.length)
        (receipts s (footprintKeep protect jobs) jobs) n ∧
      ∀ v ∈ stateNames s ++ footprintKeep protect jobs, n v = m v :=
  ⟨_,patch_checked m fit (list_sound r built m fit) protect,preserves _ _⟩

end Yulang.GeneralDeclarativeExactOverlay337
