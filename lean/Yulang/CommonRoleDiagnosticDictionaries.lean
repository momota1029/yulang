import Yulang.CommonRoleRecursiveDiagnostics
import Yulang.RoleDictionaries

/-! Structural projection of retained diagnostics to the existing ordered
indexed dictionary payload. Failure nodes remain in the original diagnostic;
no resolver, success evidence or fuel is needed to compute the projection. -/
namespace Yulang.CommonRoleDiagnosticDictionaries
open Roles CommonRoleRecursiveDiagnostics RoleDictionaries

/-- Project every child in place, failing if any child has no dictionary. -/
def project : Tree → Option Plan
  | .missing _ | .overlap _ _ => none
  | .selected _ i cs => (cs.mapM project).map (Plan.node i)

theorem mapM_isSome {α β : Type} (f : α → Option β) (xs : List α) :
    (xs.mapM f).isSome = true ↔ ∀ x ∈ xs, (f x).isSome = true := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.mapM_cons]
    cases hx : f x <;> cases hs : xs.mapM f <;> simp_all

theorem mapM_some_of_pointwise {α β : Type} (xs : List α) (f : α → Option β)
    (g : α → β) (h : ∀ x ∈ xs, f x = some (g x)) :
    xs.mapM f = some (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons,List.map_cons]
    rw [h x (by simp),ih (by intro y hy; exact h y (by simp [hy]))]
    rfl

/-- This equivalence also holds for trees not produced by the builder. -/
theorem project_success (t : Tree) :
    (project t).isSome = true ↔ t.status = .resolved := by
  induction t using Tree.rec (motive_2 := fun cs =>
      ∀ t ∈ cs, (project t).isSome = true ↔ t.status = .resolved) with
  | missing g => simp [project,Tree.status]
  | overlap g hs => simp [project,Tree.status]
  | selected g i cs ih =>
    simp only [project,Option.isSome_map,mapM_isSome,Tree.status,combine_eq_resolved]
    constructor
    · intro h r hr
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hr
      exact (ih t ht).mp (h t ht)
    · intro h t ht
      exact (ih t ht).mpr (h t.status (List.mem_map.mpr ⟨t,ht,rfl⟩))
  | nil => rename_i t ht; simp at ht
  | cons t ts ih ihts =>
    rename_i s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ih
    · exact ihts s hs

/-- The actual selected declaration and each repeated child occurrence agree. -/
theorem dictionary_projects (impls : List Impl) (wf : WellFormed impls)
    {g : Goal} (d : Dictionary impls g) :
    project (diagnose impls wf g) = some d.erase := by
  induction d with
  | @impl g i unique children ih =>
    rw [diagnose_selected impls wf g i unique,project,Dictionary.erase_impl]
    have h : (i.constraints.attach.mapM fun c =>
        project (diagnose impls wf (c.val.subst (matchingSubst i.head g.args)))) =
        some (i.constraints.attach.map fun c => (children c.val c.property).erase) :=
      mapM_some_of_pointwise _ _ _ (by intro c _; exact ih c.val c.property)
    have mapped := congrArg (Option.map (Plan.node i)) h
    simpa only [List.mapM_map,Function.comp_def,Option.map_some,
      List.mapM_subtype,List.unattach_attach] using mapped

/-- Payload equality, not merely equality of successful status. -/
theorem diagnose_project_exact (impls : List Impl) (wf : WellFormed impls)
    (g : Goal) (p : Plan) :
    project (diagnose impls wf g) = some p ↔
      ∃ d : Dictionary impls g, d.erase = p := by
  constructor
  · intro found
    have success : resolve impls wf g = .resolved := by
      rw [← diagnose_status]
      exact (project_success _).mp (by rw [found]; rfl)
    let d := buildResolved impls wf g success
    exact ⟨d,Option.some.inj ((dictionary_projects impls wf d).symm.trans found)⟩
  · rintro ⟨d,rfl⟩
    exact dictionary_projects impls wf d

theorem diagnose_project_elaborate (impls : List Impl) (wf : WellFormed impls)
    (g : Goal) (p : Plan) :
    project (diagnose impls wf g) = some p ↔ elaborate impls wf g = .resolved p := by
  rw [diagnose_project_exact,elaborate_success_iff]

theorem project_all_visible (impls : List Impl) (wf : WellFormed impls)
    (g : Goal) (p : Plan) (found : project (diagnose impls wf g) = some p) :
    ∀ i ∈ p.declarations, i ∈ impls := by
  obtain ⟨d,rfl⟩ := (diagnose_project_exact impls wf g p).mp found
  exact d.all_visible

/-- Child positions remain observable in the actual dictionary payload. -/
def planChildren : Plan → List Plan
  | .node _ ps => ps

def follow (p : Plan) : List Nat → Option Plan
  | [] => some p
  | k :: rest => (planChildren p)[k]?.bind (fun child => follow child rest)

theorem mapM_getElem {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
    (h : xs.mapM f = some ys) (k : Nat) : ys[k]? = (xs[k]?).bind f := by
  induction xs generalizing ys k with
  | nil =>
    have eq : ys = [] := by simpa using h.symm
    subst ys
    simp
  | cons x xs ih =>
    cases hx : f x with
    | none => simp [List.mapM_cons,hx] at h
    | some y =>
      cases hs : xs.mapM f with
      | none => simp [List.mapM_cons,hx,hs] at h
      | some zs =>
        have eq : y :: zs = ys := by simpa [List.mapM_cons,hx,hs] using h
        subst ys
        cases k with
        | zero => simp [hx]
        | succ k => simpa using ih zs hs k

theorem project_children (t : Tree) (p : Plan) (h : project t = some p) :
    t.children.mapM project = some (planChildren p) := by
  cases t with
  | missing g => simp [project] at h
  | overlap g hs => simp [project] at h
  | selected g i cs =>
    cases hc : cs.mapM project with
    | none => simp [project,hc] at h
    | some ps =>
      have eq : Plan.node i ps = p := by simpa [project,hc] using h
      subst p
      exact hc

/-- Exact addressed subtree payloads, including repeated sibling positions. -/
theorem project_follow_exact (t : Tree) (p : Plan) (h : project t = some p)
    (path : List Nat) (q : Plan) :
    follow p path = some q ↔ ∃ child, t.follow path = some child ∧ project child = some q := by
  induction path generalizing t p q with
  | nil => simp [follow,Tree.follow,h]
  | cons k rest ih =>
    have children := project_children t p h
    have position := mapM_getElem project t.children (planChildren p) children k
    simp only [follow,Tree.follow,position]
    cases hc : t.children[k]? with
    | none => simp
    | some c =>
      have success := (mapM_isSome project t.children).mp (by rw [children]; rfl)
        c (List.mem_of_getElem? hc)
      obtain ⟨cp,hp⟩ := Option.isSome_iff_exists.mp success
      simp only [Option.bind_some,hp]
      exact ih c cp hp q

/-- A successful root's dictionary path is exactly the independent declaration
path and the complete existing indexed dictionary of its target. -/
theorem diagnose_plan_path_exact (impls : List Impl) (wf : WellFormed impls)
    (g : Goal) (p : Plan) (h : project (diagnose impls wf g) = some p)
    (path : List Nat) (q : Plan) :
    follow p path = some q ↔ ∃ target, Path impls g path target ∧
      ∃ d : Dictionary impls target, d.erase = q := by
  rw [project_follow_exact _ p h]
  constructor
  · rintro ⟨child,found,projected⟩
    obtain ⟨target,route,eq⟩ := (diagnose_follow_exact impls wf g path child).mp found
    rw [← eq] at projected
    exact ⟨target,route,(diagnose_project_exact impls wf target q).mp projected⟩
  · rintro ⟨target,route,dict⟩
    exact ⟨diagnose impls wf target,(diagnose_follow_exact impls wf g path _).mpr
      ⟨target,route,rfl⟩,(diagnose_project_exact impls wf target q).mpr dict⟩

end Yulang.CommonRoleDiagnosticDictionaries
