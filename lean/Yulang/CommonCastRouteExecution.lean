import Yulang.CommonCastRoutes
import Yulang.PureCasts

/-!
# Compiling extracted routes from checked declaration bodies

A declaration table contains actual bodies, their inferred signed rows and the
body bounds. It contains no preselected conversion plan. The executable route
extractor selects the edges and this compiler composes their checked bodies.

This closes the finite route-to-execution bridge. Deriving the declaration
body bounds and endpoint carriers from the full Common source judgment is a
separate obligation; this module does not assume that a ground endpoint checker
already establishes those source contracts.
-/

namespace Yulang.CommonCastRouteExecution

open CommonCastRoutes FiniteReachability PureCasts Directed

universe u
variable {vertices scopes : Nat} {Key Payload Response : Type u}

structure Bodies (adj : Adj vertices) (Carrier : Fin vertices → Type u)
    (scopes : Nat) (Key Payload Response : Type u) where
  declaration : ∀ source target, target ∈ adj source →
    Declaration scopes Key Payload Response (Carrier source) (Carrier target)
  checked : ∀ source target edge, (declaration source target edge).check = true

def compileSteps {adj : Adj vertices} {Carrier : Fin vertices → Type u}
    (bodies : Bodies adj Carrier scopes Key Payload Response)
    (source target : Fin vertices) : List (Fin vertices) →
    Option (Plan scopes Key Payload Response (Carrier source) (Carrier target))
  | [] => if same : source = target then some (same ▸ Plan.keep) else none
  | next :: rest =>
      if edge : next ∈ adj source then
        (compileSteps bodies next target rest).map fun tail =>
          .chain (.declared (bodies.declaration source next edge)
            (bodies.checked source next edge)) tail
      else none

theorem compileSteps_complete {adj : Adj vertices} {Carrier : Fin vertices → Type u}
    (bodies : Bodies adj Carrier scopes Key Payload Response)
    {source target : Fin vertices} {steps : List (Fin vertices)}
    (valid : Edges adj source steps target) :
    (compileSteps bodies source target steps).isSome = true := by
  induction valid with
  | nil => simp [compileSteps]
  | cons edge _ ih => simp [compileSteps, edge, ih]

theorem compileSteps_sound {adj : Adj vertices} {Carrier : Fin vertices → Type u}
    (bodies : Bodies adj Carrier scopes Key Payload Response)
    (source target : Fin vertices) (steps : List (Fin vertices))
    (compiled : (compileSteps bodies source target steps).isSome = true) :
    Edges adj source steps target := by
  induction steps generalizing source with
  | nil =>
      by_cases same : source = target
      · subst source; exact .nil
      · simp [compileSteps, same] at compiled
  | cons next rest ih =>
      by_cases edge : next ∈ adj source
      · apply Edges.cons edge
        apply ih
        simpa [compileSteps, edge] using compiled
      · simp [compileSteps, edge] at compiled

def compile {adj : Adj vertices} {Carrier : Fin vertices → Type u}
    (bodies : Bodies adj Carrier scopes Key Payload Response)
    (source target : Fin vertices) :
    Option (Plan scopes Key Payload Response (Carrier source) (Carrier target)) :=
  (CommonCastRoutes.search adj source target).bind fun route =>
    compileSteps bodies source target route.steps

/-- All finite graphs and all checked body tables; no external plan or chosen
route, no fuel, and no successful-search premise. -/
theorem compile_exact {adj : Adj vertices} {Carrier : Fin vertices → Type u}
    (bodies : Bodies adj Carrier scopes Key Payload Response)
    (source target : Fin vertices) :
    (compile bodies source target).isSome = true ↔ Reach adj [source] target := by
  have exactness := CommonCastRoutes.search_exact adj source target
  cases found : CommonCastRoutes.search adj source target with
  | none => simpa [compile, found] using exactness
  | some route =>
      have successful := compileSteps_complete bodies route.valid
      simpa [compile, found, successful] using exactness

/-- Every plan returned by the actual compiler has a pure immediate row. -/
theorem compiled_run_pure {adj : Adj vertices} {Carrier : Fin vertices → Type u}
    (bodies : Bodies adj Carrier scopes Key Payload Response)
    (source target : Fin vertices)
    (plan : Plan scopes Key Payload Response (Carrier source) (Carrier target))
    (_compiled : compile bodies source target = some plan) (value : Carrier source) :
    plan.run value = .pure (plan.value value) := plan.run_eq_pure value

/-- The original source computation is evaluated once. Every signed request,
payload and response branch is retained when the selected route is inserted. -/
theorem compiled_insert_requestTree {adj : Adj vertices} {Carrier : Fin vertices → Type u}
    (bodies : Bodies adj Carrier scopes Key Payload Response)
    (source target : Fin vertices)
    (plan : Plan scopes Key Payload Response (Carrier source) (Carrier target))
    (_compiled : compile bodies source target = some plan)
    (original : Computation scopes Key Payload Response (Carrier source)) :
    requestTree (insert plan original) = requestTree original :=
  insert_requestTree plan original

end Yulang.CommonCastRouteExecution
