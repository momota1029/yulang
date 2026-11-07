import Yulang.CommonCastSourceBodies
import Yulang.CoreExpr

/-!
# Resolved construction fields and synthesized pure casts

Each original source expression occurs in one site. Fixed fields and fields
using an invariant parameter share one ordered site vector; repeated parameter
references resolve through one parameter assignment. Cast code is synthesized
from the actual checked source registry, not supplied as an external plan.

The source judgment here is the existing resolved operational judgment. This
closes executable site validation and sequencing at that layer; generation of
arbitrary Common construction constraints and their full solved family remain
separate obligations.
-/

namespace Yulang.CommonConstructionResolved

open Directed PureCasts
open OperationalTyping (Shape VTy CTy Expr Env Tree Value ValidValue)

variable {vertices parameters scopes : Nat} {Key Atom : Type} [DecidableEq Key]

inductive Target (parameters vertices : Nat) where
  | fixed : Fin vertices → Target parameters vertices
  | parameter : Fin parameters → Target parameters vertices

def Target.resolve (assignment : Fin parameters → Fin vertices) : Target parameters vertices → Fin vertices
  | .fixed target => target
  | .parameter index => assignment index

structure Site (parameters vertices scopes : Nat) (Key Atom : Type)
    (context : List Shape) (shape : Fin vertices → Shape) where
  position : Nat
  field : Nat
  source : Fin vertices
  target : Target parameters vertices
  expression : Expr scopes Key Atom context (shape source)

def Site.Valid {context : List Shape} {shape : Fin vertices → Shape}
    (types : (vertex : Fin vertices) → VTy scopes Key (shape vertex))
    (environment : Env (CTy scopes Key) context)
    (site : Site parameters vertices scopes Key Atom context shape) : Prop :=
  ∃ result, OperationalTyping.Typing environment site.expression result ∧
    OperationalTyping.VLe result.value (types site.source)

def Site.check {context : List Shape} {shape : Fin vertices → Shape}
    (types : (vertex : Fin vertices) → VTy scopes Key (shape vertex))
    (environment : Env (CTy scopes Key) context)
    (site : Site parameters vertices scopes Key Atom context shape) : Bool :=
  match OperationalTyping.infer environment site.expression with
  | none => false
  | some result => OperationalTyping.checkV result.value (types site.source)

theorem Site.check_exact {context : List Shape} {shape : Fin vertices → Shape}
    (types : (vertex : Fin vertices) → VTy scopes Key (shape vertex))
    (environment : Env (CTy scopes Key) context)
    (site : Site parameters vertices scopes Key Atom context shape) :
    site.check types environment = true ↔ site.Valid types environment := by
  constructor
  · intro checked
    cases inferred : OperationalTyping.infer environment site.expression with
    | none => simp [Site.check, inferred] at checked
    | some result =>
        exact ⟨result, OperationalTyping.infer_sound _ _ _ inferred,
          (OperationalTyping.checkV_exact _ _).mp (by simpa [Site.check, inferred] using checked)⟩
  · rintro ⟨result, typed, subtype⟩
    simp [Site.check, OperationalTyping.infer_complete typed,
      (OperationalTyping.checkV_exact _ _).mpr subtype]

abbrev Carrier (scopes : Nat) (Key Atom : Type) {vertices : Nat}
    (shape : Fin vertices → Shape) (types : (vertex : Fin vertices) → VTy scopes Key (shape vertex))
    (vertex : Fin vertices) := { value : Value scopes Key Atom (shape vertex) // ValidValue (types vertex) value }

structure Compiled {context : List Shape} {shape : Fin vertices → Shape}
    {types : (vertex : Fin vertices) → VTy scopes Key (shape vertex)}
    {adj : FiniteReachability.Adj vertices}
    (registry : CommonCastSourceBodies.Registry adj shape types (Atom := Atom))
    (environment : Env (CTy scopes Key) context)
    (assignment : Fin parameters → Fin vertices)
    (site : Site parameters vertices scopes Key Atom context shape) where
  sourceChecked : site.check types environment = true
  conversion : Plan scopes Key Atom Atom (Carrier scopes Key Atom shape types site.source)
    (Carrier scopes Key Atom shape types (site.target.resolve assignment))

def compileSite {context : List Shape} {shape : Fin vertices → Shape}
    {types : (vertex : Fin vertices) → VTy scopes Key (shape vertex)}
    {adj : FiniteReachability.Adj vertices}
    (registry : CommonCastSourceBodies.Registry adj shape types (Atom := Atom))
    (environment : Env (CTy scopes Key) context) (assignment : Fin parameters → Fin vertices)
    (site : Site parameters vertices scopes Key Atom context shape) :
    Option (Compiled registry environment assignment site) :=
  if checked : site.check types environment = true then
    (registry.synthesize site.source (site.target.resolve assignment)).map fun plan => ⟨checked, plan⟩
  else none

/-- Every original source expression and fixed/shared target, in an arbitrary
static source environment. All source and cast checks are executed. -/
theorem compile_site_exact {context : List Shape} {shape : Fin vertices → Shape}
    {types : (vertex : Fin vertices) → VTy scopes Key (shape vertex)}
    {adj : FiniteReachability.Adj vertices}
    (registry : CommonCastSourceBodies.Registry adj shape types (Atom := Atom))
    (environment : Env (CTy scopes Key) context) (assignment : Fin parameters → Fin vertices)
    (site : Site parameters vertices scopes Key Atom context shape) :
    (compileSite registry environment assignment site).isSome = true ↔
      site.Valid types environment ∧ registry.Valid ∧
        FiniteReachability.Reach adj [site.source] (site.target.resolve assignment) := by
  have casts := CommonCastSourceBodies.source_registry_synthesize_exact registry
    site.source (site.target.resolve assignment)
  by_cases checked : site.check types environment = true
  · have valid := (site.check_exact types environment).mp checked
    cases synthesized : registry.synthesize site.source (site.target.resolve assignment) <;>
      simpa [compileSite, checked, synthesized, valid] using casts
  · have invalid : ¬ site.Valid types environment := fun valid =>
      checked ((site.check_exact types environment).mpr valid)
    simp [compileSite, checked, invalid]

private def refine {A : Type} {P : A → Prop}
    (tree : Computation scopes Key Atom Atom A) (valid : OperationalTyping.AllReturns P tree) :
    Computation scopes Key Atom Atom { value : A // P value } :=
  match tree with
  | .pure value => .pure ⟨value, valid⟩
  | .request occurrence payload resume => .request occurrence payload
      (fun response => refine (resume response) (valid response))

omit [DecidableEq Key] in
private theorem refine_executes {A : Type} {P : A → Prop}
    (tree : Computation scopes Key Atom Atom A) (valid : OperationalTyping.AllReturns P tree) :
    mapValue Subtype.val (refine tree valid) = tree := by
  induction tree with
  | pure value => rfl
  | request occurrence payload resume ih =>
      exact congrArg (Computation.request occurrence payload) (funext fun response => ih response (valid response))

private theorem source_returns {context : List Shape} {shape : Fin vertices → Shape}
    {types : (vertex : Fin vertices) → VTy scopes Key (shape vertex)}
    {environment : Env (CTy scopes Key) context}
    {site : Site parameters vertices scopes Key Atom context shape}
    (checked : site.check types environment = true)
    (runtime : Env (Tree scopes Key Atom) context) (valid : OperationalTyping.EnvValid environment runtime) :
    OperationalTyping.AllReturns (ValidValue (types site.source)) (OperationalTyping.eval runtime site.expression) := by
  obtain ⟨result, typed, subtype⟩ := (site.check_exact types environment).mp checked
  exact OperationalTyping.allReturns_mono _ _
    (OperationalTyping.value_subtype_sound _ _ subtype)
    _ (OperationalTyping.typing_sound typed runtime valid).2

def Compiled.run {context : List Shape} {shape : Fin vertices → Shape}
    {types : (vertex : Fin vertices) → VTy scopes Key (shape vertex)}
    {adj : FiniteReachability.Adj vertices}
    {registry : CommonCastSourceBodies.Registry adj shape types (Atom := Atom)}
    {environment : Env (CTy scopes Key) context} {assignment : Fin parameters → Fin vertices}
    {site : Site parameters vertices scopes Key Atom context shape}
    (compiled : Compiled registry environment assignment site)
    (runtime : Env (Tree scopes Key Atom) context) (valid : OperationalTyping.EnvValid environment runtime) :
    Computation scopes Key Atom Atom (Carrier scopes Key Atom shape types (site.target.resolve assignment)) :=
  insert compiled.conversion (refine (OperationalTyping.eval runtime site.expression)
    (source_returns compiled.sourceChecked runtime valid))

/-- Actual source evaluation is retained. The cast code was synthesized from
checked source bodies, and every signed request and response branch is kept. -/
theorem compiled_site_requestTree {context : List Shape} {shape : Fin vertices → Shape}
    {types : (vertex : Fin vertices) → VTy scopes Key (shape vertex)}
    {adj : FiniteReachability.Adj vertices}
    {registry : CommonCastSourceBodies.Registry adj shape types (Atom := Atom)}
    {environment : Env (CTy scopes Key) context} {assignment : Fin parameters → Fin vertices}
    {site : Site parameters vertices scopes Key Atom context shape}
    (compiled : Compiled registry environment assignment site)
    (runtime : Env (Tree scopes Key Atom) context) (valid : OperationalTyping.EnvValid environment runtime) :
    requestTree (compiled.run runtime valid) = requestTree (OperationalTyping.eval runtime site.expression) := by
  change requestTree (insert compiled.conversion _) = _
  rw [insert_requestTree]
  have same := refine_executes (OperationalTyping.eval runtime site.expression)
    (source_returns compiled.sourceChecked runtime valid)
  exact (mapValue_comp _ _ _).symm.trans (congrArg requestTree same)

end Yulang.CommonConstructionResolved

namespace Yulang.CommonConstructionResolved

open Directed PureCasts
open OperationalTyping (Shape VTy CTy Expr Env Tree Value ValidValue)

variable {vertices parameters scopes : Nat} {Key Atom : Type} [DecidableEq Key]
variable {context : List Shape} {shape : Fin vertices → Shape}
variable {types : (vertex : Fin vertices) → VTy scopes Key (shape vertex)}
variable {adj : FiniteReachability.Adj vertices}

inductive Code (registry : CommonCastSourceBodies.Registry adj shape types (Atom := Atom))
    (environment : Env (CTy scopes Key) context) (assignment : Fin parameters → Fin vertices) :
    List (Site parameters vertices scopes Key Atom context shape) → Type 1 where
  | nil : Code registry environment assignment []
  | cons {site rest} : Compiled registry environment assignment site →
      Code registry environment assignment rest → Code registry environment assignment (site :: rest)

def compile (registry : CommonCastSourceBodies.Registry adj shape types (Atom := Atom))
    (environment : Env (CTy scopes Key) context) (assignment : Fin parameters → Fin vertices) :
    (sites : List (Site parameters vertices scopes Key Atom context shape)) →
      Option (Code registry environment assignment sites)
  | [] => some .nil
  | site :: rest => do
      return .cons (← compileSite registry environment assignment site)
        (← compile registry environment assignment rest)

/-- Every source site is checked, including fixed fields and repeated shared
parameters, and the compiled vector has exactly the original ordered index. -/
theorem compile_exact (registry : CommonCastSourceBodies.Registry adj shape types (Atom := Atom))
    (environment : Env (CTy scopes Key) context) (assignment : Fin parameters → Fin vertices)
    (sites : List (Site parameters vertices scopes Key Atom context shape)) :
    (compile registry environment assignment sites).isSome = true ↔
      ∀ site ∈ sites, site.Valid types environment ∧ registry.Valid ∧
        FiniteReachability.Reach adj [site.source] (site.target.resolve assignment) := by
  induction sites with
  | nil => simp [compile]
  | cons site rest ih =>
      have pair : (compile registry environment assignment (site :: rest)).isSome =
          ((compileSite registry environment assignment site).isSome &&
            (compile registry environment assignment rest).isSome) := by
        rw [compile]
        cases compileSite registry environment assignment site <;>
          cases compile registry environment assignment rest <;> rfl
      rw [pair, Bool.and_eq_true, compile_site_exact, ih]
      simp

abbrev BuiltValues (scopes : Nat) (Key Atom : Type) {vertices : Nat}
    (shape : Fin vertices → Shape) (types : (vertex : Fin vertices) → VTy scopes Key (shape vertex)) :=
  List ((vertex : Fin vertices) × Carrier scopes Key Atom shape types vertex)

def Code.run {registry : CommonCastSourceBodies.Registry adj shape types (Atom := Atom)}
    {environment : Env (CTy scopes Key) context} {assignment : Fin parameters → Fin vertices}
    {sites : List (Site parameters vertices scopes Key Atom context shape)}
    (code : Code registry environment assignment sites)
    (runtime : Env (Tree scopes Key Atom) context) (valid : OperationalTyping.EnvValid environment runtime) :
    Computation scopes Key Atom Atom (BuiltValues scopes Key Atom shape types) :=
  match code with
  | .nil => .pure []
  | .cons (site := site) first rest =>
      (first.run runtime valid).bind fun value =>
        (rest.run runtime valid).bind fun values =>
          .pure (⟨site.target.resolve assignment, value⟩ :: values)

/-- Reference evaluation of the original sources, in their original order.
A nonreturning source prevents later sites from being reached. -/
def originalRequests (runtime : Env (Tree scopes Key Atom) context) :
    List (Site parameters vertices scopes Key Atom context shape) →
      Computation scopes Key Atom Atom PUnit
  | [] => .pure ⟨⟩
  | site :: rest => (OperationalTyping.eval runtime site.expression).bind fun _ => originalRequests runtime rest

omit [DecidableEq Key] in
private theorem erase_bind {A B : Type} (source : Computation scopes Key Atom Atom A)
    (next : A → Computation scopes Key Atom Atom B) :
    requestTree (source.bind next) = source.bind (fun value => requestTree (next value)) := by
  induction source with
  | pure value => rfl
  | request occurrence payload resume ih =>
      exact congrArg (Computation.request occurrence payload) (funext ih)

omit [DecidableEq Key] in
private theorem constant_bind {A B : Type} (source : Computation scopes Key Atom Atom A)
    (next : Computation scopes Key Atom Atom B) :
    source.bind (fun _ => next) = (requestTree source).bind (fun _ => next) := by
  induction source with
  | pure value => rfl
  | request occurrence payload resume ih =>
      exact congrArg (Computation.request occurrence payload) (funext ih)

omit [DecidableEq Key] in
private theorem erase_pure_bind {A B : Type} (source : Computation scopes Key Atom Atom A) (f : A → B) :
    requestTree (source.bind (fun value => .pure (f value))) = requestTree source := by
  rw [bind_pure_map]
  exact mapValue_comp _ _ _

/-- All fixed and parameter fields retain their entire source request tree.
Each reached site is evaluated once; after a source returns, its synthesized
pure conversion runs before the next source. No successful-evaluation premise
is needed, and no later source is forced after a nonreturning one. -/
theorem code_requestTree {registry : CommonCastSourceBodies.Registry adj shape types (Atom := Atom)}
    {environment : Env (CTy scopes Key) context} {assignment : Fin parameters → Fin vertices}
    {sites : List (Site parameters vertices scopes Key Atom context shape)}
    (code : Code registry environment assignment sites)
    (runtime : Env (Tree scopes Key Atom) context) (valid : OperationalTyping.EnvValid environment runtime) :
    requestTree (code.run runtime valid) = originalRequests runtime sites := by
  induction code with
  | nil => rfl
  | @cons site rest first tail ih =>
      change requestTree ((first.run runtime valid).bind (fun value =>
        (tail.run runtime valid).bind (fun values =>
          .pure (⟨site.target.resolve assignment, value⟩ :: values)))) = _
      rw [erase_bind]
      simp only [erase_pure_bind]
      rw [constant_bind, compiled_site_requestTree, ih]
      exact (constant_bind _ _).symm

@[simp] theorem fixed_field_target (assignment : Fin parameters → Fin vertices) (target : Fin vertices) :
    Target.resolve assignment (.fixed target) = target := rfl

/-- Every occurrence of the same invariant parameter reads the same resolved
endpoint, without duplicating its source expression into separate sites. -/
@[simp] theorem shared_parameter_target (assignment : Fin parameters → Fin vertices) (index : Fin parameters) :
    Target.resolve assignment (.parameter index) = assignment index := rfl

end Yulang.CommonConstructionResolved
