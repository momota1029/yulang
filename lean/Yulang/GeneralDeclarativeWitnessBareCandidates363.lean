import Yulang.GeneralDeclarativeWitnessNonpointGraph363

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessBareCandidates363
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessNativePreparation360 (shape)
open GeneralDeclarativeWitnessModeCoverage357 (checkDecl)
open GeneralDeclarativeWitnessProblem349 (declared)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeWhere319 (Capture)

def variables : List Pattern → Option (List Nat)
  | [] => some []
  | .var n :: rest => (variables rest).map (n :: ·)
  | _ :: _ => none

theorem variables_source {source : List Pattern} {ns : List Nat}
    (got : variables source = some ns) : source = ns.map Pattern.var := by
  induction source generalizing ns with
  | nil =>
    have eq : [] = ns := Option.some.inj got
    cases eq
    rfl
  | cons p tail ih =>
    cases p <;> try contradiction
    rename_i n
    cases pick : variables tail with
    | none => simp [variables,pick] at got
    | some rest =>
      have same : n :: rest = ns := by simpa [variables,pick] using got
      cases same
      simp [ih pick]

def visible (e : Environment) (d : Demand) : List Declaration :=
  e.source.declarations.filter (fun impl => impl.role == d.role)

structure FitsBare (e : Environment) (d : Demand) (impl : Declaration) where
  binders : List Nat
  source : impl.head.map normalize = binders.map Pattern.var
  distinct : binders.Nodup
  arity : d.arguments.length = binders.length
  writtenTypes : checkDecl e impl = true
  supportedShape : shape e.source impl = true
  requested : declared e.source d = true

def FitsBare.captures {e d impl} (x : FitsBare e d impl) : List (Nat × Capture) :=
  x.binders.zip d.arguments

def candidate (e : Environment) (d : Demand) (impl : Declaration) : Option (FitsBare e d impl) :=
  match shape : variables (impl.head.map normalize) with
  | none => none
  | some names =>
    if scope : names.Nodup ∧ d.arguments.length = names.length then
      if terms : checkDecl e impl && GeneralDeclarativeWitnessNativePreparation360.shape e.source impl &&
          declared e.source d then
        have ending := Bool.and_eq_true_iff.mp terms
        have checked := Bool.and_eq_true_iff.mp ending.1
        some ⟨names,variables_source shape,scope.1,scope.2,checked.1,checked.2,ending.2⟩
      else none
    else none

inductive Covered (e : Environment) (d : Demand) : List Declaration → Type where
  | none : Covered e d []
  | next : FitsBare e d impl → Covered e d rest → Covered e d (impl::rest)

def scan (e : Environment) (d : Demand) : (cs : List Declaration) → Option (Covered e d cs)
  | [] => some .none
  | a::as => do
    let first ← candidate e d a
    let rest ← scan e d as
    pure (.next first rest)

/-- This finite resolver is explanatory only for a fully covered visible
bare-binder set. Unsupported heads give no evidence, not a rejection and
not an excuse to select some other candidate. -/
inductive Decision (e : Environment) (d : Demand) where
  | selected (impl : Declaration) (all : visible e d = [impl]) (proof : FitsBare e d impl)
  | ambiguous (a b : Declaration) (tail : List Declaration)
      (order : visible e d = a::b::tail) (different : a.id ≠ b.id)
      (all : Covered e d (a::b::tail))

def decideCandidates (e : Environment) (d : Demand) : Option (Decision e d) :=
  match order : visible e d with
  | [] => none
  | [a] => (candidate e d a).map (.selected a order)
  | a::b::rest =>
    if apart : a.id ≠ b.id then
      (scan e d (a::b::rest)).map (.ambiguous a b rest order apart)
    else none

theorem member_of_visible {e : Environment} {d : Demand} {impl : Declaration}
    (h : impl ∈ visible e d) : impl ∈ e.source.declarations ∧ impl.role = d.role := by
  simpa [visible,List.mem_filter] using h

theorem selected_descriptor_only_of_current_visible {e : Environment} {d : Demand} {impl : Declaration}
    (exact : visible e d = [impl]) :
    impl ∈ e.source.declarations ∧ impl.role = d.role ∧
    ∀ other,other ∈ visible e d → other = impl := by
  have h := member_of_visible (show impl ∈ visible e d from exact.symm ▸ List.mem_cons_self)
  exact ⟨h.1,h.2,fun _ h => List.mem_singleton.mp (exact ▸ h)⟩

end Yulang.GeneralDeclarativeWitnessBareCandidates363
