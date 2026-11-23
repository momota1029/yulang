import Yulang.GeneralDeclarativeWitnessOrdinarySpecialCase357
import Yulang.CommonRecursiveNominalIntervalContextAdmission

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessSparseIntervals357
open GeneralDeclarativeWitnessConstructorModes357 (Environment Use Mode readUse)
open CommonRecursiveNominalIntervals
  (Endpoint Bounds Argument ContextWellFormed ContextDerives compileInContext compile_in_context_exact result_some)
open CommonDeclaredNominalInspection (Registry Parameter)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (Atom All)

abbrev Site := Nat × Nat

mutual
def visited {α : Type} : Endpoint α → List Site
  | .ordinary _ => []
  | .nominal key args => (key,args.length) :: visitedList args
termination_by x => sizeOf x

def visitedList {α : Type} : List (Argument α) → List Site
  | [] => []
  | .inl (.point item) :: last => visited item ++ visitedList last
  | .inl (.interval lo hi) :: last => visited lo ++ visited hi ++ visitedList last
  | .inr _ :: last => visitedList last
termination_by xs => sizeOf xs
end

def names (mode : Mode) (arity : Nat) : Option (List Parameter) :=
  match mode with
  | .primitive _ => none
  | .invariant => some (List.replicate arity ⟨.value,.invariant⟩)
  | .declared ps => some ps

def Legal (e : Environment) (table : Registry) (site : Site) : Prop :=
  ∃ use : Use e site.1 site.2,∃ ps, names use.mode site.2 = some ps ∧ table[site.1]? = some ps

def hasLicense (e : Environment) (table : Registry) (p : Site) : Bool :=
  match readUse e p.1 p.2 with
  | none => false
  | some use =>
    match names use.mode p.2 with
    | none => false
    | some ps => decide (table[p.1]? = some ps)

theorem independently_licensed {e : Environment} {table : Registry} {site : Site}
    (verified : hasLicense e table site = true) : Legal e table site := by
  unfold hasLicense at verified
  cases got : readUse e site.1 site.2 with
  | none => simp [got] at verified
  | some use =>
    cases q : names use.mode site.2 with
    | none => simp [got,q] at verified
    | some ps =>
      simp only [got,q,decide_eq_true_eq] at verified
      exact ⟨use,ps,q,verified⟩

structure Compiled (e : Environment) (table : Registry) (context : Bool) (lo hi : Endpoint Nat) where
  authority : ∀ site ∈ visited lo ++ visited hi,Legal e table site
  rows : List (Atom Nat)
  exact : compileInContext table context lo hi = some rows

/-- A dense computation table is a local adapter only. Every visited name
must resolve in the actual sparse source with its *original* arity and
variance. A zero-length entry cannot justify an absent declaration. -/
def compile (e : Environment) (table : Registry) (context : Bool) (lo hi : Endpoint Nat) :
    Option (Compiled e table context lo hi) :=
  if given : (visited lo ++ visited hi).all (hasLicense e table) = true then
    match proof : compileInContext table context lo hi with
    | some rows => some ⟨fun site h => independently_licensed (List.all_eq_true.mp given site h),rows,proof⟩
    | none => none
  else none

theorem declared_context_meaning {e table context lo hi} (run : Compiled e table context lo hi)
    (m : Nat → Comp Common.model) (facts : All Common.model m run.rows) :
    ContextWellFormed table context lo ∧ ContextWellFormed table context hi ∧
      ContextDerives table m context lo hi := by
  apply (compile_in_context_exact table m context lo hi).mp
  rw [run.exact,result_some]
  exact facts

theorem no_absent_site {e : Environment} {table ctx lo hi} (run : Compiled e table ctx lo hi)
    {site : Site} (used : site ∈ visited lo ++ visited hi) :
    (GeneralSourceMetadataRows291.constructors e.source.declared site.1).isSome = true := by
  obtain ⟨known,_,_,_⟩ := run.authority site used
  rw [known.actual]
  rfl

end Yulang.GeneralDeclarativeWitnessSparseIntervals357
