import Yulang.GeneralDeclarativeWitnessRecord349
import Yulang.GeneralDeclarativeExactOverlay337

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessProjection349
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture InInterval)
open GeneralDeclarativeWitnessManifest349 (Manifest Attached support)
open GeneralDeclarativeWitnessRecord349 (Wire)
open GeneralDeclarativeEndpointProgram336 (Jobs template ready)
open GeneralDeclarativeEndpointNames336 (Triple)
open GeneralNominalCommonBridge (Assignment)

def unpack : Pattern → Option (List (Nat × Nat) × Nat)
  | .var tail => some ([],tail)
  | .record label (.var binder) rest =>
    (unpack rest).map (fun (fields,tail) => ((label,binder)::fields,tail))
  | _ => none

theorem unpack_exact {pat : Pattern} {shape : List (Nat × Nat)} {tail : Nat}
    (out : unpack pat = some (shape,tail)) : pat = template shape tail := by
  cases pat with
  | «var» n =>
    have same := Option.some.inj out
    cases same
    rfl
  | record label field rest =>
    cases field <;> try cases out
    rename_i n
    cases built : unpack rest with
    | none =>
      simp [unpack,built] at out
    | some pair =>
      obtain ⟨fields,last⟩ := pair
      have same : ((label,n)::fields,last) = (shape,tail) := by
        change ((unpack rest).map _) = some (shape,tail) at out
        rw [built] at out
        exact Option.some.inj out
      cases same
      exact congrArg (fun e => Pattern.record label (.var n) e) (unpack_exact built)
  | app _ _ | variant _ _ | join _ _ => cases out
termination_by sizeOf pat

structure Checked {s : State} {m : Manifest} (a : Attached s m) (arg : Capture) (pat : Pattern) where
  shape : List (Nat × Nat)
  tail : Nat
  pattern : normalize pat = template shape tail
  source : GeneralDeclarativeWitnessRecord349.Checked a arg (shape.map Prod.fst)
  jobs : Jobs
  generated : ready arg shape tail source.lower source.upper source.displayedLower source.displayedUpper
    source.lowerEnd source.upperEnd = some jobs

/-- Jobs come from the actual normalized declaration pattern; a
certificate supplies only its reads, not keys, binders or field order. -/
def decode {s : State} {m : Manifest} (a : Attached s m) (arg : Capture) (pat : Pattern)
    (wire : Wire) : Option (Checked a arg pat) :=
  match shape : unpack (normalize pat) with
  | some (first::rest,tail) => do
    let fields := first::rest
    let source ← GeneralDeclarativeWitnessRecord349.decode a arg (fields.map Prod.fst) wire
    match computed : ready arg fields tail source.lower source.upper source.displayedLower source.displayedUpper
      source.lowerEnd source.upperEnd with
    | none => none
    | some jobs => pure ⟨fields,tail,unpack_exact shape,source,jobs,computed⟩
  | _ => none

theorem ordered {s : State} {m : Manifest} {a : Attached s m} {arg : Capture} {pat : Pattern}
    (out : Checked a arg pat) : out.jobs.map Prod.fst = (normalize pat).variables := by
  rw [out.pattern]
  exact (GeneralDeclarativeEndpointProgram336.list_sound out.source.fact out.generated).1

/-- Semantic projections are exact in the checked input model.
This does not allocate extra names, install I-58 ties, or derive a
new model extension on the user's behalf. -/
theorem replay_same_model {s : State} {m : Manifest} {a : Attached s m} {arg : Capture} {pat : Pattern}
    (out : Checked a arg pat) (model : Assignment) (fit : Models s model) :
    ∀ job ∈ out.jobs, ∃ t : Triple,
      GeneralDeclarativeExactOverlay337.eval job.2 model = some t ∧ InInterval t.1 t.2.2 t.2.1 :=
  GeneralDeclarativeExactOverlay337.list_sound out.source.fact out.generated model fit

end Yulang.GeneralDeclarativeWitnessProjection349
