import Yulang.CommonRoleIntervalCapture
import Yulang.CommonRoleIntervalGeneration

/-!
Repeated captures from the existing finite structural capture, compiled to
ordinary shared-slot checks. This does not extend the candidate scanner:
its `supported` check still excludes repeated variables and join heads.
-/
namespace Yulang.CommonRoleRepeatedCaptureChecks

open CommonRoleCaptureNormalization (Form)
open CommonRoleIntervalCapture (Bindings)
open Core.PresenceGeneration (TyTerm Comp)
open PresenceNormalForm (Atom All)

def term : Form → TyTerm Nat
  | .var name => .var name
  | .int => .base .int
  | .pair first last => .pair (term first) (term last)
  | .join first last => .union (term first) (term last)
  | .tick payload => .variant 0 (term payload)

/-- Endpoint lowering retains the meaning of each original captured form. -/
theorem term_eval (assignment : Nat → Comp Common.model) (form : Form) :
    (term form).eval Common.model assignment = form.eval (fun name => (assignment name).1) := by
  induction form <;> simp_all [term, TyTerm.eval, Form.eval, Common.model]

def intervals (bindings : Bindings) (name : Nat) : List (CommonRoleIntervalGeneration.Argument Nat) :=
  bindings.filterMap fun (key, bounds) =>
    if key = name then some (term bounds.1, term bounds.2) else none

def names (bindings : Bindings) : List Nat := (bindings.map Prod.fst).eraseDups

def merged (bindings : Bindings) (name : Nat) : CommonRoleIntervalGeneration.Argument Nat :=
  let occurrences := intervals bindings name
  (occurrences.foldr (fun bounds rest => .union bounds.1 rest) .bottom,
   occurrences.foldr (fun bounds rest => .inter bounds.2 rest) .top)

theorem merged_eval (bindings : Bindings) (name : Nat) (assignment : Nat → Comp Common.model) :
    CommonRoleIntervals.evaluate (CommonRoleIntervalGeneration.eval assignment) (merged bindings name) =
      CommonRoleIntervalGeneration.meaning assignment (intervals bindings name) := by
  unfold merged CommonRoleIntervalGeneration.meaning CommonRoleIntervals.coalesce
  induction intervals bindings name with
  | nil => rfl
  | cons bounds rest ih =>
      simp only [List.foldr_cons, CommonRoleIntervals.evaluate, CommonRoleIntervalGeneration.eval,
        TyTerm.eval, Common.model, List.map_cons, CommonBoundCoalescing.joinTypes,
        CommonBoundCoalescing.meetTypes, Prod.mk.injEq] at *
      exact ⟨congrArg _ ih.1, congrArg _ ih.2⟩

theorem merged_valid_iff (bindings : Bindings) (name : Nat) (assignment : Nat → Comp Common.model) :
    CommonRoleIntervals.Valid
        (CommonRoleIntervals.evaluate (CommonRoleIntervalGeneration.eval assignment) (merged bindings name)) ↔
      All Common.model assignment (CommonRoleIntervalGeneration.generate (intervals bindings name)) := by
  rw [merged_eval, CommonRoleIntervalGeneration.generate_exact]

/-- Retain all old and cross checks for every captured variable. -/
def generate (bindings : Bindings) : List (Atom Nat) :=
  (names bindings).flatMap fun name => CommonRoleIntervalGeneration.generate (intervals bindings name)

/-- The output holds exactly when every pair of occurrences of the same
captured name has a compatible lower and upper endpoint. -/
theorem generate_exact (bindings : Bindings) (assignment : Nat → Comp Common.model) :
    All Common.model assignment (generate bindings) ↔
      ∀ name ∈ names bindings, ∀ first ∈ intervals bindings name,
        ∀ last ∈ intervals bindings name,
          Common.Subtype (first.1.eval Common.model assignment) (last.2.eval Common.model assignment) := by
  constructor
  · intro checks name named first present last included
    have model : All Common.model assignment (CommonRoleIntervalGeneration.generate (intervals bindings name)) :=
      fun atom member => checks atom (List.mem_flatMap.mpr ⟨name, named, member⟩)
    have valid := (CommonRoleIntervalGeneration.generate_exact assignment _).mp model
    have pairwise := (CommonRoleIntervals.valid_coalesce _).mp valid
    exact pairwise (CommonRoleIntervals.evaluate (CommonRoleIntervalGeneration.eval assignment) first)
      (List.mem_map.mpr ⟨first, present, rfl⟩)
      (CommonRoleIntervals.evaluate (CommonRoleIntervalGeneration.eval assignment) last)
      (List.mem_map.mpr ⟨last, included, rfl⟩)
  · intro pairs atom member
    obtain ⟨name, named, member⟩ := List.mem_flatMap.mp member
    have valid : CommonRoleIntervals.Valid (CommonRoleIntervalGeneration.meaning assignment (intervals bindings name)) := by
      apply (CommonRoleIntervals.valid_coalesce _).mpr
      intro first present last included
      obtain ⟨firstOriginal, firstMember, rfl⟩ := List.mem_map.mp present
      obtain ⟨lastOriginal, lastMember, rfl⟩ := List.mem_map.mp included
      exact pairs name named firstOriginal firstMember lastOriginal lastMember
    exact (CommonRoleIntervalGeneration.generate_exact assignment _).mpr valid atom member

/-- Connect the actual structural capture output to these ordinary checks. -/
def captureChecks (forms : List Form) (arguments : List CommonRoleIntervalPaterson.Argument) :
    Option (List (Atom Nat)) :=
  (CommonRoleIntervalCapture.captureArguments forms arguments).map generate

theorem capture_checks_exact (forms : List Form)
    (arguments : List CommonRoleIntervalPaterson.Argument) (atoms : List (Atom Nat)) :
    captureChecks forms arguments = some atoms ↔
      ∃ bindings, CommonRoleIntervalCapture.CaptureArguments forms arguments bindings ∧
        generate bindings = atoms := by
  simp only [captureChecks, Option.map_eq_some_iff, CommonRoleIntervalCapture.capture_arguments_exact]

/-- Two occurrences of the same head variable retain both self checks and
both cross checks, including when their endpoint pairs differ. -/
theorem repeated_example :
    captureChecks [.var 0, .var 0] [(.int, .int), (.var 1, .var 2)] =
      some [.tyLe (.base .int) (.base .int), .tyLe (.base .int) (.var 2),
        .tyLe (.var 1) (.base .int), .tyLe (.var 1) (.var 2)] := by
  rfl

end Yulang.CommonRoleRepeatedCaptureChecks
