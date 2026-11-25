import Yulang.GeneralDeclarativeI65I74X6AmbiguousVisits417

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.X6Ambiguous417
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open PlainMerged416 (PlainRows)
open CommonRoleOutermostResolver (All₂ Dictionary Summarizes Result)

structure Ambiguous (s : I72.State) (q : I72.Request) where
  rows : PlainRows s q
  plain : PlainHit rows
  ground : GroundHit rows
  ordered : visible s.core q = [plain.candidate.decl,ground.candidate.decl] ∨
    visible s.core q = [ground.candidate.decl,plain.candidate.decl]
  distinct : plain.candidate.decl.id ≠ ground.candidate.decl.id
  visits : Visits rows

theorem actual_matching_candidates_are_exactly_two417 {s q} (a : Ambiguous s q) :
    ∀ d, d ∈ visible s.core q ↔ d = a.plain.candidate.decl ∨ d = a.ground.candidate.decl := by
  intro d
  rcases a.ordered with h|h <;> rw [h] <;> simp [or_comm]

theorem same_input_has_distinct_authored_ordinals417 {s q} (a : Ambiguous s q) :
    a.plain.candidate.ordinal ≠ a.ground.candidate.ordinal := by
  intro same
  have address := a.plain.candidate.authored
  rw [same,a.ground.candidate.authored] at address
  exact a.distinct (congrArg Declaration.id (Option.some.inj address).symm)

/-- The new *declarative* rule contains two independently derived actual
matching heads for two real visible declarations on one request.  There
is no model, checker result, guessed capture, or supplied verdict in it. -/
def ambiguityLocal417 : SourcePrimitives where
  elected := fun _ _ _ _ => False
  other := fun s q verdict needs =>
    verdict = .ambiguous ∧ needs = [] ∧ Nonempty (Ambiguous s q)

def R9 : SourcePrimitives where
  elected := PlainMerged416.R8.elected
  other := fun s q verdict needs =>
    PlainMerged416.R8.other s q verdict needs ∨ ambiguityLocal417.other s q verdict needs

theorem no_election_rule_was_changed417 {s q event needs} :
    R9.elected s q event needs ↔ PlainMerged416.R8.elected s q event needs := Iff.rfl

theorem selected_trace_is_dictionary_sound417 {s q t e} (trace : SourceTrace R9 s q t e)
    (m : I72.Model) (fit : Fits s m) :
    ∀ d, Summarizes t (.selected d) → DictionaryEvidence s m q d := by
  exact SourceTrace.rec (R := R9) (s := s)
    (motive_1 := fun q t _ _ => ∀ d, Summarizes t (.selected d) → DictionaryEvidence s m q d)
    (motive_2 := fun qs ts _ => ∀ ds, All₂ Summarizes ts (ds.map Result.selected) →
      DictionaryEvidenceForest s m qs ds)
    (motive_3 := fun _ _ => True)
    (fun _ _ evidence => by cases evidence)
    (fun v _ _ _ _ _ evidence => by cases v <;> cases evidence)
    (fun event _ decision _ _ _ proveKids d actual => by
      have semantics := PlainMerged416.selected_plain_local_sound416 decision m fit
      cases actual with
      | selected ordered combine =>
        cases combine with
        | selected exactEach =>
          rw [exactEach] at ordered
          exact .node event semantics.1 semantics.2 (proveKids _ ordered))
    (fun ds pair => by
      cases ds with
      | nil => exact .nil
      | cons => cases pair)
    (fun _ _ first rest ds ordered => by
      cases ds with
      | nil => cases ordered
      | cons d ds =>
        cases ordered with
        | cons head tail => exact .cons (first d head) (rest ds tail))
    True.intro (fun _ _ _ _ _ _ => True.intro) trace

theorem dictionary_sound_R9 : DictionarySound R9 := by
  rintro s q d ⟨t,e,⟨trace⟩,result⟩ m fit
  exact selected_trace_is_dictionary_sound417 trace m fit d result

end Yulang.GeneralDeclarativeI65.I72.X6Ambiguous417
