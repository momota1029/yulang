import Yulang.GeneralDeclarativeI65Body367
import Yulang.GeneralDeclarativeI65Lowering365
import Yulang.GeneralDeclarativePriority321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativePriority321 (RootRecurs)

/-- Necessary selection facts grounded in a model-free complete
visible observation tape, with the explicit ordinary root-K2 veto.
This structure is not the generalized declarative selected rule:
preselection native/candidate recursion must also be excluded by
its own current source judgment. -/
structure TapedMatch (s : State) (q : Request)
    (tape : CandidateTape s q (visible s q)) (row : Declaration) : Prop where
  clearRoot : ¬RootRecurs s.current.ordinary q.demand
  settled : tape.waits = false
  one : tape.live = [row]

theorem root_recurrence_vetoes_tape {s : State} {q : Request}
    {tape : CandidateTape s q (visible s q)} {row : Declaration}
    (root : RootRecurs s.current.ordinary q.demand) :
    ¬TapedMatch s q tape row :=
  fun fake => fake.clearRoot root

theorem actual_matched_row {s : State} {q : Request}
    {tape : CandidateTape s q (visible s q)} {row : Declaration}
    (only : TapedMatch s q tape row) : ∃ captured : AuthoredCandidate s q row, Stores tape captured := by
  apply live_readback tape
  rw [only.one]
  exact List.mem_cons_self

theorem rival_is_excluded_by_positive_evidence {s : State} {q : Request}
    {tape : CandidateTape s q (visible s q)} {row other : Declaration}
    (only : TapedMatch s q tape row) (appears : other ∈ visible s q) (different : other ≠ row)
    (m : Model) (fit : Fits s m) :
    ¬Nonempty (SourceHead s q other) := by
  intro rival
  obtain ⟨mistake⟩ := rival
  have absent : other ∉ tape.live := by
    rw [only.one]
    simpa using different
  obtain ⟨rigid⟩ := every_nonlive_unblocked_row_is_a_real_miss only.settled appears absent
  exact rigid_candidate_excludes_a_source_head rigid mistake m fit

/-- This consumes an already identified source row and later exact
body. It neither manufactures a language verdict from the body
nor globally proves that the current source generates this receipt. -/
theorem assembled_tape_receipt {s : State} {q : Request} {tape : CandidateTape s q (visible s q)}
    {row : Declaration} {kids : List Request}
    (only : TapedMatch s q tape row)
    (readback : ∀ c : AuthoredCandidate s q row, Stores tape c →
      ∃ body : BodyFacts s q row kids, BodyLayout body c.head) :
    ∃ chosen : AuthoredCandidate s q row, Stores tape chosen ∧ Nonempty (SourceNode s q row kids) := by
  obtain ⟨chosen,pinned⟩ := actual_matched_row only
  obtain ⟨body,recipe⟩ := readback chosen pinned
  exact ⟨chosen,pinned,⟨authored_node chosen body recipe⟩⟩

end Yulang.GeneralDeclarativeI65
