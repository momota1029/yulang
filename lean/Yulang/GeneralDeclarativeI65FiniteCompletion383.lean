import Yulang.GeneralDeclarativeI65State365
import Yulang.CommonRoleOutermostResolver

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (All₂ Frontier Tree Dictionary Result Resolves Summarizes)

/-- Positive selected source-rule interface. The first list names
producers of observations; the second names literal where demands.
Instantiating the actual candidate verdict (including all rival and
K2 premises on the stable snapshot) is separate. In particular this
interface is not a rule that accepts a locally favorable prefix. -/
abbrev SelectedSourceRule383 :=
  State → Request → List Request → Nat → List Request → Prop

mutual
/-- Finite constructive completion in one fixed declarative state.
Each producer needed for a read, and each ordered where request,
has its own genuine selected subderivation. No solver datum occurs. -/
inductive SelectedSourceProof383 (source : SelectedSourceRule383) (s : State) :
    Request → Dictionary → Type where
  | selected (rule : source s q deps key kids) :
      SelectedSourceForest383 source s deps supportDicts →
      SelectedSourceForest383 source s kids whereDicts →
      SelectedSourceProof383 source s q (.node key whereDicts)

inductive SelectedSourceForest383 (source : SelectedSourceRule383) (s : State) :
    List Request → List Dictionary → Type where
  | nil : SelectedSourceForest383 source s [] []
  | cons : SelectedSourceProof383 source s q d → SelectedSourceForest383 source s qs ds →
      SelectedSourceForest383 source s (q::qs) (d::ds)
end

/-- I-67: completion is a finite selected derivation in the *same*
state, not a bit supplied by a solver. This definition lives at the
positive proof interface, before the actual local source rules are
instantiated. -/
def FiniteCompleted383 (source : SelectedSourceRule383) (s : State) (q : Request) : Prop :=
  ∃ d, Nonempty (SelectedSourceProof383 source s q d)

theorem finite_forest_completes_members383
    {source : SelectedSourceRule383} {s : State} {qs : List Request} {ds : List Dictionary}
    (proofs : SelectedSourceForest383 source s qs ds) :
    ∀ q ∈ qs, FiniteCompleted383 source s q := by
  exact SelectedSourceForest383.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun qs _ _ => ∀ q ∈ qs, FiniteCompleted383 source s q)
    (fun _ _ _ _ _ => True.intro)
    (fun _ no => by cases no)
    (fun proof _ _ ih q hit => by
      rcases List.mem_cons.mp hit with rfl|tail
      · exact ⟨_,⟨proof⟩⟩
      · exact ih q tail)
    proofs

/-- If every selected rule for a member of a family needs a member
of that same family (either as a producer read or as a where demand),
that family has no finite proof. A syntactic cycle with a genuine
alternative outside the family is not rejected by this statement. -/
theorem no_finite_circular_completion383 {source : SelectedSourceRule383} {s : State}
    (closed : Request → Prop)
    (needsInside : ∀ q deps key kids, source s q deps key kids → closed q →
      (∃ p ∈ deps,closed p) ∨ (∃ k ∈ kids,closed k))
    {q : Request} {d : Dictionary} (p : SelectedSourceProof383 source s q d) :
    ¬closed q := by
  exact SelectedSourceProof383.rec
    (motive_1 := fun q _ _ => ¬closed q)
    (motive_2 := fun qs _ _ => ∀ q ∈ qs, ¬closed q)
    (fun localStep _ _ fromRead fromWhere bad => by
      rcases needsInside _ _ _ _ localStep bad with ⟨dep,seen,c⟩|⟨kid,seen,c⟩
      · exact fromRead dep seen c
      · exact fromWhere kid seen c)
    (fun _ no => by cases no)
    (fun _ _ once later q seen => by
      rcases List.mem_cons.mp seen with rfl|tail
      · exact once
      · exact later q tail)
    p

theorem closed_family_has_no_completed_member383
    {source : SelectedSourceRule383} {s : State}
    (closed : Request → Prop)
    (needsInside : ∀ q deps key kids, source s q deps key kids → closed q →
      (∃ p ∈ deps,closed p) ∨ (∃ k ∈ kids,closed k))
    {q : Request} (belongs : closed q) :
    ¬FiniteCompleted383 source s q := by
  rintro ⟨_,⟨proof⟩⟩
  exact no_finite_circular_completion383 closed needsInside proof belongs

/-- Projection only of the positive fragment. The other outcomes
are deliberately not assigned rules here. Do not substitute this for
the full actual Classifies verdict. -/
def SupportedSelectedFrontier383 (source : SelectedSourceRule383) (s : State)
    (q : Request) : Frontier Request → Prop
  | .selected key kids =>
      ∃ deps, source s q deps key kids ∧ ∀ p ∈ deps, FiniteCompleted383 source s p
  | _ => False

/-- Where children, and only those children, form the ordered
diagnostic tree and dictionary. Proofs for output-read dependencies
are kept separately and do not become dictionary entries. -/
theorem selected_proof_projects_literal_where383
    {source : SelectedSourceRule383} {s : State}
    {q : Request} {d : Dictionary} (p : SelectedSourceProof383 source s q d) :
    ∃ t : Tree, Resolves (SupportedSelectedFrontier383 source s) q t ∧
      Summarizes t (.selected d) := by
  exact SelectedSourceProof383.rec
    (motive_1 := fun q d _ => ∃ t : Tree,
      Resolves (SupportedSelectedFrontier383 source s) q t ∧ Summarizes t (.selected d))
    (motive_2 := fun qs ds _ => ∃ ts : List Tree,
      All₂ (Resolves (SupportedSelectedFrontier383 source s)) qs ts ∧
        All₂ Summarizes ts (ds.map Result.selected))
    (fun step supporters _ _ after => by
      obtain ⟨trees,resolved,results⟩ := after
      exact ⟨.selected _ trees,.selected ⟨_,step,finite_forest_completes_members383 supporters⟩ resolved,
        .selected results (.selected rfl)⟩)
    ⟨[],.nil,.nil⟩
    (fun _ _ first later => by
      obtain ⟨t,proved,summary⟩ := first
      obtain ⟨ts,provedRest,summaries⟩ := later
      exact ⟨t::ts,.cons proved provedRest,.cons summary summaries⟩)
    p

end Yulang.GeneralDeclarativeI65
