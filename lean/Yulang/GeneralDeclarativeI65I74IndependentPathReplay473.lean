import Yulang.GeneralDeclarativeI65I74FiniteCheckedObservation473

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473
open GeneralDeclarationPatterns (Pattern)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open ObservationAlternatives473 (Place Positions oldPosition graphOf readAlternatives)
open WrittenPattern460.PhysicalOrigin (Pose)
open QuotientObservation471 (ReturnsUpToEquality)

inductive IndependentPath (s : OwnState) (positions : Positions n)
    (rel : List (Fin n × Fin n)) : Fin n → Pattern → Expr → Expr →
      List StepWire → List Pose → Fin n → Bool → Prop where
  | terminal :
      GuardedObservationInput s positions rel here →
      (bit = true ↔ ReturnsUpToEquality (graphOf s positions) here) →
      IndependentPath s positions rel here p query raw [] [] here bit
  | branch (move : StepWire) (origin : ReadStep s move p query raw) :
      GuardedObservationInput s positions rel here →
      ¬ReturnsUpToEquality (graphOf s positions) here →
      appendToInline (oldPosition positions here) (childSlot move.action) origin.actualRawChild =
        some (oldPosition positions next) →
      IndependentPath s positions rel next origin.writtenChild origin.childQuery origin.actualRawChild
        tail suffix final bit →
      IndependentPath s positions rel here p query raw (move :: tail) (move.written ++ suffix) final bit

theorem independent_path_has_finite_replay_at_its_exact_terminal
    {s : OwnState} {positions : Positions n} {rel : List (Fin n × Fin n)}
    {here p query raw steps suffix final bit}
    (original : IndependentPath s positions rel here p query raw steps suffix final bit) :
    ∃ (wire : PathWire n) (reported : TypedPathResult s positions (oldPosition positions here) p query raw wire),
      wire.here.which = here ∧ wire.rest.map Prod.fst = steps ∧
      readLiteralPath s positions rel (oldPosition positions here) p query raw wire = some reported ∧
      reported.suffix = suffix ∧ reported.final = final ∧ reported.bit = bit := by
  induction original with
  | terminal auth adequate =>
    obtain ⟨c,site,ran⟩ := independent_checkpoint_reifies_the_exact_site_and_sign auth _ adequate
    refine ⟨⟨c,[]⟩,⟨[],_,_,.stop ?_ ?_⟩,site,rfl,?_,rfl,site,rfl⟩
    · rw [site]
    · simpa [site] using adequate
    · rw [readLiteralPath]
      split
      · rename_i no; rw [ran] at no; cases no
      · rename_i b yes
        have eq := Option.some.inj (yes.symm.trans ran)
        subst b
        rfl
  | branch move origin auth safe atNext follows ih =>
    rename_i p₁ q₁ raw₁ here₁ next₁ tail₁ suffix₁ final₁ bit₁
    have sign : false = true ↔ ReturnsUpToEquality (graphOf s positions) here₁ := by
      simp [safe]
    obtain ⟨c,hereSite,ran⟩ := independent_checkpoint_reifies_the_exact_site_and_sign auth false sign
    obtain ⟨next,report,nextSite,moves,replay,address,terminal,output⟩ := ih
    rcases next with ⟨nextCheck,tail⟩
    refine ⟨⟨c,(move,nextCheck)::tail⟩,⟨move.written ++ report.suffix,report.final,report.bit,?_⟩,
      hereSite,by simp [moves],?_,congrArg (fun l => move.written ++ l) address,terminal,output⟩
    · refine .step origin ?_ ?_ atNext report.visits
      · rw [hereSite]
      · simpa [hereSite] using safe
    · simp only [readLiteralPath,independent_step_derivation_replays_its_original_addresses origin,
        bind,Option.bind]
      split
      · split
        · rename_i missing; rw [atNext] at missing; cases missing
        · rename_i chosen found
          have eq := Option.some.inj (found.symm.trans atNext)
          subst chosen
          rw [replay]
          rfl
      · rename_i failed
        exact (failed ran).elim

end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473
