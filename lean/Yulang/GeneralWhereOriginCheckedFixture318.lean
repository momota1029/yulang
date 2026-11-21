import Yulang.GeneralWhereOriginAssemble318
import Yulang.GeneralWhereOriginCheckedLayout318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 14000000
namespace Yulang.GeneralWhereOriginCheckedFixture318
open GeneralLiveCompoundRegistry316 (sourceRegistry otherChild registry boundary_checked)
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralWhereVersionRootReport317 (plan)
open GeneralWhereOriginFixture318 (lowerCurrent upperCurrent)
open GeneralWhereVersionSnapshot317 (snap)
open GeneralWhereVersionBase317 (loSlot hiSlot)
open GeneralWhereVersionCase317 (expr)
open GeneralWhereVersionInstall317 (fixed Models)
open GeneralWhereOriginTrace318 (rawOf)
open GeneralWhereOriginDelta318 (Cell)
open GeneralWhereOriginPartition318 (allClassified existing_iff classified_iff)
open GeneralWhereOriginAssemble318 (guard ActualRows modeled_preinstall)
open GeneralWhereOriginReady318 (HeadReady)
open GeneralWhereOriginSupport318 (journalSources)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalVersionedPlans231 (variables)
open GeneralWhereVersionCompiler317 (schema)
open GeneralNominalCommonBridge (Assignment)

theorem only_current (c : Cell plan) : c = lowerCurrent ∨ c = upperCurrent := by
  rcases c with ⟨clause,index,side,pattern,expression,listed,hit,good,compiled⟩
  have named : clause = otherChild := List.mem_singleton.mp listed
  subst clause
  have inRange := (List.getElem?_eq_some_iff.mp hit).1
  have i : index = 0 := by
    change index < 1 at inRange
    omega
  subst index
  have atPos : otherChild.arguments[0]? = some (.variant 0 (.var 0)) := rfl
  have exactPat := Option.some.inj (hit.symm.trans atPos)
  subst pattern
  have known : GeneralNominalCenteredHeadMatExpressions.translate plan.packet.registry.constructors
    plan.packet.context.interpretation (.variant 0 (.var 0)) = some expr := rfl
  have exactExpr := Option.some.inj (compiled.symm.trans known)
  subst expression
  cases side
  · exact .inl rfl
  · exact .inr rfl

theorem full_classification : allClassified fixed plan (guard fixed plan) = true := by
  apply (classified_iff fixed plan _).mpr
  intro c
  apply List.mem_append_left
  apply (existing_iff fixed c).mpr
  rcases only_current c with rfl|rfl
  · exact ⟨loSlot,GeneralWhereVersionReuse317.exact_slots.1⟩
  · exact ⟨hiSlot,GeneralWhereVersionReuse317.exact_slots.2⟩

theorem rechecked (m : Assignment) (valid : Models fixed m) :
    ∃ n, Models fixed n ∧ HeadReady fixed plan n ∧ Agree (journalSources fixed ++ guard fixed plan) m n ∧
      (schema plan).unknown = false ∧ (schema plan).Holds (variables plan n) n := by
  have parent := (GeneralWhereVersionJournal317.fixed_iff m).mp valid
  have current := GeneralWhereVersionCurrentCert317.current_certified m valid
  apply modeled_preinstall boundary_checked GeneralWhereOriginCheckedLayout318.enumerated_trace
    (focus := root) (key := GeneralLiveCompoundRegistry316.declaration.id) (p := plan) ?_
    full_classification ?_ m valid ?_ (fun row whereAt _ => current.2.1.rows row whereAt)
  · rw [GeneralWhereVersionInstall317.mixed_eq]
    exact current.1
  · exact GeneralLiveCompoundRegistry316.coverage.1 _ List.mem_cons_self
  · refine ⟨current.2.1.head,current.2.1.input,current.2.1.captures,current.2.1.headSchema,?_⟩
    rw [GeneralWhereVersionInstall317.mixed_eq]
    exact GeneralWhereVersionRootRegistry317.classes m parent

end Yulang.GeneralWhereOriginCheckedFixture318
