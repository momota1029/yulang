import Yulang.GeneralDeclarativeI65Obligations365

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open CommonRecursiveNominalIntervals
  (Endpoint Argument ResultHolds ContextObligation inspectContextObligation inspectContext
   decomposeContextArguments decompose_context_arguments_size_lt
   inspect_context_nominal concatenate_exact result_some result_none compileInContext admitContext admit_context_exact)
open CommonDeclaredNominalInspection (Registry)
open GeneralDeclarativeWitnessSparseIntervals357 (Compiled)
open GeneralDeclarativeWitnessFullIntervals357 (compiled_full_exact)
open GeneralNominalCommonBridge (Assignment)
open PresenceNormalForm (Atom)

def Listed (s : GeneralDeclarativeHead320.State) (atom : Atom Nat) : Prop :=
  atom ∈ s.normal.ordinary

section
local instance (priority := high) : SizeOf Nat := @instSizeOfDefault Nat
local instance (priority := high) : WellFoundedRelation Nat := Nat.lt_wfRel

theorem compare_of_existing_inspection (s : GeneralDeclarativeHead320.State) (table : Registry)
    (context : Bool) (first last : Endpoint Nat)
    (facts : ResultHolds (Listed s) (inspectContext table context first last)) :
    Nonempty (Compare s table context first last) := by
  cases first with
  | ordinary a =>
    cases last with
    | ordinary b =>
      rw [inspectContext,result_some] at facts
      exact ⟨.ordinary (facts _ List.mem_cons_self)⟩
    | nominal k args =>
      rw [inspectContext] at facts <;> simp_all
  | nominal name before =>
    cases last with
    | ordinary b =>
      rw [inspectContext] at facts <;> simp_all
    | nominal other after =>
      by_cases same : name = other
      · subst other
        cases declared : table[name]? with
        | none =>
          rw [inspectContext] at facts
          simp [declared] at facts
        | some row =>
          cases generated : decomposeContextArguments context row before after with
          | none =>
            have absent : inspectContext table context (.nominal name before) (.nominal name after) = none := by
              rw [inspectContext]
              simp only [↓reduceIte,declared]
              split <;> simp_all
            rw [absent] at facts
            exact False.elim (result_none _ facts)
          | some obligations =>
            rw [inspect_context_nominal table context name before after row obligations declared generated,
              concatenate_exact] at facts
            simp only [List.forall_mem_map] at facts
            have all : ResultHolds (ContextNeed s table)
                (decomposeContextArguments context row before after) := by
              rw [generated,result_some]
              intro item present
              have leaf := facts item present
              rcases item with ⟨ctx,obligation⟩
              cases obligation with
              | row a b =>
                exact (result_some ..).mp leaf _ List.mem_cons_self
              | value a b =>
                have _smaller := decompose_context_arguments_size_lt context row before after
                  obligations generated ctx a b present
                exact compare_of_existing_inspection s table ctx a b leaf
            obtain ⟨args⟩ := context_arguments_of_needs row before after all
            exact ⟨.nominal declared args⟩
      · rw [inspectContext] at facts
        simp [same] at facts
termination_by max (sizeOf first) (sizeOf last)
decreasing_by
  all_goals subst_vars
  have actual := decompose_context_arguments_size_lt context row before after
    obligations generated ctx a b present
  apply Nat.lt_of_lt_of_le actual
  simp only [Endpoint.nominal.sizeOf_spec]
  omega

end

/-- Feed the old exact exporter into the new declarative proof. The
input is a trace from the existing comparison plus membership in this
very state, not a Boolean assertion supplied by the witness. -/
theorem reflects_existing_compiler {e s table context lo hi} (c : Compiled e table context lo hi)
    (present : ∀ a ∈ c.rows, a ∈ s.normal.ordinary) :
    Nonempty (DeclaredComparison e s table context lo hi) := by
  have actual : ResultHolds (Listed s) (compileInContext table context lo hi) := ⟨c.rows,c.exact,present⟩
  unfold compileInContext at actual
  by_cases admitted : (admitContext table context lo && admitContext table context hi) = true
  · simp only [admitted,ite_true] at actual
    obtain ⟨left,right⟩ := Bool.and_eq_true_iff.mp admitted
    obtain ⟨read⟩ := compare_of_existing_inspection s table context lo hi actual
    exact ⟨⟨c.authority,(admit_context_exact ..).mp left,(admit_context_exact ..).mp right,read⟩⟩
  · simp only [admitted,Bool.false_eq_true,ite_false] at actual
    exact False.elim (result_none _ actual)

end Yulang.GeneralDeclarativeI65
