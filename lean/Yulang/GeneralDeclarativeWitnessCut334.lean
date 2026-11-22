import Yulang.GeneralDeclarativeWitnessCutRank334

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCut334
open GeneralDeclarativeWitnessCutDecl334
open GeneralDeclarativeWitnessCutBody334
open GeneralDeclarativeWitnessCutRank334 (at_center no_present_center safe)
open GeneralDeclarativeWitnessHead334 (CurrentArgument)
open GeneralDeclarativeWitnessClassify334 (Rule selected_center_reads)
open GeneralDeclarativeWitnessCorrespond334 (Legacy Realized old_to_selected)
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralDeclarativeHead320 (Equation Models)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl Ready)
open GeneralDeclarativeGrowth327 (Extends fits)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeTrace321 (Trace Occurrence)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeInlineSpine331 (Closed)
open GeneralDeclarativeRecordSpine330 (Spine)
open GeneralDeclarativeArityPlan330 (Plan Reads)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativeStableAttempt329 (Elected independent_election)
open GeneralDeclarativeCurrentReceipt330 (literal Staged)
open GeneralDeclarations (Declaration)
open GeneralDeclarationExamples (constructors)
open CommonRoleOutermostResolver (All₂ Classify Dictionary)

theorem no_alias_rhs
    (linked : Alias (restriction support) 1 owner)
    (stored : (⟨owner,rhs⟩ : Equation) ∈ (restriction support).equations) : False := by
  cases at_center linked
  exact no_present_center stored

theorem no_named (held : Trace (restriction support) .actual 1 wanted seen) : False := by
  cases held with
  | record linked stored _ _ => exact no_alias_rhs linked stored

theorem no_spine (held : Spine (restriction support) 1 fields tail) : False := by
  cases held with
  | width link e | exactEnd link e => exact no_alias_rhs link e
  | cons link e _ => exact no_alias_rhs link e
  | inline link _ e => exact no_alias_rhs link e
  | prefixed link e _ => exact no_alias_rhs link e

theorem no_inline_known {code : GeneralNominalCenteredHeadMatExpressions.Expr}
    (notBinder : ∀ n, code ≠ .variable n)
    (held : Read (restriction support) .actual (.variable 1) code used) : False := by
  cases held with
  | capture => exact notBinder _ rfl
  | expose _ link e _ => exact no_alias_rhs link e
  | record source _ _ _ _ _ _ =>
    cases source with
    | name known => exact no_spine known
    | terminal ending => cases ending

theorem no_inline (held : Read (restriction support) .actual (.variable 1) wanted used) : False :=
  no_inline_known (by intro n impossible; cases impossible) held

theorem no_projected (plan : Plan) (same : plan.code = wanted) : False := by
  cases plan <;> cases same

theorem no_current : ¬CurrentArgument support constructors interpretation arg pat := by
  rintro ⟨_,held⟩
  rcases held with ⟨_,_,printed,seen⟩|⟨_,_,printed,seen⟩|⟨plan,printed,_⟩
  · cases Option.some.inj (normal.symm.trans printed)
    exact no_named seen
  · cases Option.some.inj (normal.symm.trans printed)
    exact no_inline seen
  · exact no_projected plan (Option.some.inj (printed.symm.trans normal))

def waiting (_ : Demand) (_ : Declaration) : Prop := False

theorem unchanged_bounds : Bounds final arg :=
  fits (GeneralDeclarativeGrowth327.trans (GeneralDeclarativeGrowth327.facts _ _)
    (GeneralDeclarativeGrowth327.trans folded.preserve.grows (GeneralDeclarativeGrowth327.facts _ _))) bounds

theorem lower_known : Ready support root := by
  intro cap existsAt
  cases List.mem_singleton.mp existsAt
  exact ⟨_,lo,exact_supported.mpr List.mem_cons_self,alias_refl _,rfl⟩

theorem head_endpoints : HeadMatches (restriction support) constructors interpretation root impl := by
  refine .cons ⟨unchanged_bounds,wanted,[⟨0,.lower,3⟩,⟨1,.lower,4⟩],[⟨0,.upper,3⟩,⟨1,.upper,4⟩],normal,?_,?_⟩ .nil
  · exact .record (alias_refl _) (exact_supported.mpr List.mem_cons_self) .capture .capture
  · exact .record (alias_refl _) (exact_supported.mpr (List.mem_cons_of_mem _ List.mem_cons_self)) .capture .capture

theorem old_elected :
    Elected final registry interpretation support (candidates support registry interpretation waiting) root impl := by
  refine ⟨lower_known,safe _,fun ⟨_,_,no⟩ => no,⟨⟨List.mem_cons_self,rfl⟩,.inl head_endpoints⟩,?_⟩
  intro other allowed
  cases List.mem_singleton.mp allowed.1.1
  rfl

theorem old_stage : Staged final registry interpretation root impl [] :=
  ⟨final,built,literal (GeneralDeclarativeClauseBatch327.reflexive _)⟩

theorem actual_old : Legacy support registry interpretation waiting root (.selected impl.id []) :=
  .prior (independent_election old_elected old_stage)

theorem no_arguments : ¬All₂ (CurrentArgument support constructors interpretation) root.arguments impl.head := by
  intro ready
  cases ready with
  | cons opened _ => exact no_current opened

theorem actual_wait : Rule support registry interpretation waiting root .pending :=
  .unread old_elected no_arguments

theorem no_new_selected {key kids} :
    ¬Rule support registry interpretation waiting root (.selected key kids) := by
  intro chosen
  obtain ⟨d,_,known,heads⟩ :
      ∃ d : Declaration, d.id = key ∧ d ∈ registry.declarations ∧
        All₂ (CurrentArgument support constructors interpretation) root.arguments d.head := by
    obtain ⟨d,id,⟨w⟩⟩ := GeneralDeclarativeWitnessClassify334.selected_witness chosen
    exact ⟨d,id,w.chosen.viable.1.1,GeneralDeclarativeWitnessHead334.current_heads w.slice w.source⟩
  cases List.mem_singleton.mp known
  exact no_arguments heads

/-- Actual separating declarative state. The old branch uses a real
checked compiler frame, not a synthetic arbitrary generates relation.
The new branch cannot source the center from an unfinished output,
although the independently sourced endpoints still match. -/
theorem separating_state :
    (∃ m, Models final m) ∧ Legacy support registry interpretation waiting root (.selected impl.id []) ∧
      Rule support registry interpretation waiting root .pending ∧
      ∀ key kids, ¬Rule support registry interpretation waiting root (.selected key kids) :=
  ⟨has_model,actual_old,actual_wait,fun _ _ => no_new_selected⟩

theorem not_every_old_readback : ¬Realized support registry interpretation waiting :=
  fun realizes => no_new_selected (old_to_selected realizes declared actual_old)

theorem old_tree :
    Classify (Legacy support registry interpretation waiting) root (.selected (.node impl.id [])) :=
  ⟨.selected impl.id [],.selected actual_old .nil,.selected .nil (.selected rfl)⟩

theorem new_waiting_tree : Classify (Rule support registry interpretation waiting) root .pending :=
  ⟨.pending,.pending actual_wait,.pending⟩

theorem no_new_dictionary (dict : Dictionary) :
    ¬Classify (Rule support registry interpretation waiting) root (.selected dict) := by
  rintro ⟨diag,resolves,summaries⟩
  cases resolves with
  | pending _ => cases summaries
  | rejected _ => cases summaries
  | ambiguous _ => cases summaries
  | selected choice _ => exact no_new_selected choice

end Yulang.GeneralDeclarativeWitnessCut334
