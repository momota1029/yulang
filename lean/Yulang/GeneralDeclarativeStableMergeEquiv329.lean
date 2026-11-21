import Yulang.GeneralDeclarativeStableMerge329
import Yulang.GeneralDeclarativePlacementEvidence327
import Yulang.GeneralDeclarativeChildScope321
import Yulang.GeneralNominalCenteredHeadMatCompilerSemantics

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStableMergeEquiv329
open GeneralDeclarativeHead320 (State Models variables_eq)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeMerge320 (Merge equality_sound lower_exact upper_exact shared_center)
open GeneralDeclarativePlacementEquiv327 (SpanSame RequestSame)
open GeneralNominalCenteredHeadMatExpressions (Expr value values)
open GeneralDeclarativeTraceNames321 (names namesMany)
open CommonNominalFullCarrier (Equivalent subtype_refl)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm record_congr variant_congr union_congr)
open GeneralNominalCenteredHeadMatCompilerSemantics (primitive_congr nominal_congr)
open GeneralNominalMatchedAssembly (Aligned)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalMaterialization (Mode)

/-- Independently built repeated captures, with any choice of old
representative and any order of the same occurrence group, agree
in all three modes of every common ordinary model. -/
theorem aggregates {s : State} (first : Merge s a as x) (last : Merge s b bs y)
    (groups : (a::as).Perm (b::bs)) (m : Assignment) (fit : Models s m) : SpanSame m x y := by
  have lx := equality_sound first.lowerEq m fit
  have ly := equality_sound last.lowerEq m fit
  have ux := equality_sound first.upperEq m fit
  have uy := equality_sound last.upperEq m fit
  have common := groups.mem_iff.mp (show a ∈ a::as from List.mem_cons_self)
  refine ⟨?_,eqv_trans (eqv_symm ((shared_center first m fit).2 a List.mem_cons_self))
    ((shared_center last m fit).2 a common),?_⟩
  · have rs := (lower_exact m b bs (m y.lower).1).mp ly.2
    have ls := (lower_exact m a as (m x.lower).1).mp lx.2
    exact ⟨CommonNominalFullCarrier.subtype_trans lx.1 ((lower_exact m a as _).mpr
      (fun o h => rs o (groups.mem_iff.mp h))),CommonNominalFullCarrier.subtype_trans ly.1
      ((lower_exact m b bs _).mpr (fun o h => ls o (groups.mem_iff.mpr h)))⟩
  · have rs := (upper_exact m b bs (m y.upper).1).mp uy.1
    have ls := (upper_exact m a as (m x.upper).1).mp ux.1
    exact ⟨CommonNominalFullCarrier.subtype_trans ((upper_exact m b bs _).mpr
      (fun o h => ls o (groups.mem_iff.mpr h))) uy.2,CommonNominalFullCarrier.subtype_trans
      ((upper_exact m a as _).mpr (fun o h => rs o (groups.mem_iff.mp h))) ux.2⟩

mutual
theorem value_equiv (e : Expr)
    (same : ∀ md n, n ∈ names e → Equivalent (first md n) (last md n)) :
    Equivalent (value first mode e) (value last mode e) := by
  cases e with
  | «variable» n => exact same mode n List.mem_cons_self
  | primitive tag args => exact primitive_congr tag (values_equiv args same)
  | nominal tag args => exact nominal_congr tag (values_equiv (mode := .actual) args same)
  | record tag a b =>
    exact record_congr tag
      (value_equiv a (fun md n h => same md n (List.mem_append_left _ h)))
      (value_equiv b (fun md n h => same md n (List.mem_append_right _ h)))
  | variant tag a => exact variant_congr tag (value_equiv a same)
  | join a b =>
    exact union_congr (value_equiv a (fun md n h => same md n (List.mem_append_left _ h)))
      (value_equiv b (fun md n h => same md n (List.mem_append_right _ h)))
termination_by sizeOf e
theorem values_equiv (es : List Expr)
    (same : ∀ md n, n ∈ namesMany es → Equivalent (first md n) (last md n)) :
    Aligned Equivalent (values first mode es) (values last mode es) := by
  cases es with
  | nil => exact .nil
  | cons a rest =>
    exact .cons (value_equiv a (fun md n h => same md n (List.mem_append_left _ h)))
      (values_equiv rest (fun md n h => same md n (List.mem_append_right _ h)))
termination_by sizeOf es
end

open GeneralDeclarations (DeclarationChecked Clause)
open GeneralDeclarativeFrameReadback325 (ClauseFrame sourceNames)
open GeneralDeclarativeSourceEmission322 (Names useArg demand useOutput)
open GeneralDeclarativeEmissionForest322 (children Placement)
open GeneralDeclarativeClauseOrigins325 (Origin origin_reads)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (translate)
open CommonRoleOutermostResolver (All₂)

theorem mode_agrees {m : Assignment} (same : SpanSame m (baseA k) (baseB k)) (md : Mode) :
    Equivalent (variables baseA m md k) (variables baseB m md k) := by
  cases md
  · exact same.1
  · exact same.2.2
  · exact same.2.1

theorem witnesses {s : State} {m : Assignment} (fit : Models s m)
    (a : Origin s x (logical baseA md e)) (b : Origin s y (logical baseB md e))
    (same : ∀ n ∈ names e, SpanSame m (baseA n) (baseB n)) : Equivalent (m x).1 (m y).1 := by
  have ao := GeneralDeclarativeEqualities322.semantic (origin_reads a) m fit
  have bo := GeneralDeclarativeEqualities322.semantic (origin_reads b) m fit
  change Equivalent (m x).1 (value (GeneralDeclarativeHead320.environment m) .actual (logical baseA md e)) at ao
  change Equivalent (m y).1 (value (GeneralDeclarativeHead320.environment m) .actual (logical baseB md e)) at bo
  rw [logical_value] at ao bo
  exact eqv_trans ao (eqv_trans (value_equiv e (fun mode n inNames => mode_agrees (same n inNames) mode)) (eqv_symm bo))

theorem inputs_two (m : Assignment) (namesA namesB : Names) (left right : Nat → Capture)
    (offset : Nat) (patterns : List GeneralDeclarationPatterns.Pattern)
    (agrees : ∀ j p, patterns[j]? = some p →
      SpanSame m (useArg namesA (left (offset+j)) p) (useArg namesB (right (offset+j)) p)) :
    All₂ (SpanSame m) (GeneralDeclarativeSourceEmission322.inputs namesA left offset patterns)
      (GeneralDeclarativeSourceEmission322.inputs namesB right offset patterns) := by
  induction patterns generalizing offset with
  | nil => exact .nil
  | cons first rest ih =>
    refine .cons (agrees 0 first rfl) (ih (offset+1) ?_)
    intro j p here
    have fixed := agrees (j+1) p (show (first::rest)[j+1]? = some p from here)
    have shift : offset + (j+1) = offset + 1 + j := by omega
    simpa only [shift] using fixed

theorem ordered_index {r : α → β → Prop} {xs : List α} {ys : List β} (h : All₂ r xs ys) {n : Nat} (there : xs[n]? = some a) :
    ∃ b, ys[n]? = some b ∧ r a b := by
  induction h generalizing n with
  | nil => cases there
  | cons first _ last =>
    cases n with
    | zero =>
      have fixed := Option.some.inj there
      cases fixed
      exact ⟨_,rfl,first⟩
    | succ n =>
      exact last (n := n) there

theorem compares {s : State} {left right : Placement} {m : Assignment}
    (checked : DeclarationChecked r.constructors r.roles impl)
    (used : cl ∈ impl.requirements)
    (a : ClauseFrame s r i impl cl (sourceNames impl left baseA) left)
    (b : ClauseFrame s r i impl cl (sourceNames impl right baseB) right)
    (targets : left.targets = right.targets)
    (fit : Models s m) (equal : ∀ n ∈ impl.inputNames, SpanSame m (baseA n) (baseB n)) :
    RequestSame m (demand impl cl (sourceNames impl left baseA) (left.compound cl) (left.targets cl))
      (demand impl cl (sourceNames impl right baseB) (right.compound cl) (right.targets cl)) := by
  obtain ⟨cs,pa,readA⟩ := a.input
  obtain ⟨ds,pb,readB⟩ := b.input
  cases Option.some.inj (pa.symm.trans pb)
  have related (p) (found : p ∈ cl.arguments) (e) (coded : translate r.constructors i (normalize p) = some e) :
      ∀ n ∈ names e, SpanSame m ((sourceNames impl left baseA).input n) ((sourceNames impl right baseB).input n) := by
    intro n seen
    have here := GeneralDeclarativeChildScope321.translated_where_names checked used found coded seen
    unfold sourceNames
    rw [GeneralDeclarativeProducedNames325.exact_input checked here,GeneralDeclarativeProducedNames325.exact_input checked here]
    exact equal n here
  refine ⟨rfl,?_,?_⟩
  · apply inputs_two
    intro j p pos
    rw [Nat.zero_add]
    have inArgs := List.mem_of_getElem? pos
    cases kind : normalize p with
    | var n =>
      have q : n ∈ impl.inputNames :=
        GeneralDeclarativeChildScope321.translated_where_names (interp := i) checked used inArgs
          (by simp [kind,translate]) (show n ∈ names (.variable n) from List.mem_cons_self)
      simp only [useArg,kind,sourceNames,GeneralDeclarativeProducedNames325.exact_input checked q]
      exact equal n q
    | app ctor args | record ctor args _ | variant ctor args | join ctor args =>
      have compound : GeneralDeclarativeEmissionOperands322.Compound p := fun n x => by rw [kind] at x; cases x
      have zipped := GeneralDeclarativeClauseOrigins325.normalized_order pa
      obtain ⟨e,coded,compiled⟩ := ordered_index zipped pos
      obtain ⟨l0,l1,l2⟩ := readA j p e pos coded compound
      obtain ⟨h0,h1,h2⟩ := readB j p e pos coded compound
      simp only [useArg,kind]
      exact ⟨witnesses fit l0 h0 (related p inArgs e compiled),
        witnesses fit l1 h1 (related p inArgs e compiled),witnesses fit l2 h2 (related p inArgs e compiled)⟩
  · have same : GeneralDeclarativeFrameReadback325.placeById impl left =
        GeneralDeclarativeFrameReadback325.placeById impl right := by
      unfold GeneralDeclarativeFrameReadback325.placeById
      rw [targets]
    simp [demand,useOutput,GeneralDeclarationDemands.outputTarget,Names.old,sourceNames,
      GeneralDeclarativeProducedNames325.table,same,targets]

/-- Different allowed repeated capture representatives and different
compound addresses preserve all ordered where inputs in a common
model, provided the packed spans agree and targets are fixed.
Literal address checking and supported diagnostic replay remain
separate obligations. -/
theorem forest {s : State} {left right : Placement} {m : Assignment}
    (checked : DeclarationChecked r.constructors r.roles impl)
    (a : ∀ cl ∈ impl.requirements, ClauseFrame s r i impl cl (sourceNames impl left baseA) left)
    (b : ∀ cl ∈ impl.requirements, ClauseFrame s r i impl cl (sourceNames impl right baseB) right)
    (targets : left.targets = right.targets)
    (fit : Models s m) (equal : ∀ n ∈ impl.inputNames, SpanSame m (baseA n) (baseB n)) :
    All₂ (RequestSame m) (children impl (sourceNames impl left baseA) left)
      (children impl (sourceNames impl right baseB) right) := by
  unfold children
  have step (cs : List Clause) (allowed : cs ⊆ impl.requirements) :
      All₂ (RequestSame m)
        (cs.map fun cl => demand impl cl (sourceNames impl left baseA) (left.compound cl) (left.targets cl))
        (cs.map fun cl => demand impl cl (sourceNames impl right baseB) (right.compound cl) (right.targets cl)) := by
    induction cs with
    | nil => exact .nil
    | cons first rest ih =>
      have clause := allowed List.mem_cons_self
      exact .cons (compares checked clause (a first clause) (b first clause) targets fit equal)
        (ih fun _ h => allowed (List.mem_cons_of_mem _ h))
  exact step _ (fun _ h => h)

theorem forest_evidence {m : Assignment}
    (alike : All₂ (RequestSame m) old new)
    (checked : All₂ (GeneralDeclarativeEvidence320.Evidence r i m) old dicts) :
    All₂ (GeneralDeclarativeEvidence320.Evidence r i m) new dicts :=
  GeneralDeclarativePlacementEvidence327.children_evidence alike checked

end Yulang.GeneralDeclarativeStableMergeEquiv329
