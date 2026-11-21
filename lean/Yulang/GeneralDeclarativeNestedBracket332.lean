import Yulang.GeneralDeclarativeNestedClash332
import Yulang.GeneralDeclarativeNestedIndex332
import Yulang.CommonNominalFullModel

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNestedBracket332
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralDeclarativeNestedClash332 (Apart pairExpr from_lower)
open GeneralDeclarativeNestedDecode332 (normalized)
open GeneralDeclarativeNestedIndex332 (ofRows)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarationExamples (constructors)
open GeneralDeclarationPatterns (Pattern)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeExampleSource320 (int)
open CommonNominalFullCarrier (Ty record emptyRecord observeTy variant pair Subtype
  subtype_refl common_pair_iff common_variant_iff)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullDemand (ProbeAt ProbeStep MaskedProbeStep producerLe_iff_probe)

private theorem finite_record_below_width (label : Nat)
    (payload rest : CommonNominalFinite.Ty Common.Row) :
    CommonNominalFullDemand.ProducerLe Common.rowLe (.record label payload rest) .emptyRecord := by
  apply (producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  cases rank <;> cases obs <;> simp_all [ProbeAt,ProbeStep,MaskedProbeStep]
  all_goals split <;> simp_all

theorem record_below_width (label : Nat) (payload rest : Ty) :
    Subtype (record label payload rest) emptyRecord :=
  fun _ => finite_record_below_width label _ _

abbrev width : Expr := .primitive .emptyRecord []
abbrev wanted : Expr := .variant 4 (pairExpr (.variable 3) (.record 7 (.variable 4) width))
abbrev wider : Expr := .variant 4 (pairExpr (.variable 3) width)

abbrev pattern : Pattern := .variant 4 (.app 5 [.var 0,.record 7 (.var 1) (.var 2)])
abbrev lowRow : Equation := ⟨0,wanted⟩
abbrev actualRow : Equation := ⟨1,wanted⟩
abbrev highRow : Equation := ⟨2,wider⟩
abbrev eqs : List Equation := [lowRow,actualRow,highRow]
abbrev state : State := ⟨⟨[],[(0,1),(1,2)]⟩,eqs⟩
abbrev arg : Capture := ⟨0,1,2⟩
abbrev uses (mode : GeneralNominalMaterialization.Mode) : List Occurrence :=
  [⟨0,mode,.variable 3⟩,⟨1,mode,.variable 4⟩,⟨2,mode,width⟩]

def support : Supported state (fun _ => False) :=
  ⟨fun e o => e ∈ eqs ∧ o = .source,fun h => h.1⟩
noncomputable def src := ofRows eqs (fun _ h => from_source support ⟨h,rfl⟩)

theorem limited_upper :
    normalized src constructors interpretation .lower (.variable 0) pattern = some (uses .lower) ∧
    normalized src constructors interpretation .actual (.variable 1) pattern = some (uses .actual) ∧
    normalized src constructors interpretation .upper (.variable 2) pattern = none :=
  ⟨rfl,rfl,rfl⟩

abbrev bool : Ty := .base .bool
abbrev actualType := variant 4 (pair int (record 7 bool emptyRecord))
abbrev widerType := variant 4 (pair int emptyRecord)
def model : Assignment := fun n =>
  (if n = 0 ∨ n = 1 then actualType else if n = 2 then widerType else if n = 4 then bool else int,Common.rowEmpty)

theorem model_exists : Models state model := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro pair allotted
    change pair ∈ [(0,1),(1,2)] at allotted
    rcases List.mem_cons.mp allotted with rfl|other
    · exact subtype_refl _
    · cases List.mem_singleton.mp other
      exact (common_variant_iff 4 ..).mpr ((common_pair_iff ..).mpr
        ⟨subtype_refl _,record_below_width _ _ _⟩)
  · intro e read
    change e ∈ [lowRow,actualRow,highRow] at read
    simp only [List.mem_cons,List.not_mem_nil,or_false] at read
    rcases read with h|h|h <;> cases h <;> exact eqv_refl _

/-- In this actual interval the independent upper projection is
too weak to show a required nested field; the center does have the
field in an inhabited model. Neither a clash nor a final pending
diagnostic follows merely from the reader returning none. -/
theorem upper_none_not_clash :
    normalized src constructors interpretation .upper (.variable 2) pattern = none ∧
      ∃ m, Models state m ∧ eqAt m (.variable 1) wanted :=
  ⟨limited_upper.2.2,model,model_exists,eqv_refl _⟩

/-- In contrast the same exact wider layout, when given as a
supported LOWER observation rather than an upper one, is genuinely
incompatible with this required nested field. -/
theorem actual_lower_obstruction : Apart wider wanted := by
  apply Apart.tagged
  apply Apart.second
  exact .missing (raw := []) (stop := width) (desiredFields := [(7,.variable 4)])
    .width rfl .here

theorem lower_none_is_real (m : Assignment) (valid : Models state m) :
    ¬eqAt m (.variable 2) wanted :=
  from_lower (GeneralDeclarativeOpaqueNominal328.point_bounded state 2)
    (p := support)
    (.row (from_source support
      ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),rfl⟩))
    actual_lower_obstruction m valid

end Yulang.GeneralDeclarativeNestedBracket332
