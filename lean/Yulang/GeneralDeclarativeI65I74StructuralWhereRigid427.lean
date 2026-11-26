import Yulang.GeneralDeclarativeI65I74StructuralWhereParent427
import Yulang.GeneralDeclarativeRecordIntervals330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.StructuralWhere427
open CommonNominalFullCarrier (Ty record observeTy Subtype Equivalent subtype_trans)
open CommonNominalFullDemand (ProbeAt)
open GeneralDeclarativeRecordChannel330 (project)
open GeneralDeclarativeRecordIntervals330 (direct projected_below)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeK2Graph321 (Shape)
open GeneralDeclarativeGraphRows321 (observed structural literal_head shapeOf)
open GeneralDeclarativeInspect321 (Visit)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralDeclarationPatterns (Pattern)

private def fieldTestEnv427 : CommonNominalFullDemand.Environment Common.Row :=
  ⟨fun _ => .bottom,fun _ => []⟩

/-- A rigid record and a concrete int are observably distinct; a checked
mismatch is not failure of a search or absence of a retained row. -/
theorem actual_record_cannot_be_int427 (label : Nat) (field rest : Ty) :
    ¬ Equivalent (record label field rest) (.base .int) := by
  intro agree
  have expected : ProbeAt Common.rowLe 0 fieldTestEnv427 (observeTy 1 (.base .int)) (.base .int) := rfl
  have impossible := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (agree.1 1)
      0 fieldTestEnv427 (.base .int) expected
  change False at impossible
  exact impossible

theorem first_box_payload_equivalence427 (label : Nat) {a b ar br : Ty}
    (h : Equivalent (record label a ar) (record label b br)) :
    Equivalent a b :=
  ⟨projected_below label false (direct ..) (direct ..) h.1,
    projected_below label false (direct ..) (direct ..) h.2⟩

/-- A positive source mismatch at a known rigid payload. The actual
row class, requested payload and distinct cases are all structural
data, independent of fitting models. -/
inductive ExactOpposite427 (s : State) (site : Nat) : Expr → Type where
  | intAgainstRecord {label : Nat} {field rest : Expr} {row : Nat} :
      s.current.ordinary.equations[row]? =
        some ⟨site,.primitive (.scalar .int) []⟩ →
      ExactOpposite427 s site (.record label field rest)
  | recordAgainstInt {label field : Nat} {row : Nat} :
      s.current.ordinary.equations[row]? =
        some ⟨site,.record label (.variable field) (.primitive .emptyRecord [])⟩ →
      ExactOpposite427 s site (.primitive (.scalar .int) [])

theorem ExactOpposite427.inspects {s site code} (d : ExactOpposite427 s site code) :
    GeneralDeclarativeInspect321.Inspects code :=
  match d with
  | .intAgainstRecord _ => .record
  | .recordAgainstInt _ => .primitive

theorem exact_opposite_excludes_same_fit_payload427 {s site code}
    (d : ExactOpposite427 s site code) (m : Model) (fit : Fits s m)
    (vars : GeneralNominalMaterialization.Mode → Nat → Ty) :
    ¬ Equivalent (m.assignment site).1
      (GeneralNominalCenteredHeadMatExpressions.value vars .actual code) := by
  intro agreement
  cases d with
  | @intAgainstRecord label field rest row original =>
    have found := fit.1.1.2 _ (List.mem_of_getElem? original)
    change Equivalent (m.assignment site).1 (.base .int) at found
    change Equivalent (m.assignment site).1 (record label _ _) at agreement
    exact actual_record_cannot_be_int427 label _ _
      (eqv_trans ⟨agreement.2,agreement.1⟩ found)
  | @recordAgainstInt label field row original =>
    have found := fit.1.1.2 _ (List.mem_of_getElem? original)
    change Equivalent (m.assignment site).1 (record label (m.assignment field).1 .emptyRecord) at found
    change Equivalent (m.assignment site).1 (.base .int) at agreement
    exact actual_record_cannot_be_int427 label _ _
      (eqv_trans ⟨found.2,found.1⟩ agreement)

/-- A real field visit of a competing declaration. Both endpoints are
literal ordinary rows at addressed positions in the actual State. -/
structure BoxRival427 (s : State) (q : Request) (d : Declaration) where
  ordinal : Nat
  authored : (authoredRegistry s.current).declarations[ordinal]? = some d
  visibleAt : d ∈ visible s q
  root : Nat
  args : q.demand.arguments = [point root]
  box : Nat
  headField : Pattern
  headTail : Pattern
  head : d.head = [.record box headField headTail]
  want : Expr
  tail : Expr
  compiled : translateWhere427 s (.record box headField headTail) = some (.record box want tail)
  field : Nat
  boxRow : Nat
  seenBox : s.current.ordinary.equations[boxRow]? =
    some ⟨root,.record box (.variable field) (.primitive .emptyRecord [])⟩
  clash : ExactOpposite427 s field want

theorem real_rival_visits_original_mismatched_field427 {s q d} (r : BoxRival427 s q d) :
    Visit (structural s.current.ordinary) r.root (.record r.box r.want r.tail) r.field := by
  have actual := literal_head (List.mem_of_getElem? r.seenBox)
    (show shapeOf (.record r.box (.variable r.field) (.primitive .emptyRecord [])) =
      some (.record [(r.box,r.field)]) from by simp [shapeOf,GeneralDeclarativeGraphRows321.fields])
  exact .field actual List.mem_cons_self List.mem_cons_self (.here r.clash.inspects)

theorem model_excludes_source_head_with_actual_opposite_payload427 {s q d} (r : BoxRival427 s q d)
    (m : Model) (fit : Fits s m) : ¬Nonempty (SourceHead s q d) := by
  rintro ⟨e⟩
  cases e with
  | ordered capture read =>
    rw [r.args,r.head] at read
    cases read with
    | cons first _ =>
      cases first with
      | declared view _ =>
        have mismatch := view.syntaxHead
        change GeneralDeclarationPatterns.Pattern.record _ _ _ = .app _ _ at mismatch
        cases mismatch
      | ordinary shown =>
        let vars := GeneralDeclarativeWhere319.variables capture m.assignment
        obtain ⟨_,code,compiled,center⟩ := shown
        have compiler : code = .record r.box r.want r.tail := Option.some.inj
          (compiled.symm.trans r.compiled)
        subst code
        have headMeaning := GeneralDeclarativeNormalized320.center_sound center m.assignment fit.1.1
        change Equivalent (m.assignment r.root).1
          (record r.box (GeneralNominalCenteredHeadMatExpressions.value vars .actual r.want)
            (GeneralNominalCenteredHeadMatExpressions.value vars .actual r.tail)) at headMeaning
        have original := fit.1.1.2 _ (List.mem_of_getElem? r.seenBox)
        change Equivalent (m.assignment r.root).1 (record r.box (m.assignment r.field).1 .emptyRecord) at original
        have nested := eqv_trans ⟨original.2,original.1⟩ headMeaning
        exact exact_opposite_excludes_same_fit_payload427 r.clash m fit vars
          (first_box_payload_equivalence427 r.box nested)
  | joined joined =>
    have text := (List.cons.inj (joined.head.symm.trans r.head)).1
    have impossible := joined.normalized
    rw [text] at impossible
    change GeneralDeclarationPatterns.Pattern.record _ _ _ = .variant _ _ at impossible
    cases impossible

end Yulang.GeneralDeclarativeI65.StructuralWhere427
