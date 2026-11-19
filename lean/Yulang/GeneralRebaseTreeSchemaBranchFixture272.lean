import Yulang.GeneralRebaseTreeSchema272

namespace Yulang.GeneralRebaseTreeSchemaBranchFixture272
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatSchemas (Schema)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralRebaseFiniteTree272 (Tree Canonical value scalar)
open GeneralRebaseTreeConstructors272 (nominalTree pairTree variantTree recordTree emptyTree)
open GeneralRebaseTreeExprCompile272 (Env Variables compile)
open GeneralRebaseTreeSchema272 (compute compute_sound)
open GeneralRebaseTreeInterpreter272 (Certified run)

def expression : Expr :=
 .nominal 5 [.primitive .pair [.primitive (.scalar .int) [],.primitive (.scalar .bool) []],
  .record 2 (.variant 7 (.primitive (.scalar .int) []))
    (.record 9 (.primitive .exactEmpty []) (.primitive .emptyRecord []))]

def first : Tree := pairTree (scalar .int) (scalar .bool)
def second : Tree := recordTree [2,9] (Fin.cases (variantTree 7 (scalar .int)) (Fin.cases emptyTree Fin.elim0))
def expected : Tree := nominalTree 5 [first,second]

def env : Env := fun _ _ => none
def vars : Variables := fun _ _ => .bottom
def schema : Schema := ⟨[⟨4,.actual,expression⟩],false⟩
def witness : Assignment := fun _ => (GeneralNominalCenteredHeadMatExpressions.value vars .actual expression,Common.rowEmpty)

theorem expression_checked : compile env .actual expression = some expected := by
 simp [expression,expected,first,second,compile,GeneralRebaseTreeExprCompile272.many,GeneralRebaseTreeExprCompile272.primitive,
   GeneralRebaseTreeRecordBuild272.appendField,recordTree,Bind.bind,Option.bind]

theorem schema_checked : compute env schema 4 = some expected := by
 simpa [compute,schema,GeneralRebaseTreeSchema272.entry] using expression_checked

theorem holds : schema.Holds vars witness := by
 intro eq member
 cases List.mem_singleton.mp member
 exact ⟨subtype_refl _,subtype_refl _⟩

theorem table : Certified witness (compute env schema) := by
 intro name t found
 exact compute_sound env witness vars schema name (by intro _ _ _ impossible; cases impossible) holds t found

def seek_pair : GeneralNominalRecursiveInspection.Origin := .structural (.nominal (.source 4) 5 0) .pair 1
def seek_record : GeneralNominalRecursiveInspection.Origin :=
 .structural (.structural (.nominal (.source 4) 5 1) (.record [9,2,2]) 1) (.variant 7) 0

theorem actual_pair_branch : run (compute env schema) seek_pair = .found (scalar .bool) := rfl
theorem actual_variant_under_record : run (compute env schema) seek_record = .found (scalar .int) := rfl

theorem other_identity_not_enriched : compute env schema 5 = none := rfl

end Yulang.GeneralRebaseTreeSchemaBranchFixture272
