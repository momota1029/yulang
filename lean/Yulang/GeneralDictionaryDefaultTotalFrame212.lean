import Yulang.GeneralNominalHeadLedgerFrame182
import Yulang.GeneralNominalCenteredHeadMatExtension
import Yulang.GeneralDictionaryDefaultKernel208

/-! Finite assignment support for total expressions. These supports include
all three modes and positional role defaults, rather than legacy schemas. -/
namespace Yulang.GeneralDictionaryDefaultTotalFrame212
open GeneralDeclarations GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalMaterialization (Mode)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalCenteredHeadMatExpressions
open GeneralNominalCenteredHeadMatSchemas (Schema Equation)
open GeneralNominalCenteredHeadMatExtension (names sources value_congr)
open GeneralNominalCenteredHeadMatEffects
variable {roles : Roles.RoleDecls} {first last : Assignment}

 def resolve (plan : Plan roles) (mode : Mode) (name : Nat) : Nat :=
  if name ∈ plan.packet.declaration.outputNames then plan.binder name
  else match mode with
    | .actual => plan.binder name
    | .lower => ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1
    | .upper => ((GeneralNominalPacketSupport.capture plan.packet).inputs name).2

 theorem variables_sources (plan : Plan roles) (model : Assignment) :
    variables plan model = sources (resolve plan) model := by
  funext mode name
  by_cases member : name ∈ plan.packet.declaration.outputNames
  · simp only [variables,sources,resolve,member,ite_true] <;> rfl
  · cases mode <;> simp only [variables,sources,resolve,member,ite_false] <;> rfl

 def reads (resolve : Mode → Nat → Nat) (expression : Expr) : List Nat :=
  (names expression).flatMap fun name => [resolve .actual name,resolve .lower name,resolve .upper name]

 theorem reads_member (resolve : Mode → Nat → Nat) (expression : Expr) (mode : Mode)
    (member : name ∈ names expression) : resolve mode name ∈ reads resolve expression := by
  apply List.mem_flatMap.mpr
  refine ⟨name,member,?_⟩
  cases mode <;> simp

 theorem value_same (resolve : Mode → Nat → Nat) (expression : Expr)
    (same : Agree (reads resolve expression) first last) :
    value (sources resolve first) mode expression = value (sources resolve last) mode expression := by
  apply value_congr
  intro mode name member
  unfold sources
  rw [same _ (reads_member resolve expression mode member)]

 def schemaSources (resolve : Mode → Nat → Nat) (schema : Schema) : List Nat :=
  schema.equations.flatMap fun equation => equation.target :: reads resolve equation.expression

 theorem schema_iff (resolve : Mode → Nat → Nat) (schema : Schema)
    (same : Agree (schemaSources resolve schema) first last) :
    schema.Holds (sources resolve first) first ↔ schema.Holds (sources resolve last) last := by
  apply forall_congr'; intro equation
  apply forall_congr'; intro member
  have target := same equation.target (List.mem_flatMap.mpr ⟨equation,member,List.mem_cons_self ..⟩)
  have rhs := value_same (mode := equation.mode) resolve equation.expression
    (fun name present => same name (List.mem_flatMap.mpr ⟨equation,member,List.mem_cons_of_mem _ present⟩))
  unfold Equation.Holds
  rw [target,rhs]

 theorem plan_schema_iff (plan : Plan roles) (schema : Schema)
    (same : Agree (schemaSources (resolve plan) schema) first last) :
    schema.Holds (variables plan first) first ↔ schema.Holds (variables plan last) last := by
  rw [variables_sources,variables_sources]
  exact schema_iff _ _ same

 def bodyResolve (plan : Plan roles) : GeneralDictionaryAssociatedProvenance.Body → Mode → Nat → Nat
  | .explicit _ => resolve plan
  | .default _ _ _ => fun _ index => (List.ofFn plan.input.center)[index]?.getD 0

 theorem body_variables_sources (plan : Plan roles) (body) (model : Assignment) :
    bodyVariables plan model body = sources (bodyResolve plan body) model := by
  cases body with
  | explicit => exact variables_sources plan model
  | default => rfl

 def bodySources (plan : Plan roles) (target : Nat) (body : GeneralDictionaryAssociatedProvenance.Body) : List Nat :=
  schemaSources (bodyResolve plan body) (bodySchema plan target body)

 theorem body_iff (plan : Plan roles) (target : Nat) (body)
    (same : Agree (bodySources plan target body) first last) :
    BodyHolds plan target first body ↔ BodyHolds plan target last body := by
  unfold BodyHolds
  rw [body_variables_sources,body_variables_sources]
  exact schema_iff _ _ same

 noncomputable def classSources (state : GeneralNominalCenteredSteps.State roles)
    (focus : GeneralSourceDictionaries.Occurrence roles) (plan : Plan roles) : List Nat :=
  (GeneralNominalCenteredHeadOutputs.requests state focus).flatMap fun output =>
    output.target :: ((GeneralDictionaryAssociatedProvenance.lookup roles plan.packet.declaration output.name).toList.flatMap
      fun body => bodySources plan output.target body)

 theorem class_iff (state : GeneralNominalCenteredSteps.State roles)
    (focus : GeneralSourceDictionaries.Occurrence roles) (plan : Plan roles)
    (same : Agree (classSources state focus plan) first last) :
    ClassEffects state focus plan first ↔ ClassEffects state focus plan last := by
  have target output (member : output ∈ GeneralNominalCenteredHeadOutputs.requests state focus) :
      first output.target = last output.target :=
    same _ (List.mem_flatMap.mpr ⟨output,member,List.mem_cons_self ..⟩)
  unfold ClassEffects
  apply and_congr
  · apply forall_congr'; intro output
    apply forall_congr'; intro member
    apply forall_congr'; intro body
    apply forall_congr'; intro found
    apply body_iff
    intro name present
    apply same
    apply List.mem_flatMap.mpr
    refine ⟨output,member,List.mem_cons_of_mem _ ?_⟩
    exact List.mem_flatMap.mpr ⟨body,Option.mem_toList.mpr found,present⟩
  · unfold GeneralNominalCenteredHeadOutputs.EqualOutputs
    apply forall_congr'; intro a
    apply forall_congr'; intro aMember
    apply forall_congr'; intro b
    apply forall_congr'; intro bMember
    rw [target a aMember,target b bMember]

end Yulang.GeneralDictionaryDefaultTotalFrame212
