import Yulang.GeneralNominalRebaseOriginView243
import Yulang.GeneralDictionaryDefaultEvidence204
set_option backward.isDefEq.respectTransparency false
/-! Total explicit/default output expressions with materialized source leaves.
Nominal arguments keep actual mode; defaults keep positional input centers. -/
namespace Yulang.GeneralNominalRebaseEffectView243
open Core.PresenceGeneration (TyTerm CompTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseRawView243 (read)
open GeneralNominalMaterialization (Mode)
open GeneralNominalCenteredHeadMatExpressions (primitiveValue)
open CommonNominalFullCarrier
abbrev OldExpr := GeneralNominalCenteredHeadMatExpressions.Expr

inductive Expr where
 | source (term : TyTerm Nat)
 | primitive (constructor : GeneralCandidateInspection.Primitive) (arguments : List Expr)
 | nominal (name : Nat) (arguments : List Expr)
 | record (label : Nat) (payload tail : Expr)
 | variant (tag : Nat) (payload : Expr)
 | join (first last : Expr)

mutual
 def eval (model : Assignment) : Expr → Ty
 | .source term => term.eval CommonNominalFullCarrier.model model
 | .primitive constructor arguments => primitiveValue constructor (evals model arguments)
 | .nominal name arguments => nominal name ((evals model arguments).map Sum.inl)
 | .record label payload tail => record label (eval model payload) (eval model tail)
 | .variant tag payload => variant tag (eval model payload)
 | .join first last => .union (eval model first) (eval model last)
 def evals (model : Assignment) : List Expr → List Ty
 | [] => []
 | first :: rest => eval model first :: evals model rest
end

mutual
 def compile (variables : Mode → Nat → TyTerm Nat) (mode : Mode) : OldExpr → Expr
 | .variable name => .source (variables mode name)
 | .primitive constructor arguments => .primitive constructor (compileMany variables mode arguments)
 | .nominal name arguments => .nominal name (compileMany variables .actual arguments)
 | .record label payload tail => .record label (compile variables mode payload) (compile variables mode tail)
 | .variant tag payload => .variant tag (compile variables mode payload)
 | .join first last => .join (compile variables mode first) (compile variables mode last)
 def compileMany (variables : Mode → Nat → TyTerm Nat) (mode : Mode) : List OldExpr → List Expr
 | [] => []
 | first :: rest => compile variables mode first :: compileMany variables mode rest
end

mutual
 theorem compile_exact (variables : Mode → Nat → TyTerm Nat) (mode : Mode) (model : Assignment) (expression : OldExpr) :
 eval model (compile variables mode expression) = GeneralNominalCenteredHeadMatExpressions.value
   (fun mode name => (variables mode name).eval CommonNominalFullCarrier.model model) mode expression := by
 cases expression with
 | «variable» => rfl
 | primitive constructor arguments => simp only [compile,eval,compileMany_exact,GeneralNominalCenteredHeadMatExpressions.value]
 | nominal name arguments => simp only [compile,eval,compileMany_exact,GeneralNominalCenteredHeadMatExpressions.value]
 | record label payload tail => simp only [compile,eval,compile_exact,GeneralNominalCenteredHeadMatExpressions.value]
 | variant tag payload => simp only [compile,eval,compile_exact,GeneralNominalCenteredHeadMatExpressions.value]
 | join first last => simp only [compile,eval,compile_exact,GeneralNominalCenteredHeadMatExpressions.value]
 theorem compileMany_exact (variables : Mode → Nat → TyTerm Nat) (mode : Mode) (model : Assignment) (expressions : List OldExpr) :
 evals model (compileMany variables mode expressions) = GeneralNominalCenteredHeadMatExpressions.values
   (fun mode name => (variables mode name).eval CommonNominalFullCarrier.model model) mode expressions := by
 cases expressions with
 | nil => rfl
 | cons first rest => simp only [compileMany,evals,compile_exact,compileMany_exact,GeneralNominalCenteredHeadMatExpressions.values]
end

mutual
 def subst (mapping : Nat → CompTerm Nat) : Expr → Expr
 | .source term => .source (term.subst mapping)
 | .primitive constructor arguments => .primitive constructor (substMany mapping arguments)
 | .nominal name arguments => .nominal name (substMany mapping arguments)
 | .record label payload tail => .record label (subst mapping payload) (subst mapping tail)
 | .variant tag payload => .variant tag (subst mapping payload)
 | .join first last => .join (subst mapping first) (subst mapping last)
 def substMany (mapping : Nat → CompTerm Nat) : List Expr → List Expr
 | [] => []
 | first :: rest => subst mapping first :: substMany mapping rest
end

mutual
 theorem subst_exact (mapping : Nat → CompTerm Nat) (model : Assignment) (expression : Expr) :
 eval model (subst mapping expression) = eval (read mapping model) expression := by
 cases expression with
 | source term => exact TyTerm.eval_subst ..
 | primitive constructor arguments => simp only [subst,eval,substMany_exact]
 | nominal name arguments => simp only [subst,eval,substMany_exact]
 | record label payload tail => simp only [subst,eval,subst_exact]
 | variant tag payload => simp only [subst,eval,subst_exact]
 | join first last => simp only [subst,eval,subst_exact]
 theorem substMany_exact (mapping : Nat → CompTerm Nat) (model : Assignment) (expressions : List Expr) :
 evals model (substMany mapping expressions) = evals (read mapping model) expressions := by
 cases expressions with
 | nil => rfl
 | cons first rest => simp only [substMany,evals,subst_exact,substMany_exact]
end

open GeneralNominalCenters (Plan)
open GeneralDictionaryAssociatedProvenance (Body Supplies)

def variables (plan : Plan roles) (mapping : Nat → CompTerm Nat) (mode : Mode) (name : Nat) : TyTerm Nat :=
 if name ∈ plan.packet.declaration.outputNames then (mapping (plan.binder name)).1
 else match mode with
 | .actual => (mapping (plan.binder name)).1
 | .lower => (mapping ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1).1
 | .upper => (mapping ((GeneralNominalPacketSupport.capture plan.packet).inputs name).2).1

def bodyVariables (plan : Plan roles) (mapping : Nat → CompTerm Nat) : Body → Mode → Nat → TyTerm Nat
 | .explicit _ => variables plan mapping
 | .default _ _ _ => fun _ index => (mapping ((List.ofFn plan.input.center)[index]?.getD 0)).1

theorem variables_exact (plan : Plan roles) (mapping : Nat → CompTerm Nat) (model : Assignment) (mode : Mode) (name : Nat) :
 (variables plan mapping mode name).eval CommonNominalFullCarrier.model model =
 GeneralNominalCenteredHeadMatEffects.variables plan (read mapping model) mode name := by
 unfold variables GeneralNominalCenteredHeadMatEffects.variables
 split <;> cases mode <;> rfl

theorem bodyVariables_exact (plan : Plan roles) (mapping : Nat → CompTerm Nat) (model : Assignment) (body : Body) :
 (fun mode name => (bodyVariables plan mapping body mode name).eval CommonNominalFullCarrier.model model) =
 GeneralNominalCenteredHeadMatEffects.bodyVariables plan (read mapping model) body := by
 funext mode name
 cases body with
 | explicit => exact variables_exact plan mapping model mode name
 | default => rfl

structure Equation where
 target : TyTerm Nat
 expression : Expr

def Equation.Holds (equation : Equation) (model : Assignment) : Prop :=
 Equivalent (equation.target.eval CommonNominalFullCarrier.model model) (eval model equation.expression)

def body (plan : Plan roles) (mapping : Nat → CompTerm Nat) (target : Nat) (source : Body) : Option Equation :=
 (GeneralNominalCenteredHeadMatEffects.compileBody plan source).map (fun expression =>
 ⟨(mapping target).1,compile (bodyVariables plan mapping source) .actual expression⟩)

theorem body_exact (plan : Plan roles) (mapping : Nat → CompTerm Nat) (model : Assignment) (target : Nat) (source : Body)
 (translated : GeneralNominalCenteredHeadMatEffects.compileBody plan source = some expression) :
 (⟨(mapping target).1,compile (bodyVariables plan mapping source) .actual expression⟩ : Equation).Holds model ↔
 GeneralNominalCenteredHeadMatEffects.BodyHolds plan target (read mapping model) source := by
 rw [GeneralNominalCenteredHeadMatEffects.body_equation translated]
 unfold Equation.Holds
 rw [compile_exact,bodyVariables_exact]
 rfl

/-- The original provenance and successful-translation requirements are kept. -/
def OutputWitness (plan : Plan roles) (mapping : Nat → CompTerm Nat) (model : Assignment) (output : GeneralSourceState.Output) : Prop :=
 ∃ source, Supplies roles plan.packet.declaration output.name source ∧
   ∃ equation, body plan mapping output.target source = some equation ∧ equation.Holds model

theorem output_exact (plan : Plan roles) (mapping : Nat → CompTerm Nat) (model : Assignment) (output : GeneralSourceState.Output) :
 OutputWitness plan mapping model output ↔ GeneralDictionaryDefaultEvidence204.OutputWitness plan (read mapping model) output := by
 constructor
 · rintro ⟨source,supplied,equation,translated,valid⟩
   obtain ⟨expression,found,rfl⟩ := Option.map_eq_some_iff.mp translated
   exact ⟨source,supplied,⟨expression,found⟩,(body_exact plan mapping model output.target source found).mp valid⟩
 · rintro ⟨source,supplied,⟨expression,found⟩,valid⟩
   exact ⟨source,supplied,_,by simp [body,found],(body_exact plan mapping model output.target source found).mpr valid⟩
end Yulang.GeneralNominalRebaseEffectView243
