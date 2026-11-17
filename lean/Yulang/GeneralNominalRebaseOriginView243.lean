import Yulang.GeneralNominalRebaseLiveView243
import Yulang.GeneralNominalOriginTerms
set_option backward.isDefEq.respectTransparency false
/-! Expression sources beneath actual nominal and structural observation paths.
No argument is selected by this compilation; all old observational witnesses
are preserved exactly, including nondeterministic equivalent projections. -/
namespace Yulang.GeneralNominalRebaseOriginView243
open Core.PresenceGeneration (TyTerm CompTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseRawView243 (read)
open CommonNominalFullCarrier
open GeneralNominalRecursiveInspection (Test shapeValue)
abbrev Shape := GeneralNormalizedObservation.Shape

inductive Origin where
 | source (term : TyTerm Nat)
 | nominal (parent : Origin) (name index : Nat)
 | structural (parent : Origin) (shape : Shape) (index : Nat)

inductive Observes (model : Assignment) : Origin → Ty → Prop
 | source (term) : Observes model (.source term) (term.eval CommonNominalFullCarrier.model model)
 | nominal : Observes model parent value → Equivalent value (nominal name arguments) →
     arguments[index]? = some (.inl actual) → Observes model (.nominal parent name index) actual
 | structural : Observes model parent value → values.length = shape.arity →
     Equivalent value (shapeValue shape values) → values[index]? = some actual →
     Observes model (.structural parent shape index) actual

def compile (mapping : Nat → CompTerm Nat) : GeneralNominalRecursiveInspection.Origin → Origin
 | .source name => .source (mapping name).1
 | .nominal parent name index => .nominal (compile mapping parent) name index
 | .structural parent shape index => .structural (compile mapping parent) shape index

theorem compile_exact (mapping : Nat → CompTerm Nat) (model : Assignment)
 (origin : GeneralNominalRecursiveInspection.Origin) (actual : Ty) :
 Observes model (compile mapping origin) actual ↔ GeneralNominalRecursiveInspection.Observes (read mapping model) origin actual := by
 induction origin generalizing actual with
 | source name =>
   constructor
   · intro observed; cases observed; exact .source _
   · intro observed; cases observed; exact .source _
 | nominal parent name index ih =>
   constructor
   · intro observed; cases observed with
     | nominal seen equal found => exact .nominal ((ih _).mp seen) equal found
   · intro observed; cases observed with
     | nominal seen equal found => exact .nominal ((ih _).mpr seen) equal found
 | structural parent shape index ih =>
   constructor
   · intro observed; cases observed with
     | structural seen length equal found => exact .structural ((ih _).mp seen) length equal found
   · intro observed; cases observed with
     | structural seen length equal found => exact .structural ((ih _).mpr seen) length equal found

def subst (mapping : Nat → CompTerm Nat) : Origin → Origin
 | .source term => .source (term.subst mapping)
 | .nominal parent name index => .nominal (subst mapping parent) name index
 | .structural parent shape index => .structural (subst mapping parent) shape index

theorem subst_exact (mapping : Nat → CompTerm Nat) (model : Assignment) (origin : Origin) (actual : Ty) :
 Observes model (subst mapping origin) actual ↔ Observes (read mapping model) origin actual := by
 induction origin generalizing actual with
 | source term =>
   constructor
   · intro observed; cases observed
     rw [TyTerm.eval_subst]
     exact .source _
   · intro observed; cases observed
     have h : Observes model (.source (term.subst mapping)) ((term.subst mapping).eval CommonNominalFullCarrier.model model) := .source _
     rw [TyTerm.eval_subst] at h
     exact h
 | nominal parent name index ih =>
   constructor
   · intro observed; cases observed with
     | nominal seen equal found => exact .nominal ((ih _).mp seen) equal found
   · intro observed; cases observed with
     | nominal seen equal found => exact .nominal ((ih _).mpr seen) equal found
 | structural parent shape index ih =>
   constructor
   · intro observed; cases observed with
     | structural seen length equal found => exact .structural ((ih _).mp seen) length equal found
   · intro observed; cases observed with
     | structural seen length equal found => exact .structural ((ih _).mpr seen) length equal found

def Same (model : Assignment) (first last : Origin) : Prop :=
 (∃ value, Observes model first value) ∧ (∃ value, Observes model last value) ∧
 ∀ a b, Observes model first a → Observes model last b → Equivalent a b

def Head (model : Assignment) (origin : Origin) (test : Test) : Prop :=
 (∃ value, Observes model origin value) ∧ ∀ value, Observes model origin value → test.Holds value

theorem same_exact (mapping : Nat → CompTerm Nat) (model : Assignment) (first last : GeneralNominalRecursiveInspection.Origin) :
 Same model (compile mapping first) (compile mapping last) ↔ GeneralNominalOriginTerms.Same (read mapping model) first last := by
 simp only [Same,GeneralNominalOriginTerms.Same,compile_exact]

theorem head_exact (mapping : Nat → CompTerm Nat) (model : Assignment) (origin : GeneralNominalRecursiveInspection.Origin) (test : Test) :
 Head model (compile mapping origin) test ↔ GeneralNominalOriginTerms.Head (read mapping model) origin test := by
 simp only [Head,GeneralNominalOriginTerms.Head,compile_exact]

theorem same_subst (mapping : Nat → CompTerm Nat) (model : Assignment) (first last : Origin) :
 Same model (subst mapping first) (subst mapping last) ↔ Same (read mapping model) first last := by
 simp only [Same,subst_exact]

theorem head_subst (mapping : Nat → CompTerm Nat) (model : Assignment) (origin : Origin) (test : Test) :
 Head model (subst mapping origin) test ↔ Head (read mapping model) origin test := by
 simp only [Head,subst_exact]

def compileTests (mapping : Nat → CompTerm Nat) (tests : List (GeneralNominalRecursiveInspection.Origin × Test)) : List (Origin × Test) :=
 tests.map (fun test => (compile mapping test.1,test.2))

theorem tests_exact (mapping : Nat → CompTerm Nat) (model : Assignment) (tests : List (GeneralNominalRecursiveInspection.Origin × Test)) :
 (∀ test ∈ compileTests mapping tests, Head model test.1 test.2) ↔
 ∀ test ∈ tests, GeneralNominalOriginTerms.Head (read mapping model) test.1 test.2 := by
 simp only [compileTests,List.forall_mem_map,head_exact]
end Yulang.GeneralNominalRebaseOriginView243
