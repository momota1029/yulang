import Yulang.GeneralNominalCenteredHeadMatHeadParts

set_option backward.isDefEq.respectTransparency false

/-! Actual-mode head schema uses recover whole finite payloads. Every queried
constructor consumes its cost before recursion into its finite projections. -/
namespace Yulang.GeneralNominalCenteredHeadMatSchemaMass
open GeneralDeclarationPatterns GeneralNominalCenters
open GeneralNominalCenteredHeadMatPatternSemantics
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalCenteredHeadMatHeadShape GeneralNominalCenteredHeadMatHeadParts
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalFiniteMeaning
open GeneralNominalReadbackFunctionality GeneralNominalCompoundReadback GeneralNominalMaterialization
open GeneralNominalHeadMatchMass (weighted)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {plan : Plan roles} {model : GeneralNominalCommonBridge.Assignment}

def Part (semantics : Algebra) (plan : Plan roles) (model : GeneralNominalCommonBridge.Assignment)
    (name : Nat) (pattern : Pattern) : Prop :=
  CompleteLabel pattern ∧ Equivalent (model (plan.binder name)).1 (eval semantics (fun _ => .bottom) pattern)

theorem at_congr (known : At model .actual origin value) (equal : Equivalent value other) :
    At model .actual origin other :=
  ⟨known.1,fun actual seen => eqv_trans (known.2 actual seen) equal⟩

theorem schema_restrict (valid : plan.SchemaHolds last model) (included : Included first last) :
    plan.SchemaHolds first model := ⟨fun _ member => valid.1 _ (included.1 member),fun _ member => valid.2 _ (included.2 member)⟩

theorem ofFn_index (items : List α) (length : items.length = n) (f : α → β) :
    List.ofFn (fun index : Fin n => f (items[index.val]'(by rw [length]; exact index.isLt))) = items.map f := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_map,length]
  · intro index one two
    simp only [List.getElem_ofFn,List.getElem_map]

theorem sum_le (first last : Fin n → Nat) (bounded : ∀ index, first index ≤ last index) :
    (List.ofFn first).sum ≤ (List.ofFn last).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [List.ofFn_succ,List.sum_cons]
      exact Nat.add_le_add (bounded 0) (ih _ _ (fun index => bounded index.succ))

theorem node_weight (test : Test) (children : Fin (arity test) → Expr Nat) (capture : Nat → Nat) :
    weighted capture (quote (.node test children)) =
      cost test + (List.ofFn fun index => weighted capture (quote (children index))).sum := by
  cases test with
  | scalar => simp only [weighted,quote,cost,arity,List.ofFn_zero,List.sum_nil,Nat.add_zero]
  | structural shape => cases shape <;> simp only [weighted,quote,cost,List.map_ofFn,Function.comp_def]
  | nominal => simp only [weighted,quote,cost,List.map_ofFn,Function.comp_def]

theorem schema_mass (term : Expr Nat) (canonical : Canonical term)
    (complete : CompleteLabel pattern)
    (known : At model .actual origin (eval (algebra constructors interpretation) (fun _ => .bottom) pattern))
    (schemaValid : plan.SchemaHolds (schema (quote term) origin .actual) model)
    (bounded : ∀ name label, Part (algebra constructors interpretation) plan model name label → capture name ≤ label.encode.size) :
    weighted capture (quote term) ≤ pattern.encode.size := by
  induction term generalizing pattern origin with
  | leaf name =>
      have same := schemaValid.2 ⟨name,origin,.actual⟩ (by simp [quote,schema])
      simp only [ite_true] at same
      obtain ⟨actual,seen⟩ := known.1
      have meaning := eqv_trans (eqv_symm (same.2.2 _ _ seen (.source _))) (known.2 actual seen)
      simpa only [quote,weighted,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using
        bounded name pattern ⟨complete,meaning⟩
  | node test children ih =>
      have head := schemaValid.1 _ (GeneralNominalStructuralContainment.root_test test children origin .actual)
      obtain ⟨actual,seen⟩ := known.1
      obtain ⟨pieces,length,pieceComplete,equal,bound⟩ := inversion complete canonical.1
        (holds_congr (known.2 actual seen) (head.2 actual seen))
      let part (index : Fin (arity test)) : Pattern := pieces[index.val]'(by rw [length]; exact index.isLt)
      have built : At model .actual origin
          (build test (fun index => eval (algebra constructors interpretation) (fun _ => .bottom) (part index))) := by
        have ready := at_congr known equal
        rw [realize_build (by simpa only [List.length_map] using length)] at ready
        simpa only [List.getElem_map,part] using ready
      have each (index : Fin (arity test)) : weighted capture (quote (children index)) ≤ (part index).encode.size := by
        apply ih index (canonical.2 index) (pieceComplete _ (List.getElem_mem ..))
          (project_value test canonical.1 _ built index)
        · have included := GeneralNominalStructuralContainment.child_included test children origin .actual index
          have mode : childMode test .actual = .actual := by cases test <;> rfl
          rw [mode] at included
          exact schema_restrict schemaValid included
      rw [node_weight]
      apply Nat.le_trans (Nat.add_le_add_left (sum_le _ _ each) _)
      have total : (List.ofFn fun index => (part index).encode.size).sum = size pieces :=
        congrArg List.sum (ofFn_index pieces length (fun pattern => pattern.encode.size))
      rw [total]
      exact bound

end Yulang.GeneralNominalCenteredHeadMatSchemaMass
