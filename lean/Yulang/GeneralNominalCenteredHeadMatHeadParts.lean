import Yulang.GeneralNominalCenteredHeadMatHeadShape

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! Semantic one-level inversion supplies finite projection labels and charges
their whole size to the parent. It applies to every closed count-covered normalized label. -/
namespace Yulang.GeneralNominalCenteredHeadMatHeadParts
open GeneralDeclarationPatterns GeneralPatternNormalForm
open GeneralNominalCenteredHeadMatPatternSemantics
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra application)
open GeneralNominalCenteredHeadMatHeadShape
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalFiniteMeaning
open GeneralNominalReadbackFunctionality
open CommonNominalFullCarrier
variable {test : Test}

def cost : Test → Nat
  | .structural (.record keys) => keys.length + 1
  | _ => 1

def size (patterns : List Pattern) : Nat := (patterns.map fun p => p.encode.size).sum

def CompleteLabel (pattern : Pattern) : Prop := pattern.variables = [] ∧ Normal pattern

def realize (test : Test) (values : List Ty) : Ty :=
  match test with
  | .scalar base => .base base
  | .structural shape => shapeValue shape values
  | .nominal name _ => nominal name (values.map Sum.inl)

theorem evals_map (patterns : List Pattern) : evals semantics variables patterns = patterns.map (eval semantics variables) := by
  induction patterns with
  | nil => rfl
  | cons first rest ih => simp only [evals,List.map_cons,ih]

theorem encoded_size (patterns : List Pattern) : Roles.argsSize (encodeArgs patterns) = size patterns := by
  induction patterns with
  | nil => rfl
  | cons first rest ih => simpa only [encodeArgs,Roles.argsSize,size,List.map_cons,List.sum_cons] using congrArg (first.encode.size + ·) ih

theorem realize_build (length : values.length = arity test) :
    realize test values = build test (fun index => values[index.val]'(by rw [length]; exact index.isLt)) := by
  have rebuild : List.ofFn (fun index : Fin (arity test) => values[index.val]'(by rw [length]; exact index.isLt)) = values := by
    apply List.ext_getElem
    · simpa only [List.length_ofFn] using length.symm
    · intro index one two; simp only [List.getElem_ofFn]
  cases test <;> simp only [realize,build] at *
  · rw [rebuild]
  · have mapped := congrArg (List.map (fun value : Ty => (Sum.inl value : Argument))) rebuild
    simpa only [List.map_ofFn,Function.comp_def] using congrArg (nominal _) mapped.symm

def Parts (semantics : Algebra) (pattern : Pattern) (test : Test) : Prop :=
  ∃ pieces : List Pattern, pieces.length = arity test ∧
    (∀ piece ∈ pieces, CompleteLabel piece) ∧
    Equivalent (eval semantics (fun _ => .bottom) pattern)
      (realize test (pieces.map (eval semantics (fun _ => .bottom)))) ∧
    cost test + size pieces ≤ pattern.encode.size

theorem direct (canonical : TestCanonical test) (actual : Test) (actualCanonical : TestCanonical actual)
    (pieces : List Pattern) (length : pieces.length = arity actual)
    (complete : ∀ piece ∈ pieces, CompleteLabel piece)
    (equal : Equivalent (eval semantics (fun _ => .bottom) pattern)
      (realize actual (pieces.map (eval semantics (fun _ => .bottom)))))
    (bound : cost actual + size pieces ≤ pattern.encode.size)
    (valid : test.Holds (eval semantics (fun _ => .bottom) pattern)) : Parts semantics pattern test := by
  have same : test = actual := by
    have held := holds_congr equal valid
    rw [realize_build (by simpa only [List.length_map] using length)] at held
    exact holds_build canonical actualCanonical held
  subst test
  exact ⟨pieces,length,complete,equal,bound⟩

theorem arguments_complete (complete : CompleteLabel (.app key arguments)) :
    ∀ piece ∈ arguments, CompleteLabel piece := by
  simp only [CompleteLabel,Pattern.variables,Normal] at complete
  intro piece member
  refine ⟨?_,complete.2 piece member⟩
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name used
  have parent : name ∈ variablesArgs arguments := GeneralNominalCanonicalTemplates.argument_variables arguments piece member used
  rw [complete.1] at parent
  cases parent

theorem inversion (complete : CompleteLabel pattern) (canonical : TestCanonical test)
    (valid : test.Holds (eval (algebra constructors interpretation) (fun _ => .bottom) pattern)) :
    Parts (algebra constructors interpretation) pattern test := by
  cases pattern with
  | var name => cases complete.1
  | join =>
      have impossible := complete.2
      simp only [Normal] at impossible
  | variant tag payload =>
      apply direct canonical (.structural (.variant tag)) trivial [payload] rfl
      · intro piece member; cases List.mem_singleton.mp member; simpa only [CompleteLabel,Pattern.variables,Normal] using complete
      · exact eqv_refl _
      · simp only [cost,size,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
          Pattern.encode,Roles.Term.size,Roles.argsSize,Nat.add_zero]
        exact Nat.le_refl _
      · exact valid
  | app key arguments =>
      have parts := arguments_complete complete
      have bound : 1 + size arguments = (Pattern.app key arguments).encode.size := by
        simp only [Pattern.encode,Roles.Term.size,encoded_size]
      cases primitive : interpretation.primitives key with
      | none =>
          cases declared : constructors key with
          | none =>
              exact False.elim (bottom_no_head test (by simpa only [eval,algebra,application,primitive,declared] using valid))
          | some declaration =>
              apply direct canonical (.nominal declaration.name arguments.length) trivial arguments rfl parts
              · simp only [eval,algebra,application,primitive,declared,evals_map,realize]
                exact eqv_refl _
              · exact Nat.le_of_eq bound
              · exact valid
      | some primitiveValue =>
          cases primitiveValue with
          | scalar base =>
              cases arguments with
              | cons =>
                  exact False.elim (bottom_no_head test (by simpa only [eval,algebra,application,primitive,evals,
                    GeneralNominalCenteredHeadMatExpressions.primitiveValue] using valid))
              | nil =>
                  apply direct canonical (.scalar base) trivial [] rfl parts
                  · simp only [eval,algebra,application,primitive,evals,GeneralNominalCenteredHeadMatExpressions.primitiveValue,
                      List.map_nil,realize]
                    exact eqv_refl _
                  · exact Nat.le_refl _
                  · exact valid
          | emptyRecord =>
              cases arguments with
              | cons =>
                  exact False.elim (bottom_no_head test (by simpa only [eval,algebra,application,primitive,evals,
                    GeneralNominalCenteredHeadMatExpressions.primitiveValue] using valid))
              | nil =>
                  apply direct canonical (.structural (.record [])) (by simp [TestCanonical,GeneralNormalizedObservation.Shape.Canonical]) [] rfl parts
                  · simp only [eval,algebra,application,primitive,evals,GeneralNominalCenteredHeadMatExpressions.primitiveValue,
                      List.map_nil,realize]
                    exact eqv_refl _
                  · exact Nat.le_refl _
                  · exact valid
          | exactEmpty =>
              cases arguments with
              | cons =>
                  exact False.elim (bottom_no_head test (by simpa only [eval,algebra,application,primitive,evals,
                    GeneralNominalCenteredHeadMatExpressions.primitiveValue] using valid))
              | nil =>
                  apply direct canonical (.structural .exactEmpty) trivial [] rfl parts
                  · simp only [eval,algebra,application,primitive,evals,GeneralNominalCenteredHeadMatExpressions.primitiveValue,
                      List.map_nil,realize]
                    exact eqv_refl _
                  · exact Nat.le_refl _
                  · exact valid
          | pair =>
              cases arguments with
              | nil =>
                  exact False.elim (bottom_no_head test (by simpa only [eval,algebra,application,primitive,evals,
                    GeneralNominalCenteredHeadMatExpressions.primitiveValue] using valid))
              | cons first rest =>
                  cases rest with
                  | nil =>
                      exact False.elim (bottom_no_head test (by simpa only [eval,algebra,application,primitive,evals,
                        GeneralNominalCenteredHeadMatExpressions.primitiveValue] using valid))
                  | cons last rest =>
                      cases rest with
                      | cons =>
                          exact False.elim (bottom_no_head test (by simpa only [eval,algebra,application,primitive,evals,
                            GeneralNominalCenteredHeadMatExpressions.primitiveValue] using valid))
                      | nil =>
                          apply direct canonical (.structural .pair) trivial [first,last] rfl parts
                          · simp only [eval,algebra,application,primitive,evals,GeneralNominalCenteredHeadMatExpressions.primitiveValue,
                              List.map_cons,List.map_nil,realize]
                            exact eqv_refl _
                          · exact Nat.le_of_eq bound
                          · exact valid
  | record label payload rest =>
      obtain ⟨keys,rfl⟩ := record_head valid
      obtain ⟨values,length,equal⟩ := valid
      obtain ⟨pieces,pieceLength,pieceFacts,bound⟩ := GeneralNominalCenteredHeadMatRecordProjection.record_parts
        complete.1 complete.2 length canonical equal
      refine ⟨pieces,pieceLength,?_,?_,bound⟩
      · intro piece member
        obtain ⟨index,inside,same⟩ := List.mem_iff_getElem.mp member
        have facts := pieceFacts ⟨index,by omega⟩
        exact same ▸ ⟨facts.1,facts.2.1⟩
      · apply eqv_trans equal
        apply shape_congr
        intro index
        have one : index.val < values.length := by rw [length]; exact index.isLt
        have two : index.val < pieces.length := by rw [pieceLength]; exact index.isLt
        simpa only [List.getElem?_map,List.getElem?_eq_getElem one,List.getElem?_eq_getElem two,
          Option.map_some,Option.getD_some] using (pieceFacts index).2.2

end Yulang.GeneralNominalCenteredHeadMatHeadParts
