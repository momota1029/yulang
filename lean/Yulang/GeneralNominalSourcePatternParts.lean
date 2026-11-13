import Yulang.GeneralNominalGroundForests

/-! Successful closed query children retain source Pattern witnesses.
Record sorting preserves payload provenance; nominal keys are never guessed. -/
namespace Yulang.GeneralNominalSourcePatternParts
open GeneralDeclarationPatterns GeneralNominalInspection
open GeneralNominalOriginTerms GeneralNominalCompoundReadback

inductive Part : Pattern → Pattern → Prop
  | refl : Part pattern pattern
  | argument : child ∈ arguments → Part child part → Part (.app key arguments) part
  | payload : Part payload part → Part (.record label payload tail) part
  | tail : Part tail part → Part (.record label payload tail) part
  | variant : Part payload part → Part (.variant tag payload) part
  | first : Part first part → Part (.join first last) part
  | last : Part last part → Part (.join first last) part

theorem part_trans (one : Part first middle) (two : Part middle last) : Part first last := by
  induction one with
  | refl => exact two
  | argument member _ ih => exact .argument member (ih two)
  | payload _ ih => exact .payload (ih two)
  | tail _ ih => exact .tail (ih two)
  | variant _ ih => exact .variant (ih two)
  | first _ ih => exact .first (ih two)
  | last _ ih => exact .last (ih two)

def queryChildren : Query → List Query
  | .node _ children | .nominal _ children => children
  | _ => []

theorem child_source (pattern : Pattern)
    (present : child ∈ queryChildren (translate constructors interpretation pattern))
    (closed : ∀ names, child ≠ .variables names) :
    ∃ part, Part pattern part ∧ translate constructors interpretation part = child := by
  cases pattern with
  | var | join => simp only [translate,queryChildren,List.not_mem_nil] at present
  | variant tag payload =>
    simp only [translate,queryChildren] at present
    have equal := List.mem_singleton.mp present
    split at equal
    · exact False.elim (closed _ equal)
    · exact ⟨payload,.variant .refl,equal.symm⟩
  | app key arguments =>
    rw [translate.eq_def] at present
    dsimp only at present
    split at present
    · cases present
    · cases present
    · cases present
    · simp only [queryChildren,List.mem_cons,List.not_mem_nil,or_false] at present
      rcases present with one | two
      · exact ⟨_,.argument (List.mem_cons_self ..) .refl,one.symm⟩
      · exact ⟨_,.argument (List.mem_cons_of_mem _ (List.mem_singleton_self _)) .refl,two.symm⟩
    · split at present
      · split at present
        · obtain ⟨part,_,equal⟩ := List.mem_map.mp present
          exact ⟨part.val,.argument part.property .refl,equal⟩
        · cases present
      · cases present
  | record label payload tail =>
    simp only [translate] at present
    split at present
    · rename_i labels children tailQuery
      obtain ⟨field,member,equal⟩ := List.mem_map.mp present
      have member := List.mem_mergeSort.mp member
      rcases List.mem_cons.mp member with first | later
      · subst field
        exact ⟨payload,.payload .refl,equal⟩
      · have childMember : child ∈ children := equal ▸ (List.of_mem_zip later).2
        have nested : child ∈ queryChildren (translate constructors interpretation tail) := by
          rw [tailQuery]; exact childMember
        obtain ⟨part,path,translated⟩ := child_source tail nested closed
        exact ⟨part,.tail path,translated⟩
    · cases present
  termination_by sizeOf pattern

theorem closed_quote_nonvariable (term : Expr Nat) (closed : term.leaves = []) :
    ∀ names, quote term ≠ .variables names := by
  cases term with
  | leaf name => simp [Expr.leaves] at closed
  | node test children => cases test <;> intro names equal <;> cases equal

theorem closed_child_source (pattern : Pattern) (test : GeneralNominalRecursiveInspection.Test)
    (children : Fin (arity test) → Expr Nat)
    (translated : translate constructors interpretation pattern = quote (.node test children))
    (closed : (Expr.node test children).leaves = []) (index : Fin (arity test)) :
    ∃ part, Part pattern part ∧ translate constructors interpretation part = quote (children index) := by
  have childClosed : (children index).leaves = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro name member
    have parent : name ∈ (Expr.node test children).leaves := by
      simp only [Expr.leaves,List.mem_flatten,List.mem_ofFn]
      exact ⟨_,⟨index,rfl⟩,member⟩
    rw [closed] at parent
    cases parent
  apply child_source pattern _ (closed_quote_nonvariable _ childClosed)
  rw [translated]
  cases test with
  | scalar base => exact Fin.elim0 index
  | structural shape => exact List.mem_ofFn.mpr ⟨index,rfl⟩
  | nominal name count => exact List.mem_ofFn.mpr ⟨index,rfl⟩

theorem followed_source (path : GeneralNominalFiniteMeaning.Follows root term endpoint part)
    (translated : translate constructors interpretation pattern = quote term)
    (closed : term.leaves = []) :
    ∃ source, Part pattern source ∧ translate constructors interpretation source = quote part := by
  induction path with
  | root => exact ⟨pattern,.refl,translated⟩
  | child test children index prior ih =>
    obtain ⟨source,member,meaning⟩ := ih
    obtain ⟨sub,subpart,submeaning⟩ := closed_child_source source test children meaning
      (GeneralNominalFiniteMeaning.followed_closed prior closed) index
    exact ⟨sub,part_trans member subpart,submeaning⟩

end Yulang.GeneralNominalSourcePatternParts
