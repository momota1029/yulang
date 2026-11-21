import Yulang.GeneralDeclarativeInlineCompiler331
import Yulang.GeneralDeclarativeRecordConsumption330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlineLineage331
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeInlineSpine331 (Closed)
open GeneralDeclarativeInlineTrace331 (Read Args Fields)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeOrderedRecord326 (order)
open GeneralDeclarativeRecordMaterial330 (tailExpr)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleCanonicalRows (normalize)

/-- An actual structural reach from an original term. The only
rule that reads a named RHS uses a row from this source view.
Record accesses carry the exact canonical order and never traverse
a shadowed payload as though it had been selected. -/
inductive Trail (s : State) : Expr → Expr → Prop where
  | self : Trail s term term
  | step : Trail s first mid → Trail s mid last → Trail s first last
  | expose : Alias s n owner → (⟨owner,raw⟩ : Equation) ∈ s.equations →
    Trail s (.variable n) raw
  | primitive : term ∈ args → Trail s (.primitive tag args) term
  | nominal : term ∈ args → Trail s (.nominal tag args) term
  | variant : Trail s (.variant key one) one
  | joinLeft : Trail s (.join a b) a
  | joinRight : Trail s (.join a b) b
  | selected : Closed s term raw terminal → order (normalize raw) keys = some selected →
    (key,value) ∈ selected → Trail s term value
  | residual : Closed s term raw terminal → order (normalize raw) keys = some selected →
    Trail s term (tailExpr raw keys terminal)

theorem carries {s : State} (known : Read s mode raw code seen) :
    ∀ o ∈ seen, Trail s raw o.term := by
  refine Read.rec
    (motive_1 := fun _ raw _ seen _ => ∀ o ∈ seen, Trail s raw o.term)
    (motive_2 := fun _ args _ seen _ => ∀ o ∈ seen, ∃ input ∈ args, Trail s input o.term)
    (motive_3 := fun _ fields _ seen _ => ∀ o ∈ seen, ∃ entry ∈ fields, Trail s entry.2 o.term)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ known
  · intro _ _ _ o member
    cases List.mem_singleton.mp member
    exact .self
  · intro _ _ _ _ _ _ _ link row _ carry o member
    exact .step (.expose link row) (carry o member)
  · intro _ _ _ _ _ _ carry o member
    obtain ⟨term,used,here⟩ := carry o member
    exact .step (.primitive used) here
  · intro _ _ _ _ _ _ carry o member
    obtain ⟨term,used,here⟩ := carry o member
    exact .step (.nominal used) here
  · intro _ _ _ _ _ _ carry o member
    exact .step .variant (carry o member)
  · intro _ _ _ _ _ _ _ _ _ lo hi o member
    rcases List.mem_append.mp member with fromLo|fromHi
    · exact .step .joinLeft (lo o fromLo)
    · exact .step .joinRight (hi o fromHi)
  · intro _ _ _ _ _ _ _ _ _ _ raw _ _ ordered _ _ _ hs ts o member
    rcases List.mem_append.mp member with head|tail
    · obtain ⟨⟨label,term⟩,there,carry⟩ := hs o head
      exact .step (.selected raw ordered there) carry
    · exact .step (.residual raw ordered) (ts o tail)
  · intro _ o member
    cases member
  · intro _ _ _ _ _ _ _ _ _ head tail o member
    rcases List.mem_append.mp member with one|other
    · exact ⟨_,List.mem_cons_self,head o one⟩
    · obtain ⟨term,used,there⟩ := tail o other
      exact ⟨term,List.mem_cons_of_mem _ used,there⟩
  · intro _ o member
    cases member
  · intro _ _ _ _ _ _ _ _ _ _ head tail o member
    rcases List.mem_append.mp member with one|other
    · exact ⟨_,List.mem_cons_self,head o one⟩
    · obtain ⟨entry,used,there⟩ := tail o other
      exact ⟨entry,List.mem_cons_of_mem _ used,there⟩

end Yulang.GeneralDeclarativeInlineLineage331
