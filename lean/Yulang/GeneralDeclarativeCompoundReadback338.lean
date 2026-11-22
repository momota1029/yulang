import Yulang.GeneralDeclarativeCompoundRoutes338

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCompoundReadback338
open CommonRoleCanonicalRows (normalize normalize_unique residual)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeEndpointProgram336 (Projection fields fields_exact ready)
open GeneralDeclarativeEndpointOverlay336 (Entry)
open GeneralDeclarativeExactSupport337 (endpointRows)
open GeneralDeclarativeCompoundBatch338 (Ticket minted authored_row)
open GeneralDeclarativeCompoundRoutes338 (key dispatch dispatch_exact)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeOrderedRecord326 (exact_order)
open CommonRoleOutermostResolver (All₂)

def operandLow : Projection → GeneralNominalCenteredHeadMatExpressions.Expr
  | .field _ _ a _ | .rest _ _ a _ => a

def operandHigh : Projection → GeneralNominalCenteredHeadMatExpressions.Expr
  | .field _ _ _ b | .rest _ _ _ b => b

theorem stored_low (e : Entry) : (⟨e.2.lower,operandLow e.1⟩ : Equation) ∈ endpointRows e := by
  rcases e with ⟨route,capture⟩
  cases route <;> exact List.mem_cons_self

theorem stored_high (e : Entry) : (⟨e.2.upper,operandHigh e.1⟩ : Equation) ∈ endpointRows e := by
  rcases e with ⟨route,capture⟩
  cases route <;> exact List.mem_cons_of_mem _ List.mem_cons_self

theorem actual_recipe {s : State} {p : Supported s done} (ticket : Ticket p arg fs)
    (listed : e ∈ minted s old keep ticket.jobs) :
    (∃ label a b, e.1 = .field arg label a b ∧
      (label,a) ∈ normalize ticket.lower ∧ (label,b) ∈ normalize ticket.upper) ∨
    e.1 = .rest arg (GeneralDeclarativeCompoundPattern338.layout fs |>.map Prod.fst)
      (withTail (residual (GeneralDeclarativeCompoundPattern338.layout fs |>.map Prod.fst)
        (normalize ticket.lower)) ticket.loEnd)
      (withTail (residual (GeneralDeclarativeCompoundPattern338.layout fs |>.map Prod.fst)
        (normalize ticket.upper)) ticket.hiEnd) := by
  obtain ⟨⟨j,idx⟩,inZip,rfl⟩ := List.mem_map.mp listed
  have job := List.fst_mem_of_mem_zipIdx inZip
  cases computed : fields arg (GeneralDeclarativeCompoundPattern338.layout fs) ticket.first ticket.last with
  | none =>
    have burned := ticket.calculated
    simp [ready,computed] at burned
  | some front =>
    have eq := Option.some.inj (by simpa [ready,computed] using ticket.calculated)
    rw [← eq] at job
    rcases List.mem_append.mp job with field|tail
    · obtain ⟨k,a,b,route,left,right⟩ := (fields_exact computed).2 _ field
      exact .inl ⟨k,a,b,route,
        ((exact_order (normalize_unique _) ticket.read.displayedLow).2 _ |>.mp left).1,
        ((exact_order (normalize_unique _) ticket.read.displayedHigh).2 _ |>.mp right).1⟩
    · cases List.mem_singleton.mp tail
      exact .inr rfl

theorem field_recipe {s : State} {p : Supported s done} (ticket : Ticket p arg fs)
    (listed : e ∈ minted s old keep ticket.jobs) (chosen : key e.1 = some label) :
    (label,operandLow e.1) ∈ normalize ticket.lower ∧
      (label,operandHigh e.1) ∈ normalize ticket.upper := by
  rcases actual_recipe ticket listed with ⟨k,a,b,route,left,right⟩|ending
  · rw [route] at chosen ⊢
    change some k = some label at chosen
    cases Option.some.inj chosen
    exact ⟨left,right⟩
  · rw [ending] at chosen
    cases chosen

theorem tail_recipe {s : State} {p : Supported s done} (ticket : Ticket p arg fs)
    (listed : e ∈ minted s old keep ticket.jobs) (chosen : key e.1 = none) :
    operandLow e.1 = withTail (residual (fs.map Prod.fst) (normalize ticket.lower)) ticket.loEnd ∧
      operandHigh e.1 = withTail (residual (fs.map Prod.fst) (normalize ticket.upper)) ticket.hiEnd := by
  rcases actual_recipe ticket listed with ⟨k,a,b,route,left,right⟩|ending
  · rw [route] at chosen
    cases chosen
  · rw [ending]
    simp only [operandLow,operandHigh,GeneralDeclarativeCompoundPattern338.layout_labels, and_self]

theorem aligned_field {task : Entry × GeneralDeclarationPatterns.Pattern}
    (aligned : All₂ (fun (task : Entry × GeneralDeclarationPatterns.Pattern) (field : Nat × GeneralDeclarationPatterns.Pattern) =>
      task.2 = field.2 ∧ key task.1.1 = some field.1) tasks fs) (active : task ∈ tasks) :
    ∃ field ∈ fs, task.2 = field.2 ∧ key task.1.1 = some field.1 := by
  induction aligned with
  | nil => cases active
  | cons matchHere _ later =>
    rcases List.mem_cons.mp active with rfl|tail
    · exact ⟨_,List.mem_cons_self,matchHere⟩
    · obtain ⟨e,listed,check⟩ := later tail
      exact ⟨e,List.mem_cons_of_mem _ listed,check⟩

theorem child_operands {s : State} {p : Supported s done} (ticket : Ticket p arg fs)
    (routed : dispatch fs (minted s old keep ticket.jobs) = some (tasks,tail))
    (active : task ∈ tasks) :
    ∃ field ∈ fs, task.2 = field.2 ∧
      (field.1,operandLow task.1.1) ∈ normalize ticket.lower ∧
      (field.1,operandHigh task.1.1) ∈ normalize ticket.upper := by
  obtain ⟨_,split,aligned,_⟩ := dispatch_exact routed
  have part : task.1 ∈ minted s old keep ticket.jobs := by
    rw [split]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨task,active,rfl⟩)
  obtain ⟨field,used,same,keyOf⟩ := aligned_field aligned active
  exact ⟨field,used,same,field_recipe ticket part keyOf⟩

end Yulang.GeneralDeclarativeCompoundReadback338
