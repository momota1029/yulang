import Yulang.GeneralDeclarativeInlineOrigins331
import Yulang.CommonNominalFullModel

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlineTwoOwners331
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction backed_iff from_completed)
open GeneralDeclarativeLowerKnown321 (Alias Knows knows_alias knows_row)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeInlineOrigins331 (fromOrigins complete exact_uses allocation_origins)
open GeneralDeclarativeOpaqueNominal328 (point)
open GeneralDeclarativeInlineMaterial331 (ordinary)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty pair record emptyRecord)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)

abbrev payload : Expr := .primitive .pair [.variable 3,.variable 4]
abbrev terminal : Expr := .primitive .emptyRecord []
abbrev raw : Expr := .record 7 payload terminal
abbrev pattern : Expr := .record 7 (.variable 0) (.variable 1)
abbrev aliasRow : Equation := ⟨0,.variable 1⟩
abbrev recordRow : Equation := ⟨1,raw⟩
abbrev table : State := ⟨⟨[],[]⟩,[aliasRow,recordRow]⟩
abbrev uses : List Occurrence := [⟨0,.actual,payload⟩,⟨1,.actual,terminal⟩]

def support (done : Nat → Prop) : Supported table done :=
  ⟨fun e o => (e = aliasRow ∧ o = .output 21) ∨ (e = recordRow ∧ o = .output 22),by
    rintro e o (⟨rfl,_⟩|⟨rfl,_⟩)
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self⟩

theorem stored_alias (done : Nat → Prop) (known : done 21) :
    aliasRow ∈ (restriction (support done)).equations :=
  from_completed (support done) (.inl ⟨rfl,rfl⟩) known

theorem stored_record (done : Nat → Prop) (known : done 22) :
    recordRow ∈ (restriction (support done)).equations :=
  from_completed (support done) (.inr ⟨rfl,rfl⟩) known

theorem raw_read (done : Nat → Prop) (aliasDone : done 21) (recordDone : done 22) :
    Read (restriction (support done)) .actual (.variable 0) pattern uses :=
  .record (raw := [(7,payload)]) (terminal := terminal) (keys := [7]) (selected := [(7,payload)])
    (.name (.inline (.forward (stored_alias done aliasDone)) .width (stored_record done recordDone)))
    (by decide) (by decide) rfl (.cons .capture .nil) .binder .capture

theorem alias_only_after (done : Nat → Prop) (unsettled : ¬done 21) {a b : Nat}
    (h : Alias (restriction (support done)) a b) : a = b := by
  have noExplicit {a b : Nat} (seen : (⟨a,.variable b⟩ : Equation) ∈ (restriction (support done)).equations) :
      False := by
    obtain ⟨actual,origin,active⟩ := (backed_iff _ _).mp seen
    rcases origin with ⟨_,rfl⟩|⟨wrong,_⟩
    · cases active with
      | completed yes => exact unsettled yes
    · cases congrArg Equation.right wrong
  have equality_by_bounds {x y}
      (h : GeneralDeclarativeBounds319.Bound (restriction (support done)).normal x y) : x = y := by
    induction h with
    | refl => rfl
    | interval h => cases h
    | constraint h => cases h
    | trans _ _ e f => exact e.trans f
  induction h with
  | bounds a _ => exact equality_by_bounds a
  | forward seen => exact False.elim (noExplicit seen)
  | backward seen => exact False.elim (noExplicit seen)
  | trans _ _ x y => exact x.trans y

/-- Both original owners are necessary for lower-known in this
example, despite the identical ordinary constraint/equation table. -/
theorem lower_exact (done : Nat → Prop) :
    (∃ tag, Knows (restriction (support done)) 0 tag) ↔ done 21 ∧ done 22 := by
  constructor
  · rintro ⟨tag,row,seen,link,constructor⟩
    obtain ⟨o,origin,active⟩ := (backed_iff _ _).mp seen
    rcases origin with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · cases constructor
    · cases active with
      | completed yes =>
        exact ⟨Classical.byContradiction (fun no => by cases (alias_only_after done no link)),yes⟩
  · rintro ⟨first,last⟩
    exact ⟨_,knows_alias (.forward (stored_alias done first)) (knows_row (stored_record done last) rfl)⟩

def required : List (Equation × GeneralDeclarativeOrigins321.Origin) :=
  [(aliasRow,.output 21),(recordRow,.output 22)]

theorem exact_old_requirements (done : Nat → Prop) :
    fromOrigins (support done) required ∧ (complete done required ↔ done 21 ∧ done 22) := by
  constructor
  · intro e h
    rcases List.mem_cons.mp h with rfl|other
    · exact .inl ⟨rfl,rfl⟩
    · cases List.mem_singleton.mp other
      exact .inr ⟨rfl,rfl⟩
  · exact ⟨fun h => ⟨h 21 List.mem_cons_self,h 22 (List.mem_cons_of_mem _ List.mem_cons_self)⟩,
      fun h _ seen => by
        change _ ∈ [21,22] at seen
        rcases List.mem_cons.mp seen with rfl|later
        · exact h.1
        · cases List.mem_singleton.mp later
          exact h.2⟩

theorem both_needed_for_fixed_read (done : Nat → Prop) (ready : complete done required) :
    Read (restriction (support done)) .actual (.variable 0) pattern uses := by
  obtain ⟨first,last⟩ := (exact_old_requirements done).2.mp ready
  exact raw_read done first last

abbrev int := GeneralDeclarativeExampleSource320.int
abbrev bool : Ty := .base .bool
abbrev whole : Ty := record 7 (pair int bool) emptyRecord
def model : Assignment := fun n =>
  (if n = 0 ∨ n = 1 then whole else if n = 4 then bool else int,Common.rowEmpty)

theorem ordinary_satisfies : Models table model := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,fun _ h => False.elim (List.not_mem_nil h)⟩,?_⟩
  intro e row
  change e ∈ [aliasRow,recordRow] at row
  rcases List.mem_cons.mp row with rfl|tail
  · exact eqv_refl _
  · cases List.mem_singleton.mp tail
    exact eqv_refl _

end Yulang.GeneralDeclarativeInlineTwoOwners331
