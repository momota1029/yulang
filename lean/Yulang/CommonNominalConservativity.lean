import Yulang.CommonNominalEmbedding

/-!
# Old demand order in arbitrary extended negative environments

At each negative rank, a finite family of old arrow inputs is observed. For
an arbitrary extended parameter, intersect exactly those old inputs above it.
This single old witness realizes all comparisons in that family simultaneously.
The induction uses the previous rank's conservativity, not a restriction of
extended parameters or an added assumption on solved instances.
-/

namespace Yulang.CommonNominalConservativity

abbrev Row := Common.Row
abbrev Old := CommonFinite.Ty Row
abbrev New := CommonNominalFinite.Ty Row
abbrev embed := @CommonNominalEmbedding.finite Row
abbrev OldLe (rank : Nat) := CommonFinite.ProducerLeAt Common.rowLe rank
abbrev NewLe (rank : Nat) := CommonNominalFinite.ProducerLeAt Common.rowLe rank

private def meet : List Old → Old
  | [] => .top
  | head :: tail => .inter head (meet tail)

private theorem new_trans {rank : Nat} {a b c : New}
    (first : NewLe rank a b) (last : NewLe rank b c) : NewLe rank a c :=
  fun env demand accepted => first env demand (last env demand accepted)

private theorem new_top (rank : Nat) (type : New) : NewLe rank type .top := by
  apply (CommonNominalFinite.producerLeAt_iff_probe _ _ _).mpr
  intro env obs accepted
  cases rank <;> cases obs <;>
    simp_all [CommonNominalFinite.ProbeAt, CommonNominalFinite.ProbeStep,
      CommonNominalFinite.MaskedProbeStep]

private theorem new_meet (rank : Nat) (type : New) (inputs : List Old) :
    NewLe rank type (embed (meet inputs)) ↔ ∀ input ∈ inputs, NewLe rank type (embed input) := by
  induction inputs with
  | nil => simp only [meet, CommonNominalEmbedding.finite, List.not_mem_nil, false_implies,
      forall_const, iff_true]; exact new_top rank type
  | cons head tail ih =>
      change NewLe rank type (.inter (embed head) (embed (meet tail))) ↔ _
      have split : NewLe rank type (.inter (embed head) (embed (meet tail))) ↔
          NewLe rank type (embed head) ∧ NewLe rank type (embed (meet tail)) := by
        simp only [NewLe, CommonNominalFinite.producerLeAt_iff_probe,
          CommonNominalFinite.probeAt_inter, or_imp, forall_and]
      rw [split, ih]
      simp

private theorem old_meet_member (rank : Nat) (inputs : List Old) (input : Old)
    (present : input ∈ inputs) : OldLe rank (meet inputs) input := by
  apply (CommonFinite.producerLeAt_iff_probe _ _ _).mpr
  intro env obs accepted
  induction inputs with
  | nil => cases present
  | cons head tail ih =>
      change CommonFinite.ProbeAt Common.rowLe rank env (.inter head (meet tail)) obs
      apply (CommonFinite.probeAt_inter _ _ _ _).mpr
      rcases List.mem_cons.mp present with rfl | later
      · exact Or.inl accepted
      · exact Or.inr (ih later)

private noncomputable def witness (rank : Nat) (parameter : New) (inputs : List Old) : Old := by
  classical
  exact meet (inputs.filter fun input => decide (NewLe rank parameter (embed input)))

/-- One old witness, shared across every input in the whole finite family. -/
private theorem witness_exact (rank : Nat)
    (previous : ∀ first last : Old, NewLe rank (embed first) (embed last) ↔ OldLe rank first last)
    (parameter : New) (inputs : List Old) (input : Old) (present : input ∈ inputs) :
    NewLe rank parameter (embed input) ↔ OldLe rank (witness rank parameter inputs) input := by
  classical
  let selected := inputs.filter fun input => decide (NewLe rank parameter (embed input))
  have below : NewLe rank parameter (embed (witness rank parameter inputs)) := by
    apply (new_meet rank parameter selected).mpr
    intro chosen member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  constructor
  · intro accepted
    exact old_meet_member rank selected input (List.mem_filter.mpr ⟨present, by simp [accepted]⟩)
  · intro accepted
    exact new_trans below ((previous _ _).mpr accepted)

end Yulang.CommonNominalConservativity
