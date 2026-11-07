import Yulang.CommonEffectArrowCover

/-! Finite inter-arrow inspection with independent domain, row and result
components. Choice in the negative domain stays inside constructor depth;
row components may select different family members. This is an exact
inspection stage, not elimination of the remaining depth cover. -/
namespace Yulang.CommonEffectArrowFamily
open Common (Ty Row rowLe)
open CommonFinite (ProbeAt ProducerLe)
open CommonEffectRankMonotonicity (Compare compare_refl compare_trans)
open CommonEffectLatticeUniversals (Read read_inter read_top_implies)
open CommonBoundCoalescing (meetTypes)

structure Arrow where
  input : Ty
  incoming : Row
  output : Ty
  outgoing : Row

def Arrow.type (arrow : Arrow) : Ty := Common.arrow arrow.input arrow.incoming arrow.output arrow.outgoing
def family (arrows : List Arrow) : Ty := meetTypes (arrows.map Arrow.type)

theorem read_top (depth rank : Nat) (env : CommonFinite.Environment Row) (obs : CommonFinite.Observation Row) :
    Read depth rank env obs .top ↔ obs = .trivial := by
  change ProbeAt Common.rowLe rank env .top obs ↔ _
  cases rank <;> cases obs <;> simp [ProbeAt, CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]

theorem family_read (arrows : List Arrow) (depth rank : Nat) (env : CommonFinite.Environment Row)
    (obs : CommonFinite.Observation Row) (nontrivial : obs ≠ .trivial) :
    Read depth rank env obs (family arrows) ↔ ∃ arrow ∈ arrows, Read depth rank env obs arrow.type := by
  induction arrows with
  | nil => simp [family, meetTypes, read_top, nontrivial]
  | cons arrow rest ih =>
    exact (read_inter depth rank env obs arrow.type (family rest)).trans
      ((or_congr Iff.rfl ih).trans (by simp only [List.mem_cons, exists_eq_or_imp]))

theorem arrow_argument (arrow : Arrow) (depth rank : Nat) (env : CommonFinite.Environment Row) (name : Nat) :
    Read (depth + 1) (rank + 1) env (.arrowArgument name) arrow.type ↔
      Compare rank (env.types name) (Common.observeTy depth arrow.input) := Iff.rfl

theorem arrow_input_row (arrow : Arrow) (depth rank : Nat) (env : CommonFinite.Environment Row) (expected : Row) :
    Read depth rank env (.arrowInputRow expected) arrow.type ↔ rowLe expected arrow.incoming := by
  cases rank <;> rfl

theorem arrow_output_row (arrow : Arrow) (depth rank : Nat) (env : CommonFinite.Environment Row) (expected : Row) :
    Read depth rank env (.arrowOutputRow expected) arrow.type ↔ rowLe arrow.outgoing expected := by
  cases rank <;> rfl

theorem arrow_result (arrow : Arrow) (depth rank : Nat) (env : CommonFinite.Environment Row) (obs : CommonFinite.Observation Row) :
    Read (depth + 1) rank env (.arrowResult obs) arrow.type ↔ Read depth rank env obs arrow.output := by
  cases rank <;> rfl

def Components (arrows : List Arrow) (target : Arrow) : Prop :=
  CommonEffectArrowCover.Covers (arrows.map Arrow.input) target.input ∧
  (∃ arrow ∈ arrows, rowLe target.incoming arrow.incoming) ∧
  Common.Subtype (meetTypes (arrows.map Arrow.output)) target.output ∧
  (∃ arrow ∈ arrows, rowLe arrow.outgoing target.outgoing)

theorem subtype_components (arrows : List Arrow) (target : Arrow) (below : Common.Subtype (family arrows) target.type) :
    Components arrows target := by
  let emptyEnv : CommonFinite.Environment Row := ⟨fun _ => .bottom, fun _ => []⟩
  have domainCover : CommonEffectArrowCover.Covers (arrows.map Arrow.input) target.input := by
    intro depth
    let pairs := arrows.map (fun arrow => (Common.observeTy depth target.input, Common.observeTy depth arrow.input))
    have eachRank : ∀ rank, ∃ pair ∈ pairs, Compare rank pair.1 pair.2 := by
      intro rank
      let env : CommonFinite.Environment Row := ⟨fun _ => Common.observeTy depth target.input, fun _ => []⟩
      have accepted : Read (depth + 1) (rank + 1) env (.arrowArgument 0) target.type := compare_refl rank _
      have readFamily := (CommonFinite.producerLe_iff_probe _ _).mp (below (depth + 1)) (rank + 1) env (.arrowArgument 0) accepted
      obtain ⟨arrow, member, accepted⟩ := (family_read arrows (depth + 1) (rank + 1) env (.arrowArgument 0) (by intro h; cases h)).mp readFamily
      exact ⟨(Common.observeTy depth target.input, Common.observeTy depth arrow.input), List.mem_map.mpr ⟨arrow, member, rfl⟩, accepted⟩
    obtain ⟨pair, member, accepted⟩ := (CommonEffectRankCompactness.finite_rank_exact pairs).mp eachRank
    obtain ⟨arrow, present, rfl⟩ := List.mem_map.mp member
    exact ⟨arrow.input, List.mem_map.mpr ⟨arrow, present, rfl⟩, accepted⟩
  have inputRows : ∃ arrow ∈ arrows, rowLe target.incoming arrow.incoming := by
    have accepted := (arrow_input_row target 0 0 emptyEnv target.incoming).mpr (Common.rowLe_refl _)
    have readFamily := (CommonFinite.producerLe_iff_probe _ _).mp (below 0) 0 emptyEnv (.arrowInputRow target.incoming) accepted
    obtain ⟨arrow, member, accepted⟩ := (family_read arrows 0 0 emptyEnv (.arrowInputRow target.incoming) (by intro h; cases h)).mp readFamily
    exact ⟨arrow, member, (arrow_input_row arrow 0 0 emptyEnv target.incoming).mp accepted⟩
  have outputs : Common.Subtype (meetTypes (arrows.map Arrow.output)) target.output := by
    intro depth
    apply (CommonFinite.producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    have readTarget := (arrow_result target depth rank env obs).mpr accepted
    have readFamily := (CommonFinite.producerLe_iff_probe _ _).mp (below (depth + 1)) rank env (.arrowResult obs) readTarget
    obtain ⟨arrow, member, accepted⟩ := (family_read arrows (depth + 1) rank env (.arrowResult obs) (by intro h; cases h)).mp readFamily
    exact (CommonFinite.producerLe_iff_probe _ _).mp
      (CommonBoundCoalescing.meetTypes_le_member (List.mem_map.mpr ⟨arrow, member, rfl⟩) depth) rank env obs
      ((arrow_result arrow depth rank env obs).mp accepted)
  have outputRows : ∃ arrow ∈ arrows, rowLe arrow.outgoing target.outgoing := by
    have accepted := (arrow_output_row target 0 0 emptyEnv target.outgoing).mpr (Common.rowLe_refl _)
    have readFamily := (CommonFinite.producerLe_iff_probe _ _).mp (below 0) 0 emptyEnv (.arrowOutputRow target.outgoing) accepted
    obtain ⟨arrow, member, accepted⟩ := (family_read arrows 0 0 emptyEnv (.arrowOutputRow target.outgoing) (by intro h; cases h)).mp readFamily
    exact ⟨arrow, member, (arrow_output_row arrow 0 0 emptyEnv target.outgoing).mp accepted⟩
  exact ⟨domainCover, inputRows, outputs, outputRows⟩

theorem meet_read_member (types : List Ty) (nonempty : types ≠ []) (depth rank : Nat)
    (env : CommonFinite.Environment Row) (obs : CommonFinite.Observation Row)
    (accepted : Read depth rank env obs (meetTypes types)) : ∃ type ∈ types, Read depth rank env obs type := by
  induction types with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest ih =>
    rcases (read_inter depth rank env obs first (meetTypes rest)).mp accepted with firstRead | restRead
    · exact ⟨first, List.mem_cons_self, firstRead⟩
    · by_cases empty : rest = []
      · subst rest
        exact ⟨first, List.mem_cons_self, read_top_implies depth rank env obs first restRead⟩
      · obtain ⟨type, member, typeRead⟩ := ih empty restRead
        exact ⟨type, List.mem_cons_of_mem _ member, typeRead⟩

theorem components_subtype (arrows : List Arrow) (target : Arrow) (components : Components arrows target) :
    Common.Subtype (family arrows) target.type := by
  obtain ⟨cover, ⟨anchor, anchorMember, incoming⟩, outputs, ⟨outArrow, outMember, outgoing⟩⟩ := components
  have outputNonempty : arrows.map Arrow.output ≠ [] := by
    intro empty
    have member : anchor.output ∈ arrows.map Arrow.output := List.mem_map.mpr ⟨anchor, anchorMember, rfl⟩
    rw [empty] at member
    cases member
  intro depth
  apply (CommonFinite.producerLe_iff_probe _ _).mpr
  intro rank env obs accepted
  cases obs with
  | trivial => exact CommonFinite.probeAt_trivial rank _
  | impossible | base | records | pairFirst | pairLast | field | optional | variant =>
    cases rank <;> exact False.elim accepted
  | role name =>
    apply (family_read arrows depth rank env (.role name) (by intro h; cases h)).mpr
    refine ⟨anchor, anchorMember, ?_⟩
    cases rank <;> exact accepted
  | arrowInputRow expected =>
    apply (family_read arrows depth rank env (.arrowInputRow expected) (by intro h; cases h)).mpr
    exact ⟨anchor, anchorMember, (arrow_input_row anchor depth rank env expected).mpr
      (Common.rowLe_trans ((arrow_input_row target depth rank env expected).mp accepted) incoming)⟩
  | arrowOutputRow expected =>
    apply (family_read arrows depth rank env (.arrowOutputRow expected) (by intro h; cases h)).mpr
    exact ⟨outArrow, outMember, (arrow_output_row outArrow depth rank env expected).mpr
      (Common.rowLe_trans outgoing ((arrow_output_row target depth rank env expected).mp accepted))⟩
  | arrowArgument name =>
    apply (family_read arrows depth rank env (.arrowArgument name) (by intro h; cases h)).mpr
    cases depth with
    | zero =>
      refine ⟨anchor, anchorMember, ?_⟩
      cases rank <;> exact accepted
    | succ depth =>
      obtain ⟨input, member, bounded⟩ := cover depth
      obtain ⟨arrow, arrowMember, rfl⟩ := List.mem_map.mp member
      refine ⟨arrow, arrowMember, ?_⟩
      cases rank with
      | zero => trivial
      | succ rank =>
        have wanted := (arrow_argument target depth rank env name).mp accepted
        have domainBelow : Compare rank (Common.observeTy depth target.input) (Common.observeTy depth arrow.input) :=
          (CommonFinite.producerLe_iff_probe _ _).mp bounded rank
        exact (arrow_argument arrow depth rank env name).mpr (compare_trans rank wanted domainBelow)
  | arrowResult obs =>
    apply (family_read arrows depth rank env (.arrowResult obs) (by intro h; cases h)).mpr
    cases depth with
    | zero =>
      refine ⟨anchor, anchorMember, ?_⟩
      cases rank with
      | zero => exact CommonFinite.probeAt_bottom 0 obs
      | succ rank => exact CommonFinite.probeAt_bottom (rank + 1) obs
    | succ depth =>
      have wanted := (arrow_result target depth rank env obs).mp accepted
      have resultsRead := (CommonFinite.producerLe_iff_probe _ _).mp (outputs depth) rank env obs wanted
      obtain ⟨type, member, resultRead⟩ := meet_read_member (arrows.map Arrow.output) outputNonempty depth rank env obs resultsRead
      obtain ⟨arrow, arrowMember, rfl⟩ := List.mem_map.mp member
      exact ⟨arrow, arrowMember, (arrow_result arrow depth rank env obs).mpr resultRead⟩

theorem family_subtype_exact (arrows : List Arrow) (target : Arrow) :
    Common.Subtype (family arrows) target.type ↔ Components arrows target :=
  ⟨subtype_components arrows target, components_subtype arrows target⟩

end Yulang.CommonEffectArrowFamily
