import Yulang.CommonEffectArrowFamily
import Yulang.CommonPresenceConstraintGraph

/-! Finite shared-reference syntax for inter-arrow inspection. Depth cover,
incoming alternatives, output intersection and outgoing alternatives are
explicit finite components. No whole-source subtype or Typing predicate is
stored as an atom; no remaining component is claimed solved. -/
namespace Yulang.CommonEffectArrowInspection
open Common (Ty Row Equivalent Subtype)
open CommonBoundCoalescing (meetTypes)

structure Arrow (Rows Node : Type) where
  input : Node
  incoming : Rows
  output : Node
  outgoing : Rows

def Arrow.eval (rows : Rows → Row) (values : Node → Ty) (arrow : Arrow Rows Node) : CommonEffectArrowFamily.Arrow :=
  ⟨values arrow.input, rows arrow.incoming, values arrow.output, rows arrow.outgoing⟩

structure Output (Rows Node : Type) where
  domains : List Node
  input : Node
  incoming : Rows
  incomingCandidates : List Rows
  results : List Node
  result : Node
  outgoingCandidates : List Rows
  outgoing : Rows

def inspect (arrows : List (Arrow Rows Node)) (target : Arrow Rows Node) : Output Rows Node :=
  ⟨arrows.map Arrow.input, target.input, target.incoming, arrows.map Arrow.incoming,
    arrows.map Arrow.output, target.output, arrows.map Arrow.outgoing, target.outgoing⟩

def Output.Holds (rows : Rows → Row) (values : Node → Ty) (output : Output Rows Node) : Prop :=
  CommonEffectArrowCover.Covers (output.domains.map values) (values output.input) ∧
  (∃ incoming ∈ output.incomingCandidates, Common.rowLe (rows output.incoming) (rows incoming)) ∧
  Subtype (meetTypes (output.results.map values)) (values output.result) ∧
  (∃ outgoing ∈ output.outgoingCandidates, Common.rowLe (rows outgoing) (rows output.outgoing))

theorem exists_map (entries : List α) (map : α → β) (property : β → Prop) :
    (∃ value ∈ entries.map map, property value) ↔ ∃ entry ∈ entries, property (map entry) := by
  constructor
  · rintro ⟨value, member, accepted⟩
    obtain ⟨entry, listed, rfl⟩ := List.mem_map.mp member
    exact ⟨entry, listed, accepted⟩
  · rintro ⟨entry, member, accepted⟩
    exact ⟨map entry, List.mem_map.mpr ⟨entry, member, rfl⟩, accepted⟩

theorem inspect_exact (arrows : List (Arrow Rows Node)) (target : Arrow Rows Node)
    (rows : Rows → Row) (values : Node → Ty) :
    (inspect arrows target).Holds rows values ↔
      Subtype (CommonEffectArrowFamily.family (arrows.map (Arrow.eval rows values))) (target.eval rows values).type := by
  simpa only [Output.Holds, inspect, CommonEffectArrowFamily.Components, List.map_map, Function.comp_def,
    Arrow.eval, exists_map] using (CommonEffectArrowFamily.family_subtype_exact
      (arrows.map (Arrow.eval rows values)) (target.eval rows values)).symm

theorem meet_append (first last : List Ty) :
    Equivalent (meetTypes (first ++ last)) (.inter (meetTypes first) (meetTypes last)) := by
  have before : Subtype (meetTypes (first ++ last)) (meetTypes first) :=
    (CommonBoundCoalescing.le_meetTypes_iff _ _).mpr (fun type member =>
      CommonBoundCoalescing.meetTypes_le_member (List.mem_append_left _ member))
  have after : Subtype (meetTypes (first ++ last)) (meetTypes last) :=
    (CommonBoundCoalescing.le_meetTypes_iff _ _).mpr (fun type member =>
      CommonBoundCoalescing.meetTypes_le_member (List.mem_append_right _ member))
  refine ⟨(Common.common_inter_is_meet _ _ _).mpr ⟨before, after⟩, ?_⟩
  apply (CommonBoundCoalescing.le_meetTypes_iff _ _).mpr
  intro type member
  rcases List.mem_append.mp member with member | member
  · exact Common.subtype_trans (CommonBoundCoalescing.inter_le_left _ _) (CommonBoundCoalescing.meetTypes_le_member member)
  · exact Common.subtype_trans (CommonBoundCoalescing.inter_le_right _ _) (CommonBoundCoalescing.meetTypes_le_member member)

theorem family_append (first last : List CommonEffectArrowFamily.Arrow) :
    Equivalent (CommonEffectArrowFamily.family (first ++ last))
      (.inter (CommonEffectArrowFamily.family first) (CommonEffectArrowFamily.family last)) := by
  simpa only [CommonEffectArrowFamily.family, List.map_append] using
    meet_append (first.map CommonEffectArrowFamily.Arrow.type) (last.map CommonEffectArrowFamily.Arrow.type)

theorem family_singleton (arrow : CommonEffectArrowFamily.Arrow) :
    Equivalent (CommonEffectArrowFamily.family [arrow]) arrow.type := by
  refine ⟨CommonBoundCoalescing.meetTypes_le_member (List.mem_singleton_self _), ?_⟩
  exact (CommonBoundCoalescing.le_meetTypes_iff _ _).mpr (fun type member => by
    have same : type = arrow.type := List.mem_singleton.mp member
    exact same ▸ Common.subtype_refl arrow.type)

open Core.PresenceGeneration (TyTerm RowTerm)
open PresenceOpenTailGenerationLowering (Pool subterms)
open CommonPresenceConstraintGraph (Realizes rowEval lowerNode realizes_reference)

abbrev PoolArrow (pool : Pool inputs) := Arrow (RowTerm (Fin inputs)) (Fin pool.size)

def arrowNode (pool : Pool inputs) (input result : TyTerm (Fin inputs)) (incoming outgoing : RowTerm (Fin inputs))
    (member : .arrow input incoming result outgoing ∈ pool.terms) : PoolArrow pool :=
  ⟨pool.child _ member input (by simp [subterms]), incoming,
    pool.child _ member result (by simp [subterms]), outgoing⟩

def extract (pool : Pool inputs) : (source : TyTerm (Fin inputs)) → source ∈ pool.terms → Option (List (PoolArrow pool))
  | .top, _ => some []
  | .inter first last, member => do
      let before ← extract pool first (pool.closed _ member first (by simp [subterms]))
      let after ← extract pool last (pool.closed _ member last (by simp [subterms]))
      pure (before ++ after)
  | .arrow input incoming result outgoing, member => some [arrowNode pool input result incoming outgoing member]
  | _, _ => none

theorem arrowNode_exact (pool : Pool inputs) (input result : TyTerm (Fin inputs)) (incoming outgoing : RowTerm (Fin inputs))
    (member : .arrow input incoming result outgoing ∈ pool.terms) (rows : Fin inputs → Row) (values : Fin pool.size → Ty)
    (realizes : Realizes pool rows values) :
    Equivalent (values (pool.reference (.arrow input incoming result outgoing) member))
      ((arrowNode pool input result incoming outgoing member).eval (rowEval rows) values).type := by
  exact Common.equivalent_symm (realizes_reference pool rows values realizes _ member)

theorem extract_exact (pool : Pool inputs) (source : TyTerm (Fin inputs)) (member : source ∈ pool.terms)
    (arrows : List (PoolArrow pool)) (found : extract pool source member = some arrows)
    (rows : Fin inputs → Row) (values : Fin pool.size → Ty) (realizes : Realizes pool rows values) :
    Equivalent (values (pool.reference source member))
      (CommonEffectArrowFamily.family (arrows.map (Arrow.eval (rowEval rows) values))) := by
  induction source generalizing arrows with
  | top =>
    have same : arrows = [] := (Option.some.inj found).symm
    subst arrows
    exact Common.equivalent_symm (realizes_reference pool rows values realizes _ member)
  | arrow input incoming result outgoing =>
    have same : arrows = [arrowNode pool input result incoming outgoing member] := (Option.some.inj found).symm
    subst arrows
    exact Common.equivalent_trans (arrowNode_exact pool input result incoming outgoing member rows values realizes)
      (Common.equivalent_symm (family_singleton _))
  | inter first last iha ihb =>
    cases beforeFound : extract pool first (pool.closed _ member first (by simp [subterms])) with
    | none => simp [extract, beforeFound] at found
    | some before =>
      cases afterFound : extract pool last (pool.closed _ member last (by simp [subterms])) with
      | none => simp [extract, beforeFound, afterFound] at found
      | some after =>
        simp [extract, beforeFound, afterFound] at found
        subst arrows
        have beforeSame := iha _ before beforeFound
        have afterSame := ihb _ after afterFound
        have node := Common.equivalent_symm (realizes_reference pool rows values realizes _ member)
        have children : Equivalent
            ((lowerNode pool (.inter first last) member).eval rows values)
            (.inter (CommonEffectArrowFamily.family (before.map (Arrow.eval (rowEval rows) values)))
              (CommonEffectArrowFamily.family (after.map (Arrow.eval (rowEval rows) values)))) :=
          ⟨Common.common_inter_mono beforeSame.1 afterSame.1, Common.common_inter_mono beforeSame.2 afterSame.2⟩
        rw [List.map_append]
        exact Common.equivalent_trans (Common.equivalent_trans node children)
          (Common.equivalent_symm (family_append _ _))
  | _ => cases found

/-- Actual pool IDs and actual generated arrow/inter/top source syntax.
Only independent constructor equations are a semantic premise. -/
theorem inspect_collected_exact (pool : Pool inputs) (source : TyTerm (Fin inputs)) (sourceMember : source ∈ pool.terms)
    (arrows : List (PoolArrow pool)) (found : extract pool source sourceMember = some arrows)
    (input result : TyTerm (Fin inputs)) (incoming outgoing : RowTerm (Fin inputs))
    (targetMember : .arrow input incoming result outgoing ∈ pool.terms)
    (rows : Fin inputs → Row) (values : Fin pool.size → Ty) (realizes : Realizes pool rows values) :
    (inspect arrows (arrowNode pool input result incoming outgoing targetMember)).Holds (rowEval rows) values ↔
      Subtype (values (pool.reference source sourceMember)) (values (pool.reference (.arrow input incoming result outgoing) targetMember)) := by
  have sourceSame := extract_exact pool source sourceMember arrows found rows values realizes
  have targetSame := arrowNode_exact pool input result incoming outgoing targetMember rows values realizes
  constructor
  · intro accepted
    exact Common.subtype_trans sourceSame.1 (Common.subtype_trans
      ((inspect_exact arrows (arrowNode pool input result incoming outgoing targetMember) (rowEval rows) values).mp accepted) targetSame.2)
  · intro accepted
    apply (inspect_exact arrows (arrowNode pool input result incoming outgoing targetMember) (rowEval rows) values).mpr
    exact Common.subtype_trans sourceSame.2 (Common.subtype_trans accepted targetSame.1)

end Yulang.CommonEffectArrowInspection
