import Yulang.CommonLegacyFiniteErasure

/-! Constructor-depth truncation for legacy contextual comparisons. -/

namespace Yulang.CommonLegacyTruncation

universe u
variable {Row : Type u}

open StructuralBase (Ty)
open ProducerContextual (Environment Observation ProbeStep)
open CommonFiniteEmbedding (OldCompare)

def truncate (depth : Nat) : Ty Row → Ty Row
  | .base scalar => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (truncate depth first) (truncate depth last)
  | .inter first last => .inter (truncate depth first) (truncate depth last)
  | .emptyRecord => .emptyRecord
  | .pair first last => .pair
      (match depth with | 0 => .bottom | d + 1 => truncate d first)
      (match depth with | 0 => .bottom | d + 1 => truncate d last)
  | .record label payload rest => .record label
      (match depth with | 0 => .bottom | d + 1 => truncate d payload)
      (truncate depth rest)
  | .variant label payload => .variant label
      (match depth with | 0 => .bottom | d + 1 => truncate d payload)
  | .arrow input incoming output outgoing => .arrow
      (match depth with | 0 => .bottom | d + 1 => truncate d input) incoming
      (match depth with | 0 => .bottom | d + 1 => truncate d output) outgoing

def domains : Ty Row → List (Ty Row)
  | .union first last | .inter first last | .pair first last |
      .record _ first last => domains first ++ domains last
  | .variant _ payload => domains payload
  | .arrow input _ output _ => input :: (domains input ++ domains output)
  | _ => []

def remaining (depth : Nat) : Observation Row → Nat
  | .pairFirst obs | .pairLast obs | .field _ obs | .variant _ obs | .arrowResult obs =>
      remaining (depth - 1) obs
  | _ => depth

noncomputable def clip (env : Environment Row) (argumentOrder : Ty Row → Ty Row → Prop)
    (depth : Nat) (obs : Observation Row) : Observation Row := by
  classical
  exact match obs with
  | .pairFirst obs => .pairFirst (match depth with | 0 => .trivial | d + 1 => clip env argumentOrder d obs)
  | .pairLast obs => .pairLast (match depth with | 0 => .trivial | d + 1 => clip env argumentOrder d obs)
  | .field label obs => .field label (match depth with | 0 => .trivial | d + 1 => clip env argumentOrder d obs)
  | .variant label obs => .variant label (match depth with | 0 => .trivial | d + 1 => clip env argumentOrder d obs)
  | .arrowResult obs => .arrowResult (match depth with | 0 => .trivial | d + 1 => clip env argumentOrder d obs)
  | .arrowArgument name => match depth with
      | 0 => if argumentOrder (env.types name) .bottom then .arrowResult .trivial else .impossible
      | _ + 1 => .arrowArgument name
  | other => other

/-- A fixed observation reaches one common remaining constructor depth in
every compared type. Only its finite negative-domain tests need alignment. -/
theorem truncate_probe (leRow : Row → Row → Prop)
    (sourceEnv targetEnv : Environment Row)
    (sourceOrder targetOrder : Ty Row → Ty Row → Prop)
    (roles : sourceEnv.roles = targetEnv.roles)
    (type : Ty Row) (depth : Nat) (obs : Observation Row)
    (arguments : remaining depth obs ≠ 0 → ∀ name domain, domain ∈ domains type →
      (sourceOrder (sourceEnv.types name) domain ↔
        targetOrder (targetEnv.types name) (truncate (remaining depth obs - 1) domain))) :
    ProbeStep leRow targetEnv targetOrder (truncate depth type) obs ↔
      ProbeStep leRow sourceEnv sourceOrder type (clip targetEnv targetOrder depth obs) := by
  classical
  have clipTrivial (depth : Nat) (obs : Observation Row) :
      clip targetEnv targetOrder depth obs = .trivial ↔ obs = .trivial := by
    cases obs <;> cases depth <;> simp [clip]
    split <;> simp
  induction type generalizing depth obs with
  | union first last ihf ihl =>
      simp only [truncate, ProducerContextual.probeStep_union]
      exact and_congr
        (ihf depth obs (fun positive name domain member =>
          arguments positive name domain (List.mem_append_left _ member)))
        (ihl depth obs (fun positive name domain member =>
          arguments positive name domain (List.mem_append_right _ member)))
  | inter first last ihf ihl =>
      simp only [truncate, ProducerContextual.probeStep_inter]
      exact or_congr
        (ihf depth obs (fun positive name domain member =>
          arguments positive name domain (List.mem_append_left _ member)))
        (ihl depth obs (fun positive name domain member =>
          arguments positive name domain (List.mem_append_right _ member)))
  | pair first last ihf ihl =>
      have firstArgs := fun positive name domain member =>
        arguments positive name domain (List.mem_append_left _ member)
      have lastArgs := fun positive name domain member =>
        arguments positive name domain (List.mem_append_right _ member)
      cases obs <;> cases depth <;> simp [truncate, clip, ProbeStep, roles]
      all_goals first
        | exact ihf _ _ firstArgs
        | exact ihl _ _ lastArgs
        | (split <;> simp [ProbeStep])
  | variant label payload ih =>
      cases obs <;> cases depth <;> simp [truncate, clip, ProbeStep, roles]
      all_goals first
        | exact fun _ => ih _ _ arguments
        | (split <;> simp [ProbeStep])
  | record current payload rest ihp ihr =>
      have payloadArgs := fun positive name domain member =>
        arguments positive name domain (List.mem_append_left _ member)
      have restArgs := fun positive name domain member =>
        arguments positive name domain (List.mem_append_right _ member)
      cases obs <;> cases depth <;> simp [truncate, clip, ProbeStep, roles]
      all_goals first
        | (split <;> simp [ProbeStep])
        | skip
      case field.zero label obs =>
        exact imp_congr_right fun _ => ihr 0 (.field label obs) restArgs
      case field.succ label obs depth =>
        split
        · exact ihp depth obs payloadArgs
        · exact ihr (depth + 1) (.field label obs) restArgs
  | arrow input incoming output outgoing ihi iho =>
      have outputArgs := fun positive name domain member => arguments positive name domain
        (List.mem_cons_of_mem _ (List.mem_append_right _ member))
      cases obs <;> cases depth <;> simp [truncate, clip, ProbeStep, roles]
      case arrowArgument.zero name => split <;> simp_all [ProbeStep]
      case arrowArgument.succ name depth =>
        exact (arguments (by simp [remaining]) name input List.mem_cons_self).symm
      case arrowResult.succ obs depth => exact iho depth obs outputArgs
  | bottom => simp [truncate, ProducerContextual.probeStep_bottom]
  | top =>
      cases obs <;> cases depth <;> simp [truncate, clip, ProbeStep]
      split <;> simp [ProbeStep]
  | base | emptyRecord =>
      cases obs <;> cases depth <;> simp [truncate, clip, ProbeStep, roles]
      all_goals split <;> simp [ProbeStep]

/-- Every constructor-depth truncation preserves every finite-rank
contextual comparison. Rows and their relation are entirely arbitrary. -/
theorem truncate_compare (leRow : Row → Row → Prop) (rank depth : Nat)
    (source target : Ty Row) (below : OldCompare leRow rank source target) :
    OldCompare leRow rank (truncate depth source) (truncate depth target) := by
  classical
  induction rank generalizing depth source target with
  | zero =>
      intro env obs accepted
      have transport (type : Ty Row) := truncate_probe leRow env env
        (fun _ _ => True) (fun _ _ => True) rfl type depth obs (fun _ _ _ _ => Iff.rfl)
      exact (transport source).mpr
        (below env (clip env (fun _ _ => True) depth obs) ((transport target).mp accepted))
  | succ rank ih =>
      have meetBelow (types : List (Ty Row)) (type : Ty Row) (member : type ∈ types) :
          OldCompare leRow rank (CommonFiniteEmbedding.meet types) type := by
        induction types with
        | nil => cases member
        | cons first rest before =>
          intro env obs accepted
          apply (ProducerContextual.probeAt_inter rank first (CommonFiniteEmbedding.meet rest) obs).mpr
          rcases List.mem_cons.mp member with rfl | member
          · exact Or.inl accepted
          · exact Or.inr (before member env obs accepted)
      have belowTruncateMeet (types : List (Ty Row)) (parameter : Ty Row) (depth : Nat)
          (bounded : ∀ type ∈ types, OldCompare leRow rank parameter (truncate depth type)) :
          OldCompare leRow rank parameter (truncate depth (CommonFiniteEmbedding.meet types)) := by
        induction types with
        | nil =>
          intro env obs accepted
          cases rank <;> cases obs <;>
            simp_all [CommonFiniteEmbedding.meet, truncate, ProducerContextual.ProbeAt, ProbeStep]
        | cons first rest before =>
          have firstBelow := bounded first List.mem_cons_self
          have restBelow := before (fun type member => bounded type (List.mem_cons_of_mem _ member))
          intro env obs accepted
          change ProducerContextual.ProbeAt leRow rank env
            (.inter (truncate depth first) (truncate depth (CommonFiniteEmbedding.meet rest))) obs at accepted
          exact ((ProducerContextual.probeAt_inter rank _ _ obs).mp accepted).elim
            (firstBelow env obs) (restBelow env obs)
      intro env obs accepted
      by_cases exhausted : remaining depth obs = 0
      · have transport (type : Ty Row) := truncate_probe leRow env env
          (OldCompare leRow rank) (OldCompare leRow rank) rfl type depth obs
          (fun positive => False.elim (positive exhausted))
        exact (transport source).mpr
          (below env (clip env (OldCompare leRow rank) depth obs) ((transport target).mp accepted))
      · let tests := domains source ++ domains target
        let selected (name : Nat) := tests.filter fun type =>
          decide (OldCompare leRow rank (env.types name) (truncate (remaining depth obs - 1) type))
        let sourceEnv : Environment Row := ⟨fun name => CommonFiniteEmbedding.meet (selected name), env.roles⟩
        have arguments (name : Nat) (domain : Ty Row) (member : domain ∈ tests) :
            OldCompare leRow rank (sourceEnv.types name) domain ↔
              OldCompare leRow rank (env.types name) (truncate (remaining depth obs - 1) domain) := by
          constructor
          · intro actual
            have parameterBelow := belowTruncateMeet (selected name) (env.types name)
              (remaining depth obs - 1)
              (fun type included => of_decide_eq_true (List.mem_filter.mp included).2)
            have reflected := ih (remaining depth obs - 1) _ _ actual
            exact fun next obs held => parameterBelow next obs (reflected next obs held)
          · intro actual
            exact meetBelow (selected name) domain
              (List.mem_filter.mpr ⟨member, by simpa using actual⟩)
        have sourceTransport := truncate_probe leRow sourceEnv env
          (OldCompare leRow rank) (OldCompare leRow rank) rfl source depth obs
          (fun _ name domain member => arguments name domain (List.mem_append_left _ member))
        have targetTransport := truncate_probe leRow sourceEnv env
          (OldCompare leRow rank) (OldCompare leRow rank) rfl target depth obs
          (fun _ name domain member => arguments name domain (List.mem_append_right _ member))
        exact sourceTransport.mpr
          (below sourceEnv (clip env (OldCompare leRow rank) depth obs) (targetTransport.mp accepted))

end Yulang.CommonLegacyTruncation
