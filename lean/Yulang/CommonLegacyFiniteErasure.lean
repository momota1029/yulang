import Yulang.CommonLegacyRecordErasure
import Yulang.CommonDefaultRequired

/-! Finite presence erasure for constructing shared legacy witnesses. -/

namespace Yulang.CommonLegacyFiniteErasure

universe u
variable {Row : Type u}

abbrev NewTy (Row : Type u) := CommonFinite.Ty Row
abbrev OldTy (Row : Type u) := StructuralBase.Ty Row

def both : Option (OldTy Row) → Option (OldTy Row) → Option (OldTy Row)
  | some first, some last => some (.union first last)
  | _, _ => none

def either : Option (OldTy Row) → Option (OldTy Row) → Option (OldTy Row)
  | none, last => last
  | first, none => first
  | some first, some last => some (.inter first last)

def shape : NewTy Row → Bool
  | .bottom | .emptyRecord | .exactEmpty | .record _ _ _ | .recordDefault _ _ _ => true
  | .union first last => shape first && shape last
  | .inter first last => shape first || shape last
  | .mask _ source => shape source
  | _ => false

def presence (hidden : List Nat) (label : Nat) : NewTy Row → Bool
  | .bottom => true
  | .union first last => presence hidden label first && presence hidden label last
  | .inter first last => presence hidden label first || presence hidden label last
  | .mask more source => presence (hidden ++ more) label source
  | .record current _ rest =>
      if label = current ∧ current ∉ hidden then true else presence hidden label rest
  | .recordDefault current source _ =>
      if label = current ∧ current ∉ hidden then shape source else presence hidden label source
  | _ => false

mutual
  def erase (hidden : List Nat) : NewTy Row → OldTy Row
    | .base scalar => .base scalar
    | .bottom => .bottom
    | .top => .top
    | .union first last => .union (erase hidden first) (erase hidden last)
    | .inter first last => .inter (erase hidden first) (erase hidden last)
    | .pair first last => .pair (erase [] first) (erase [] last)
    | .emptyRecord | .exactEmpty => .emptyRecord
    | .record label payload rest =>
        if label ∈ hidden then CommonLegacyRecordErasure.recordView (erase hidden rest)
        else .record label (erase [] payload) (erase hidden rest)
    | .recordDefault label source fallback =>
        if label ∈ hidden then CommonLegacyRecordErasure.recordView (erase hidden source)
        else match optional hidden label source with
        | none => CommonLegacyRecordErasure.recordView (erase hidden source)
        | some payload => .record label
            (.union payload (if presence hidden label source then .bottom else erase [] fallback))
            (erase hidden source)
    | .variant label payload => .variant label (erase [] payload)
    | .arrow input incoming output outgoing =>
        .arrow (erase [] input) incoming (erase [] output) outgoing
    | .mask more source => erase (hidden ++ more) source

  def optional (hidden : List Nat) (label : Nat) : NewTy Row → Option (OldTy Row)
    | .bottom => some .bottom
    | .union first last => both (optional hidden label first) (optional hidden label last)
    | .inter first last => either (optional hidden label first) (optional hidden label last)
    | .mask more source => optional (hidden ++ more) label source
    | .emptyRecord => some .top
    | .exactEmpty => some (if label ∈ hidden then .top else .bottom)
    | .record current payload rest =>
        if label = current ∧ current ∉ hidden then some (erase [] payload)
        else some ((optional hidden label rest).getD .top)
    | .recordDefault current source fallback =>
        some ((if label = current ∧ current ∉ hidden then
          both (optional hidden label source)
            (some (if presence hidden label source then .bottom else erase [] fallback))
          else optional hidden label source).getD .top)
    | _ => none
end

open CommonFinite (MaskedProbeStep)

/-- Presence flags describe actual trivial-field observations, for arbitrary
finite types, masks, row relations, environments and argument comparisons. -/
theorem presence_exact (leRow : Row → Row → Prop) (env : CommonFinite.Environment Row)
    (argumentOrder : NewTy Row → NewTy Row → Prop)
    (type : NewTy Row) (hidden : List Nat) (label : Nat) :
    presence hidden label type = true ↔
      MaskedProbeStep leRow env argumentOrder hidden type (.field label .trivial) := by
  have shapeExact (type : NewTy Row) (hidden : List Nat) :
      shape type = true ↔ MaskedProbeStep leRow env argumentOrder hidden type .records := by
    induction type generalizing hidden <;>
      simp_all [shape, MaskedProbeStep]
    all_goals grind
  induction type generalizing hidden <;>
    simp_all [presence, MaskedProbeStep, CommonFinite.maskedProbeStep_trivial]
  case record => grind
  case recordDefault current source fallback ihs ihf =>
    split
    · rw [shapeExact, ← CommonDefaultRequired.optional_trivial_iff_records
        leRow env argumentOrder hidden source label]
    · rfl

def ProfileProbe (leRow : Row → Row → Prop) (env : ProducerContextual.Environment Row)
    (argumentOrder : OldTy Row → OldTy Row → Prop)
    (profile : Option (OldTy Row)) (obs : ProducerContextual.Observation Row) : Prop :=
  match profile with
  | none => False
  | some payload => ProducerContextual.ProbeStep leRow env argumentOrder payload obs

def domains : NewTy Row → List (NewTy Row)
  | .union first last | .inter first last | .pair first last |
      .record _ first last | .recordDefault _ first last => domains first ++ domains last
  | .variant _ payload | .mask _ payload => domains payload
  | .arrow input _ output _ => input :: (domains input ++ domains output)
  | _ => []

/-- Transport of finite observations when the negative tests agree. This
hypothesis belongs only to this transport lemma, not to source reflection. -/
theorem erase_probe (leRow : Row → Row → Prop)
    (newEnv : CommonFinite.Environment Row) (oldEnv : ProducerContextual.Environment Row)
    (newOrder : NewTy Row → NewTy Row → Prop) (oldOrder : OldTy Row → OldTy Row → Prop)
    (roles : newEnv.roles = oldEnv.roles)
    (type : NewTy Row)
    (arguments : ∀ name domain, domain ∈ domains type →
      (newOrder (newEnv.types name) domain ↔ oldOrder (oldEnv.types name) (erase [] domain)))
    (hidden : List Nat) (obs : ProducerContextual.Observation Row) :
    (ProducerContextual.ProbeStep leRow oldEnv oldOrder (erase hidden type) obs ↔
      MaskedProbeStep leRow newEnv newOrder hidden type
        (CommonFiniteEmbedding.embedObservation obs)) ∧
    (∀ label, ProfileProbe leRow oldEnv oldOrder (optional hidden label type) obs ↔
      MaskedProbeStep leRow newEnv newOrder hidden type
        (.optional label (CommonFiniteEmbedding.embedObservation obs))) := by
  have bothExact (p q : Option (OldTy Row)) (obs : ProducerContextual.Observation Row) :
      ProfileProbe leRow oldEnv oldOrder (both p q) obs ↔
        ProfileProbe leRow oldEnv oldOrder p obs ∧ ProfileProbe leRow oldEnv oldOrder q obs := by
    cases p <;> cases q <;>
      simp [both, ProfileProbe, ProducerContextual.probeStep_union]
  have eitherExact (p q : Option (OldTy Row)) (obs : ProducerContextual.Observation Row) :
      ProfileProbe leRow oldEnv oldOrder (either p q) obs ↔
        ProfileProbe leRow oldEnv oldOrder p obs ∨ ProfileProbe leRow oldEnv oldOrder q obs := by
    cases p <;> cases q <;>
      simp [either, ProfileProbe, ProducerContextual.probeStep_inter]
  have getDExact (p : Option (OldTy Row)) (obs : ProducerContextual.Observation Row) :
      ProducerContextual.ProbeStep leRow oldEnv oldOrder (p.getD .top) obs ↔
        ProfileProbe leRow oldEnv oldOrder p obs ∨ obs = .trivial := by
    cases p with
    | none => cases obs <;> simp [ProfileProbe, ProducerContextual.ProbeStep]
    | some payload =>
      simp only [Option.getD, ProfileProbe]
      constructor
      · exact Or.inl
      · rintro (accepted | rfl)
        · exact accepted
        · exact ProducerContextual.probeStep_trivial payload
  have embedTrivial (obs : ProducerContextual.Observation Row) :
      CommonFiniteEmbedding.embedObservation obs = .trivial ↔ obs = .trivial := by
    cases obs <;> simp [CommonFiniteEmbedding.embedObservation]
  have fieldOptional (type : NewTy Row) (hidden : List Nat) (label : Nat)
      (obs : CommonFinite.Observation Row) :
      MaskedProbeStep leRow newEnv newOrder hidden type (.field label obs) →
      MaskedProbeStep leRow newEnv newOrder hidden type (.optional label obs) := by
    induction type generalizing hidden <;> simp_all [MaskedProbeStep]
    all_goals try split <;> simp_all
    all_goals grind
  induction type generalizing hidden obs with
  | union first last ihf ihl =>
      have ihf := ihf (fun name domain member =>
        arguments name domain (List.mem_append_left _ member))
      have ihl := ihl (fun name domain member =>
        arguments name domain (List.mem_append_right _ member))
      constructor
      · simpa only [erase, ProducerContextual.probeStep_union, CommonFinite.maskedProbeStep_union] using
          and_congr (ihf hidden obs).1 (ihl hidden obs).1
      · intro label
        simpa only [optional, bothExact, CommonFinite.maskedProbeStep_union] using
          and_congr ((ihf hidden obs).2 label) ((ihl hidden obs).2 label)
  | inter first last ihf ihl =>
      have ihf := ihf (fun name domain member =>
        arguments name domain (List.mem_append_left _ member))
      have ihl := ihl (fun name domain member =>
        arguments name domain (List.mem_append_right _ member))
      constructor
      · simpa only [erase, ProducerContextual.probeStep_inter, CommonFinite.maskedProbeStep_inter] using
          or_congr (ihf hidden obs).1 (ihl hidden obs).1
      · intro label
        simpa only [optional, eitherExact, CommonFinite.maskedProbeStep_inter] using
          or_congr ((ihf hidden obs).2 label) ((ihl hidden obs).2 label)
  | mask more source ih =>
      simpa only [erase, optional, CommonFinite.maskedProbeStep_mask] using ih arguments (hidden ++ more) obs
  | pair first last ihf ihl =>
      have ihf := ihf (fun name domain member =>
        arguments name domain (List.mem_append_left _ member))
      have ihl := ihl (fun name domain member =>
        arguments name domain (List.mem_append_right _ member))
      cases obs <;> simp [erase, optional, ProfileProbe, ProducerContextual.ProbeStep,
        MaskedProbeStep, CommonFiniteEmbedding.embedObservation, roles, (ihf [] _).1, (ihl [] _).1]
  | variant label payload ih =>
      have ih := ih arguments
      cases obs <;> simp [erase, optional, ProfileProbe, ProducerContextual.ProbeStep,
        MaskedProbeStep, CommonFiniteEmbedding.embedObservation, roles, (ih [] _).1]
  | arrow input incoming output outgoing ihi iho =>
      have iho := iho (fun name domain member => arguments name domain
        (List.mem_cons_of_mem _ (List.mem_append_right _ member)))
      have inputArgs := fun name => arguments name input List.mem_cons_self
      cases obs <;> simp [erase, optional, ProfileProbe, ProducerContextual.ProbeStep,
        MaskedProbeStep, CommonFiniteEmbedding.embedObservation, roles, (iho [] _).1, inputArgs]
  | record current payload rest ihp ihr =>
      have ihp := ihp (fun name domain member =>
        arguments name domain (List.mem_append_left _ member))
      have ihr := ihr (fun name domain member =>
        arguments name domain (List.mem_append_right _ member))
      constructor
      · by_cases masked : current ∈ hidden
        · simp only [erase, ite_eq_left masked, CommonLegacyRecordErasure.recordView_probe]
          cases obs <;> simp [MaskedProbeStep, CommonFiniteEmbedding.embedObservation,
            masked, roles, (ihr hidden _).1]
        · simp only [erase, ite_eq_right masked]
          cases obs <;> simp [ProducerContextual.ProbeStep, MaskedProbeStep,
            CommonFiniteEmbedding.embedObservation, masked, roles, (ihp [] _).1, (ihr hidden _).1]
      · intro label
        simp only [optional]
        split
        · simpa [ProfileProbe, MaskedProbeStep, ‹label = current ∧ current ∉ hidden›] using (ihp [] obs).1
        · change ProducerContextual.ProbeStep leRow oldEnv oldOrder
            ((optional hidden label rest).getD .top) obs ↔ _
          rw [getDExact]
          simpa only [MaskedProbeStep, ‹¬(label = current ∧ current ∉ hidden)›,
            ↓reduceIte, embedTrivial] using or_congr ((ihr hidden obs).2 label) Iff.rfl
  | recordDefault current source fallback ihs ihf =>
      have ihs := ihs (fun name domain member =>
        arguments name domain (List.mem_append_left _ member))
      have ihf := ihf (fun name domain member =>
        arguments name domain (List.mem_append_right _ member))
      constructor
      · by_cases masked : current ∈ hidden
        · simp only [erase, ite_eq_left masked, CommonLegacyRecordErasure.recordView_probe]
          cases obs <;> simp [MaskedProbeStep, CommonFiniteEmbedding.embedObservation,
            masked, roles, (ihs hidden _).1]
        · simp only [erase, ite_eq_right masked]
          cases extracted : optional hidden current source with
          | none =>
              simp only [CommonLegacyRecordErasure.recordView_probe]
              cases obs <;> simp [MaskedProbeStep, CommonFiniteEmbedding.embedObservation,
                roles, masked, (ihs hidden _).1]
              case field label obs =>
                by_cases same : label = current
                · subst label
                  have absent := (ihs hidden obs).2 current
                  simp only [extracted, ProfileProbe, false_iff] at absent
                  simp [absent]
                  exact fun accepted => absent (fieldOptional source hidden current _ accepted)
                · simp [same]
          | some payload =>
              cases obs <;> simp [ProducerContextual.ProbeStep, MaskedProbeStep,
                CommonFiniteEmbedding.embedObservation, roles, masked, (ihs hidden _).1]
              case field label obs =>
                by_cases same : label = current
                · subst label
                  have optionalExact := (ihs hidden obs).2 current
                  simp only [extracted, ProfileProbe] at optionalExact
                  simp only [↓reduceIte, optionalExact]
                  cases present : presence hidden current source <;>
                    simp [present, (ihf [] obs).1,
                      ← presence_exact leRow newEnv newOrder source hidden current]
                · simp [same]
      · intro label
        change ProducerContextual.ProbeStep leRow oldEnv oldOrder
          ((if label = current ∧ current ∉ hidden then
            both (optional hidden label source)
              (some (if presence hidden label source then .bottom else erase [] fallback))
            else optional hidden label source).getD .top) obs ↔ _
        rw [getDExact]
        by_cases active : label = current ∧ current ∉ hidden
        · rw [ite_eq_left active, bothExact]
          have equal : label = current := active.1
          subst label
          change (ProfileProbe leRow oldEnv oldOrder (optional hidden current source) obs ∧
            ProducerContextual.ProbeStep leRow oldEnv oldOrder
              (if presence hidden current source then .bottom else erase [] fallback) obs) ∨
            obs = .trivial ↔ _
          rw [(ihs hidden obs).2 current]
          cases present : presence hidden current source <;>
            simp [MaskedProbeStep, active, present,
              (ihf [] obs).1, embedTrivial,
              ← presence_exact leRow newEnv newOrder source hidden current]
        · simpa only [active, ↓reduceIte, MaskedProbeStep, embedTrivial] using
            or_congr ((ihs hidden obs).2 label) Iff.rfl
  | exactEmpty =>
      cases obs <;> simp [erase, optional, ProfileProbe, ProducerContextual.ProbeStep,
        MaskedProbeStep, CommonFiniteEmbedding.embedObservation, roles]
      all_goals intro label; split <;> simp_all [ProducerContextual.ProbeStep]
  | base | bottom | top | emptyRecord =>
      cases obs <;> simp [erase, optional, ProfileProbe, ProducerContextual.ProbeStep,
        MaskedProbeStep, CommonFiniteEmbedding.embedObservation, roles]

def meet : List (NewTy Row) → NewTy Row
  | [] => .top
  | first :: rest => .inter first (meet rest)

open CommonFiniteEmbedding (NewCompare OldCompare)

/-- One-way monotonicity of erasure at every finite negative rank. No
agreement premise or restriction on intermediate finite types remains. -/
theorem erase_compare (leRow : Row → Row → Prop) (rank : Nat)
    (source target : NewTy Row) (below : NewCompare leRow rank source target) :
    OldCompare leRow rank (erase [] source) (erase [] target) := by
  classical
  induction rank generalizing source target with
  | zero =>
      intro env obs accepted
      let newEnv : CommonFinite.Environment Row := ⟨fun _ => .bottom, env.roles⟩
      have transport (type : NewTy Row) := (erase_probe leRow newEnv env
        (fun _ _ => True) (fun _ _ => True) rfl type (fun _ _ _ => Iff.rfl) [] obs).1
      exact (transport source).mpr
        (below newEnv (CommonFiniteEmbedding.embedObservation obs) ((transport target).mp accepted))
  | succ rank ih =>
      have meetBelow (types : List (NewTy Row)) (type : NewTy Row) (member : type ∈ types) :
          NewCompare leRow rank (meet types) type := by
        induction types with
        | nil => cases member
        | cons first rest before =>
          intro env obs accepted
          apply (CommonFinite.probeAt_inter rank first (meet rest) obs).mpr
          rcases List.mem_cons.mp member with rfl | member
          · exact Or.inl accepted
          · exact Or.inr (before member env obs accepted)
      have belowEraseMeet (types : List (NewTy Row)) (parameter : OldTy Row)
          (bounded : ∀ type ∈ types, OldCompare leRow rank parameter (erase [] type)) :
          OldCompare leRow rank parameter (erase [] (meet types)) := by
        induction types with
        | nil =>
          intro env obs accepted
          cases rank <;> cases obs <;>
            simp_all [meet, erase, ProducerContextual.ProbeAt, ProducerContextual.ProbeStep]
        | cons first rest before =>
          have firstBelow := bounded first List.mem_cons_self
          have restBelow := before (fun type member => bounded type (List.mem_cons_of_mem _ member))
          intro env obs accepted
          change ProducerContextual.ProbeAt leRow rank env (.inter (erase [] first) (erase [] (meet rest))) obs at accepted
          exact ((ProducerContextual.probeAt_inter rank _ _ obs).mp accepted).elim
            (firstBelow env obs) (restBelow env obs)
      intro env obs accepted
      let tests := domains source ++ domains target
      let selected (name : Nat) := tests.filter fun type =>
        decide (OldCompare leRow rank (env.types name) (erase [] type))
      let newEnv : CommonFinite.Environment Row := ⟨fun name => meet (selected name), env.roles⟩
      have arguments (name : Nat) (domain : NewTy Row) (member : domain ∈ tests) :
          NewCompare leRow rank (newEnv.types name) domain ↔
            OldCompare leRow rank (env.types name) (erase [] domain) := by
        constructor
        · intro actual
          have parameterBelow := belowEraseMeet (selected name) (env.types name)
            (fun type included => of_decide_eq_true (List.mem_filter.mp included).2)
          have reflected := ih _ _ actual
          exact fun next obs held => parameterBelow next obs (reflected next obs held)
        · intro actual
          exact meetBelow (selected name) domain
            (List.mem_filter.mpr ⟨member, by simpa using actual⟩)
      have sourceTransport := (erase_probe leRow newEnv env
        (NewCompare leRow rank) (OldCompare leRow rank) rfl source
        (fun name domain member => arguments name domain (List.mem_append_left _ member)) [] obs).1
      have targetTransport := (erase_probe leRow newEnv env
        (NewCompare leRow rank) (OldCompare leRow rank) rfl target
        (fun name domain member => arguments name domain (List.mem_append_right _ member)) [] obs).1
      exact sourceTransport.mpr
        (below newEnv (CommonFiniteEmbedding.embedObservation obs) (targetTransport.mp accepted))

end Yulang.CommonLegacyFiniteErasure
