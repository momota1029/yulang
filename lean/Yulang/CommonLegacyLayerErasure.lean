import Yulang.CommonLegacyTruncation
import Yulang.CommonLegacyGraphSupport
import Yulang.CommonPayloadProjection

/-! Erasure of one regular layer, retaining finite payload expressions. -/

namespace Yulang.CommonLegacyLayerErasure

universe u v w
open CommonSyntax (Layer)
open CommonPayloadProjection (Payload Profile optionalProject)
open CommonDefaultRequired (fieldPresence recordShape)
open CommonLegacyGraphSupport (refs oldRefs)

def evalOld (values : Index → StructuralBase.Ty Row) : Payload Index → StructuralBase.Ty Row
  | .ref index => values index
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (evalOld values first) (evalOld values last)
  | .inter first last => .inter (evalOld values first) (evalOld values last)

def evalLayer (values : Index → RegularValueTypes.Layer Row Child) :
    Payload Index → RegularValueTypes.Layer Row Child
  | .ref index => values index
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (evalLayer values first) (evalLayer values last)
  | .inter first last => .inter (evalLayer values first) (evalLayer values last)

def payloadRefs : Payload Index → List Index
  | .ref index => [index]
  | .bottom | .top => []
  | .union first last | .inter first last => payloadRefs first ++ payloadRefs last

def recordView : RegularValueTypes.Layer Row (Payload Index) → RegularValueTypes.Layer Row (Payload Index)
  | .bottom => .record 0 .bottom .bottom
  | .union first last => .union (recordView first) (recordView last)
  | .inter first last => .inter (recordView first) (recordView last)
  | .record label payload rest => .record label payload rest
  | _ => .emptyRecord

def erase (hidden : List Nat) : Layer Row Index → RegularValueTypes.Layer Row (Payload Index)
  | .base scalar => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (erase hidden first) (erase hidden last)
  | .inter first last => .inter (erase hidden first) (erase hidden last)
  | .pair first last => .pair (.ref first) (.ref last)
  | .emptyRecord | .exactEmpty => .emptyRecord
  | .record label payload rest =>
      if label ∈ hidden then recordView (erase hidden rest)
      else .record label (.ref payload) (erase hidden rest)
  | .recordDefault label source fallback =>
      if label ∈ hidden then recordView (erase hidden source)
      else match optionalProject hidden label source with
      | none => recordView (erase hidden source)
      | some payload => .record label
          (.union payload (if fieldPresence hidden label source then .bottom else .ref fallback))
          (erase hidden source)
  | .variant label payload => .variant label (.ref payload)
  | .arrow input incoming output outgoing => .arrow (.ref input) incoming (.ref output) outgoing
  | .mask more source => erase (hidden ++ more) source

/-- At every positive observation depth, erasing a concrete finite layer
commutes literally with erasing all its children and evaluating its retained
payload expressions. The zero-depth default rule is deliberately excluded. -/
theorem eval_erasure (source : Layer Row Index) (depth : Nat)
    (values : Index → CommonFinite.Ty Row) (hidden : List Nat) :
    CommonLegacyFiniteErasure.erase hidden (source.evalAt (depth + 1) values) =
      (erase hidden source).eval
        (evalOld (fun index => CommonLegacyFiniteErasure.erase [] (values index))) := by
  have shapeExact (layer : Layer Row Index) :
      CommonLegacyFiniteErasure.shape (layer.evalAt (depth + 1) values) = recordShape layer := by
    induction layer <;> simp_all [Layer.evalAt, CommonLegacyFiniteErasure.shape, recordShape]
  have presenceExact (layer : Layer Row Index) (hidden : List Nat) (label : Nat) :
      CommonLegacyFiniteErasure.presence hidden label (layer.evalAt (depth + 1) values) =
        fieldPresence hidden label layer := by
    induction layer generalizing hidden <;>
      simp_all [Layer.evalAt, CommonLegacyFiniteErasure.presence, fieldPresence]
  let assignment := fun index => CommonLegacyFiniteErasure.erase [] (values index)
  have bothMap (p q : Profile Index) :
      CommonLegacyFiniteErasure.both (p.map (evalOld assignment)) (q.map (evalOld assignment)) =
        (Profile.both p q).map (evalOld assignment) := by
    cases p <;> cases q <;> rfl
  have eitherMap (p q : Profile Index) :
      CommonLegacyFiniteErasure.either (p.map (evalOld assignment)) (q.map (evalOld assignment)) =
        (Profile.either p q).map (evalOld assignment) := by
    cases p <;> cases q <;> rfl
  have trivialMap (p : Profile Index) :
      some ((p.map (evalOld assignment)).getD .top) =
        (Profile.withTrivial p).map (evalOld assignment) := by
    cases p <;> rfl
  have optionalExact (layer : Layer Row Index) (hidden : List Nat) (label : Nat) :
      CommonLegacyFiniteErasure.optional hidden label (layer.evalAt (depth + 1) values) =
        (optionalProject hidden label layer).map (evalOld assignment) := by
    induction layer generalizing hidden with
    | union first last ihf ihl =>
        simp [Layer.evalAt, CommonLegacyFiniteErasure.optional, optionalProject, ihf, ihl, bothMap]
    | inter first last ihf ihl =>
        simp [Layer.evalAt, CommonLegacyFiniteErasure.optional, optionalProject, ihf, ihl, eitherMap]
    | record label payload rest ih =>
        simp only [Layer.evalAt, CommonLegacyFiniteErasure.optional, optionalProject]
        split
        · rfl
        · rw [ih, trivialMap]
    | recordDefault current source fallback ih =>
        simp only [Layer.evalAt, CommonLegacyFiniteErasure.optional, optionalProject, presenceExact]
        split
        · rw [ih]
          cases fieldPresence hidden label source <;>
            cases optionalProject hidden label source <;> rfl
        · rw [ih, trivialMap]
    | exactEmpty =>
        simp only [Layer.evalAt, CommonLegacyFiniteErasure.optional, optionalProject]
        split <;> rfl
    | mask more source ih => exact ih (hidden ++ more)
    | _ => rfl
  have recordViewExact (layer : RegularValueTypes.Layer Row (Payload Index)) :
      (recordView layer).eval (evalOld assignment) =
        CommonLegacyRecordErasure.recordView (layer.eval (evalOld assignment)) := by
    induction layer <;> simp_all [recordView, RegularValueTypes.Layer.eval,
      CommonLegacyRecordErasure.recordView, evalOld]
  induction source generalizing hidden with
  | record label payload rest ih =>
      simp only [Layer.evalAt, CommonLegacyFiniteErasure.erase, erase]
      split
      · rw [recordViewExact, ih]
      · simp only [RegularValueTypes.Layer.eval, evalOld, ih]
  | recordDefault label source fallback ih =>
      simp only [Layer.evalAt, CommonLegacyFiniteErasure.erase, erase]
      split
      · rw [recordViewExact, ih]
      · rw [optionalExact]
        cases extracted : optionalProject hidden label source with
        | none =>
            simp only [Option.map_none]
            rw [recordViewExact, ih]
        | some payload =>
          simp only [Option.map_some, RegularValueTypes.Layer.eval, evalOld, presenceExact, ih]
          cases fieldPresence hidden label source <;> rfl
  | _ => simp_all [Layer.evalAt, CommonLegacyFiniteErasure.erase, erase,
      RegularValueTypes.Layer.eval, evalOld]

def Good (allowed : Index → Prop) (payload : Payload Index) : Prop :=
  ∀ index ∈ payloadRefs payload, allowed index

def GoodProfile (allowed : Index → Prop) (profile : Profile Index) : Prop :=
  ∀ payload, profile = some payload → Good allowed payload

def GoodLayer (allowed : Index → Prop) (layer : RegularValueTypes.Layer Row (Payload Index)) : Prop :=
  ∀ payload ∈ oldRefs layer, Good allowed payload

/-- Layer erasure and optional extraction introduce no references to new
source states. Every retained payload mentions only original children. -/
theorem erase_support (allowed : Index → Prop) (source : Layer Row Index)
    (supported : ∀ index ∈ refs source, allowed index) (hidden : List Nat) :
    GoodLayer allowed (erase hidden source) ∧
      ∀ label, GoodProfile allowed (optionalProject hidden label source) := by
  have bothGood (first last : Profile Index) :
      GoodProfile allowed first → GoodProfile allowed last → GoodProfile allowed (Profile.both first last) := by
    cases first <;> cases last <;>
      simp_all [GoodProfile, Good, payloadRefs, Profile.both] <;> grind
  have eitherGood (first last : Profile Index) :
      GoodProfile allowed first → GoodProfile allowed last → GoodProfile allowed (Profile.either first last) := by
    cases first <;> cases last <;>
      simp_all [GoodProfile, Good, payloadRefs, Profile.either] <;> grind
  have trivialGood (profile : Profile Index) :
      GoodProfile allowed profile → GoodProfile allowed (Profile.withTrivial profile) := by
    cases profile <;> simp [GoodProfile, Good, payloadRefs, Profile.withTrivial]
  have viewGood (layer : RegularValueTypes.Layer Row (Payload Index)) :
      GoodLayer allowed layer → GoodLayer allowed (recordView layer) := by
    induction layer <;>
      simp_all [GoodLayer, Good, recordView, oldRefs, CommonSyntax.ofOldLayer, refs, payloadRefs] <;> grind
  induction source generalizing hidden with
  | union first last ihf ihl =>
      obtain ⟨firstGood, firstOptional⟩ := ihf
        (fun index member => supported index (List.mem_append_left _ member)) hidden
      obtain ⟨lastGood, lastOptional⟩ := ihl
        (fun index member => supported index (List.mem_append_right _ member)) hidden
      constructor
      · intro payload member
        exact (List.mem_append.mp member).elim (firstGood payload) (lastGood payload)
      · exact fun label => bothGood _ _ (firstOptional label) (lastOptional label)
  | inter first last ihf ihl =>
      obtain ⟨firstGood, firstOptional⟩ := ihf
        (fun index member => supported index (List.mem_append_left _ member)) hidden
      obtain ⟨lastGood, lastOptional⟩ := ihl
        (fun index member => supported index (List.mem_append_right _ member)) hidden
      constructor
      · intro payload member
        exact (List.mem_append.mp member).elim (firstGood payload) (lastGood payload)
      · exact fun label => eitherGood _ _ (firstOptional label) (lastOptional label)
  | record current payload rest ih =>
      have payloadGood : allowed payload := supported payload List.mem_cons_self
      obtain ⟨restGood, restOptional⟩ := ih
        (fun index member => supported index (List.mem_cons_of_mem _ member)) hidden
      constructor
      · simp only [erase]
        split
        · exact viewGood _ restGood
        · simpa [GoodLayer, oldRefs, CommonSyntax.ofOldLayer, refs, Good, payloadRefs] using
            And.intro payloadGood restGood
      · intro label
        simp only [optionalProject]
        split
        · simpa [GoodProfile, Good, payloadRefs] using payloadGood
        · exact trivialGood _ (restOptional label)
  | recordDefault current source fallback ih =>
      have fallbackGood : allowed fallback := supported fallback (List.mem_append_right _ List.mem_cons_self)
      obtain ⟨sourceGood, sourceOptional⟩ := ih
        (fun index member => supported index (List.mem_append_left _ member)) hidden
      have chosenGood (label : Nat) : GoodProfile allowed
          (if fieldPresence hidden label source then some .bottom else some (.ref fallback)) := by
        split <;> simp_all [GoodProfile, Good, payloadRefs]
      constructor
      · simp only [erase]
        split
        · exact viewGood _ sourceGood
        · cases found : optionalProject hidden current source with
          | none => exact viewGood _ sourceGood
          | some payload =>
            have payloadGood := sourceOptional current payload found
            intro part member
            rcases List.mem_cons.mp member with rfl | member
            · intro index occurs
              rcases List.mem_append.mp occurs with before | after
              · exact payloadGood index before
              · cases present : fieldPresence hidden current source <;>
                  simp [present, payloadRefs] at after
                subst index
                exact fallbackGood
            · exact sourceGood part member
      · intro label
        simp only [optionalProject]
        apply trivialGood
        split
        · exact bothGood _ _ (sourceOptional label) (chosenGood label)
        · exact sourceOptional label
  | mask more source ih => exact ih supported (hidden ++ more)
  | exactEmpty =>
      simp only [erase, optionalProject]
      constructor
      · simp [GoodLayer, oldRefs, CommonSyntax.ofOldLayer, refs]
      · intro label
        split <;> simp [GoodProfile, Good, payloadRefs]
  | _ => simp_all [erase, optionalProject, GoodLayer, GoodProfile, Good, payloadRefs,
      oldRefs, CommonSyntax.ofOldLayer, refs] <;> grind

end Yulang.CommonLegacyLayerErasure
