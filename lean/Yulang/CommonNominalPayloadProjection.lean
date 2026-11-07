import Yulang.CommonNominalDefaultRecord

/-!
# Executable field and optional-payload projections

A missing profile accepts no payload observation, including the trivial one.
A present profile is a finite lattice expression over the original guarded
payload references. This separates absence of a requirement from the top
payload type, whose trivial observation always holds.

Only the outer layer is inspected. Payload references are retained verbatim,
so regular blocks, negative arrow children and shared parameters are not
unfolded or restricted. The interpretation shifts exactly one constructor
depth, matching the selected field of a whole-record default.
-/

namespace Yulang.CommonNominalPayloadProjection

open CommonNominalSyntax (Layer)
open CommonNominalDefaultRequired (fieldPresence)

universe u v w

inductive Payload (Index : Type v) where
  | ref : Index → Payload Index
  | bottom : Payload Index
  | top : Payload Index
  | union : Payload Index → Payload Index → Payload Index
  | inter : Payload Index → Payload Index → Payload Index

namespace Payload

def evalFinite {Row : Type u} (assignment : Index → CommonNominalFinite.Ty Row) :
    Payload Index → CommonNominalFinite.Ty Row
  | .ref index => assignment index
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (evalFinite assignment first) (evalFinite assignment last)
  | .inter first last => .inter (evalFinite assignment first) (evalFinite assignment last)

def evalLayer {Row : Type u} {Child : Type w} (assignment : Index → Layer Row Child) :
    Payload Index → Layer Row Child
  | .ref index => assignment index
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (evalLayer assignment first) (evalLayer assignment last)
  | .inter first last => .inter (evalLayer assignment first) (evalLayer assignment last)

theorem evalAt_evalLayer {Row : Type u} {Child : Type w}
    (assignment : Index → Layer Row Child) (children : Child → CommonNominalFinite.Ty Row)
    (depth : Nat) (payload : Payload Index) :
    (payload.evalLayer assignment).evalAt depth children =
      payload.evalFinite (fun index => (assignment index).evalAt depth children) := by
  induction payload <;> simp_all [evalLayer, evalFinite, Layer.evalAt]

end Payload

abbrev Profile (Index : Type v) := Option (Payload Index)

namespace Profile

/-- Conjunction of payload tests, hence a union of producer payload types. -/
def both : Profile Index → Profile Index → Profile Index
  | some first, some last => some (.union first last)
  | _, _ => none

/-- Disjunction of payload tests, hence an intersection of producer types. -/
def either : Profile Index → Profile Index → Profile Index
  | none, last => last
  | first, none => first
  | some first, some last => some (.inter first last)

/-- A record constructor itself supplies the trivial optional observation. -/
def withTrivial : Profile Index → Profile Index
  | none => some .top
  | some payload => some payload

def Holds {Row : Type u} (leRow : Row → Row → Prop) (env : CommonNominalFinite.Environment Row)
    (argumentOrder : CommonNominalFinite.Ty Row → CommonNominalFinite.Ty Row → Prop)
    (assignment : Index → CommonNominalFinite.Ty Row) (profile : Profile Index)
    (obs : CommonNominalFinite.Observation Row) : Prop :=
  match profile with
  | none => False
  | some payload =>
      CommonNominalFinite.MaskedProbeStep leRow env argumentOrder [] (payload.evalFinite assignment) obs

variable {Row : Type u} (leRow : Row → Row → Prop) (env : CommonNominalFinite.Environment Row)
    (argumentOrder : CommonNominalFinite.Ty Row → CommonNominalFinite.Ty Row → Prop)
    (assignment : Index → CommonNominalFinite.Ty Row)

@[simp] theorem holds_both (first last : Profile Index) (obs : CommonNominalFinite.Observation Row) :
    Holds leRow env argumentOrder assignment (both first last) obs ↔
      Holds leRow env argumentOrder assignment first obs ∧
        Holds leRow env argumentOrder assignment last obs := by
  cases first <;> cases last <;>
    simp [both, Holds, Payload.evalFinite, CommonNominalFinite.maskedProbeStep_union]

@[simp] theorem holds_either (first last : Profile Index) (obs : CommonNominalFinite.Observation Row) :
    Holds leRow env argumentOrder assignment (either first last) obs ↔
      Holds leRow env argumentOrder assignment first obs ∨
        Holds leRow env argumentOrder assignment last obs := by
  cases first <;> cases last <;>
    simp [either, Holds, Payload.evalFinite, CommonNominalFinite.maskedProbeStep_inter]

@[simp] theorem holds_withTrivial (profile : Profile Index) (obs : CommonNominalFinite.Observation Row) :
    Holds leRow env argumentOrder assignment (withTrivial profile) obs ↔
      Holds leRow env argumentOrder assignment profile obs ∨ obs = .trivial := by
  cases profile with
  | none => cases obs <;> simp [withTrivial, Holds, Payload.evalFinite, CommonNominalFinite.MaskedProbeStep]
  | some payload =>
      simp only [withTrivial, Holds]
      constructor
      · exact Or.inl
      · rintro (accepted | rfl)
        · exact accepted
        · exact CommonNominalFinite.maskedProbeStep_trivial [] _

end Profile

/-- Finite outer inspection. Every retained reference is a proper payload
child, including the fallback of a nested default. -/
def optionalProject (hidden : List Nat) (label : Nat) : Layer Row Index → Profile Index
  | .bottom => some .bottom
  | .union first last =>
      Profile.both (optionalProject hidden label first) (optionalProject hidden label last)
  | .inter first last =>
      Profile.either (optionalProject hidden label first) (optionalProject hidden label last)
  | .mask more source => optionalProject (hidden ++ more) label source
  | .emptyRecord => some .top
  | .exactEmpty => if label ∈ hidden then some .top else some .bottom
  | .record current payload rest =>
      if label = current ∧ current ∉ hidden then some (.ref payload)
      else Profile.withTrivial (optionalProject hidden label rest)
  | .recordDefault current source fallback =>
      Profile.withTrivial
        (if label = current ∧ current ∉ hidden then
          Profile.both (optionalProject hidden label source)
            (if fieldPresence hidden label source then some .bottom else some (.ref fallback))
        else optionalProject hidden label source)
  | _ => none

def fieldProject (hidden : List Nat) (label : Nat) : Layer Row Index → Profile Index
  | .bottom => some .bottom
  | .union first last =>
      Profile.both (fieldProject hidden label first) (fieldProject hidden label last)
  | .inter first last =>
      Profile.either (fieldProject hidden label first) (fieldProject hidden label last)
  | .mask more source => fieldProject (hidden ++ more) label source
  | .record current payload rest =>
      if label = current ∧ current ∉ hidden then some (.ref payload)
      else fieldProject hidden label rest
  | .recordDefault current source fallback =>
      if label = current ∧ current ∉ hidden then
        Profile.both (optionalProject hidden label source)
          (if fieldPresence hidden label source then some .bottom else some (.ref fallback))
      else fieldProject hidden label source
  | _ => none

section Finite

variable {Row : Type u} {Index : Type v}
    (leRow : Row → Row → Prop) (env : CommonNominalFinite.Environment Row)
    (argumentOrder : CommonNominalFinite.Ty Row → CommonNominalFinite.Ty Row → Prop)
    (assignment : Index → CommonNominalFinite.Ty Row)

theorem optionalProject_exact (depth : Nat) (hidden : List Nat) (label : Nat)
    (source : Layer Row Index) (obs : CommonNominalFinite.Observation Row) :
    CommonNominalFinite.MaskedProbeStep leRow env argumentOrder hidden
        (source.evalAt (depth + 1) assignment) (.optional label obs) ↔
      Profile.Holds leRow env argumentOrder assignment (optionalProject hidden label source) obs := by
  induction source generalizing hidden with
  | union first last ihFirst ihLast =>
      simpa only [Layer.evalAt, CommonNominalFinite.maskedProbeStep_union, optionalProject,
        Profile.holds_both] using and_congr (ihFirst hidden) (ihLast hidden)
  | inter first last ihFirst ihLast =>
      simpa only [Layer.evalAt, CommonNominalFinite.maskedProbeStep_inter, optionalProject,
        Profile.holds_either] using or_congr (ihFirst hidden) (ihLast hidden)
  | mask more source ih =>
      simpa only [Layer.evalAt, CommonNominalFinite.MaskedProbeStep, optionalProject] using ih (hidden ++ more)
  | record current payload rest ih =>
      simp only [Layer.evalAt, CommonNominalFinite.MaskedProbeStep, optionalProject]
      split
      · rfl
      · rw [Profile.holds_withTrivial, ih]
  | recordDefault current source fallback ih =>
      simp only [Layer.evalAt, CommonNominalFinite.MaskedProbeStep, optionalProject,
        Profile.holds_withTrivial]
      split
      · rw [Profile.holds_both, ih,
          CommonNominalDefaultRequired.fieldPresence_exact leRow env argumentOrder assignment depth]
        cases fieldPresence hidden label source <;> cases obs <;>
          simp [Profile.Holds, Payload.evalFinite, CommonNominalFinite.MaskedProbeStep]
      · rw [ih]
  | exactEmpty =>
      by_cases masked : label ∈ hidden <;>
        cases obs <;> simp [optionalProject, Layer.evalAt, CommonNominalFinite.MaskedProbeStep,
          masked, Profile.Holds, Payload.evalFinite]
  | emptyRecord =>
      cases obs <;> simp [optionalProject, Layer.evalAt, CommonNominalFinite.MaskedProbeStep,
        Profile.Holds, Payload.evalFinite]
  | bottom =>
      cases obs <;> simp [optionalProject, Layer.evalAt, CommonNominalFinite.MaskedProbeStep,
        Profile.Holds, Payload.evalFinite]
  | _ => simp [optionalProject, Layer.evalAt, CommonNominalFinite.MaskedProbeStep, Profile.Holds]

theorem fieldProject_exact (depth : Nat) (hidden : List Nat) (label : Nat)
    (source : Layer Row Index) (obs : CommonNominalFinite.Observation Row) :
    CommonNominalFinite.MaskedProbeStep leRow env argumentOrder hidden
        (source.evalAt (depth + 1) assignment) (.field label obs) ↔
      Profile.Holds leRow env argumentOrder assignment (fieldProject hidden label source) obs := by
  induction source generalizing hidden with
  | union first last ihFirst ihLast =>
      simpa only [Layer.evalAt, CommonNominalFinite.maskedProbeStep_union, fieldProject,
        Profile.holds_both] using and_congr (ihFirst hidden) (ihLast hidden)
  | inter first last ihFirst ihLast =>
      simpa only [Layer.evalAt, CommonNominalFinite.maskedProbeStep_inter, fieldProject,
        Profile.holds_either] using or_congr (ihFirst hidden) (ihLast hidden)
  | mask more source ih =>
      simpa only [Layer.evalAt, CommonNominalFinite.MaskedProbeStep, fieldProject] using ih (hidden ++ more)
  | record current payload rest ih =>
      simp only [Layer.evalAt, CommonNominalFinite.MaskedProbeStep, fieldProject]
      split
      · rfl
      · exact ih hidden
  | recordDefault current source fallback ih =>
      simp only [Layer.evalAt, CommonNominalFinite.MaskedProbeStep, fieldProject]
      split
      · rw [Profile.holds_both, optionalProject_exact leRow env argumentOrder assignment,
          CommonNominalDefaultRequired.fieldPresence_exact leRow env argumentOrder assignment depth]
        cases fieldPresence hidden label source <;> cases obs <;>
          simp [Profile.Holds, Payload.evalFinite, CommonNominalFinite.MaskedProbeStep]
      · exact ih hidden
  | bottom =>
      cases obs <;> simp [fieldProject, Layer.evalAt, CommonNominalFinite.MaskedProbeStep,
        Profile.Holds, Payload.evalFinite]
  | _ => simp [fieldProject, Layer.evalAt, CommonNominalFinite.MaskedProbeStep, Profile.Holds]

end Finite

namespace Payload

/-- Reading a proper child once retains its whole regular graph. -/
def common (payload : Payload (CommonNominalSyntax.State CommonNominalCarrier.Row)) : CommonNominalCarrier.Ty :=
  payload.evalLayer (CommonNominalSyntax.graph CommonNominalCarrier.Row)

theorem observe_common (depth : Nat) (payload : Payload (CommonNominalSyntax.State CommonNominalCarrier.Row)) :
    CommonNominalCarrier.observeTy depth payload.common =
      payload.evalFinite (CommonNominalSyntax.observe (CommonNominalSyntax.graph CommonNominalCarrier.Row) (depth + 1)) :=
  evalAt_evalLayer (CommonNominalSyntax.graph CommonNominalCarrier.Row)
    (CommonNominalSyntax.observe (CommonNominalSyntax.graph CommonNominalCarrier.Row) depth) depth payload

end Payload

def optionalType (hidden : List Nat) (label : Nat) (source : CommonNominalCarrier.Ty) : Option CommonNominalCarrier.Ty :=
  (optionalProject hidden label source).map Payload.common

def fieldType (hidden : List Nat) (label : Nat) (source : CommonNominalCarrier.Ty) : Option CommonNominalCarrier.Ty :=
  (fieldProject hidden label source).map Payload.common

def ProfileAt (depth rank : Nat) (env : CommonNominalFinite.Environment CommonNominalCarrier.Row)
    (profile : Option CommonNominalCarrier.Ty) (obs : CommonNominalCarrier.Observation) : Prop :=
  match profile with
  | none => False
  | some payload => CommonNominalFinite.ProbeAt Common.rowLe rank env (CommonNominalCarrier.observeTy depth payload) obs

/-- The optional profile retains all finite and regular payloads, at every
negative rank and arbitrary demand environment. -/
theorem optional_type_exact (hidden : List Nat) (label : Nat) (source : CommonNominalCarrier.Ty)
    (depth rank : Nat) (env : CommonNominalFinite.Environment CommonNominalCarrier.Row) (obs : CommonNominalCarrier.Observation) :
    CommonNominalFinite.MaskedProbeAt Common.rowLe rank env hidden
        (CommonNominalCarrier.observeTy (depth + 1) source) (.optional label obs) ↔
      ProfileAt depth rank env (optionalType hidden label source) obs := by
  change CommonNominalFinite.MaskedProbeAt Common.rowLe rank env hidden
    (source.evalAt (depth + 1) (CommonNominalSyntax.observe (CommonNominalSyntax.graph CommonNominalCarrier.Row) (depth + 1)))
    (.optional label obs) ↔ _
  cases rank with
  | zero =>
      have exact := optionalProject_exact Common.rowLe env (fun _ _ => True)
        (CommonNominalSyntax.observe (CommonNominalSyntax.graph CommonNominalCarrier.Row) (depth + 1)) depth hidden label source obs
      cases projected : optionalProject hidden label source <;>
        simpa only [CommonNominalFinite.MaskedProbeAt, optionalType, ProfileAt, projected,
          Option.map, Profile.Holds, Payload.observe_common, CommonNominalFinite.ProbeAt, CommonNominalFinite.ProbeStep]
          using exact
  | succ rank =>
      have exact := optionalProject_exact Common.rowLe env (fun expected input =>
        ∀ next observation, CommonNominalFinite.ProbeAt Common.rowLe rank next input observation →
          CommonNominalFinite.ProbeAt Common.rowLe rank next expected observation)
        (CommonNominalSyntax.observe (CommonNominalSyntax.graph CommonNominalCarrier.Row) (depth + 1)) depth hidden label source obs
      cases projected : optionalProject hidden label source <;>
        simpa only [CommonNominalFinite.MaskedProbeAt, optionalType, ProfileAt, projected,
          Option.map, Profile.Holds, Payload.observe_common, CommonNominalFinite.ProbeAt, CommonNominalFinite.ProbeStep]
          using exact

theorem field_type_exact (hidden : List Nat) (label : Nat) (source : CommonNominalCarrier.Ty)
    (depth rank : Nat) (env : CommonNominalFinite.Environment CommonNominalCarrier.Row) (obs : CommonNominalCarrier.Observation) :
    CommonNominalFinite.MaskedProbeAt Common.rowLe rank env hidden
        (CommonNominalCarrier.observeTy (depth + 1) source) (.field label obs) ↔
      ProfileAt depth rank env (fieldType hidden label source) obs := by
  change CommonNominalFinite.MaskedProbeAt Common.rowLe rank env hidden
    (source.evalAt (depth + 1) (CommonNominalSyntax.observe (CommonNominalSyntax.graph CommonNominalCarrier.Row) (depth + 1)))
    (.field label obs) ↔ _
  cases rank with
  | zero =>
      have exact := fieldProject_exact Common.rowLe env (fun _ _ => True)
        (CommonNominalSyntax.observe (CommonNominalSyntax.graph CommonNominalCarrier.Row) (depth + 1)) depth hidden label source obs
      cases projected : fieldProject hidden label source <;>
        simpa only [CommonNominalFinite.MaskedProbeAt, fieldType, ProfileAt, projected,
          Option.map, Profile.Holds, Payload.observe_common, CommonNominalFinite.ProbeAt, CommonNominalFinite.ProbeStep]
          using exact
  | succ rank =>
      have exact := fieldProject_exact Common.rowLe env (fun expected input =>
        ∀ next observation, CommonNominalFinite.ProbeAt Common.rowLe rank next input observation →
          CommonNominalFinite.ProbeAt Common.rowLe rank next expected observation)
        (CommonNominalSyntax.observe (CommonNominalSyntax.graph CommonNominalCarrier.Row) (depth + 1)) depth hidden label source obs
      cases projected : fieldProject hidden label source <;>
        simpa only [CommonNominalFinite.MaskedProbeAt, fieldType, ProfileAt, projected,
          Option.map, Profile.Holds, Payload.observe_common, CommonNominalFinite.ProbeAt, CommonNominalFinite.ProbeStep]
          using exact

/-- An absent profile fails immediately; otherwise there is one ordinary
child comparison and no shifted observation obligation. -/
def ProfileBelow (profile : Option CommonNominalCarrier.Ty) (target : CommonNominalCarrier.Ty) : Prop :=
  match profile with
  | none => False
  | some payload => CommonNominalCarrier.Subtype payload target

theorem profileBelow_exact (profile : Option CommonNominalCarrier.Ty) (target : CommonNominalCarrier.Ty) :
    ProfileBelow profile target ↔
      ∀ depth rank env obs, CommonNominalFinite.ProbeAt Common.rowLe rank env
        (CommonNominalCarrier.observeTy depth target) obs → ProfileAt depth rank env profile obs := by
  cases profile with
  | none =>
      constructor
      · exact False.elim
      · intro accepts
        exact accepts 0 0 ⟨fun _ => .bottom, fun _ => []⟩ .trivial
          (CommonNominalFinite.probeAt_trivial 0 _)
  | some payload =>
      exact forall_congr' fun depth => CommonNominalFinite.producerLe_iff_probe _ _

/-- Comparing profiles retains the distinction between no requirement and
a requirement with top payload. -/
def ProfileLe (source target : Option CommonNominalCarrier.Ty) : Prop :=
  match target with
  | none => True
  | some payload => ProfileBelow source payload

theorem profileLe_exact (source target : Option CommonNominalCarrier.Ty) :
    ProfileLe source target ↔
      ∀ depth rank env obs, ProfileAt depth rank env target obs →
        ProfileAt depth rank env source obs := by
  cases target with
  | none => simp [ProfileLe, ProfileAt]
  | some payload => exact profileBelow_exact source payload

theorem optional_payload_exact (label : Nat) (source target : CommonNominalCarrier.Ty) :
    CommonNominalDefaultRequired.OptionalPayload label source target ↔
      ProfileBelow (optionalType [] label source) target := by
  rw [profileBelow_exact]
  unfold CommonNominalDefaultRequired.OptionalPayload
  apply forall_congr'
  intro depth
  apply forall_congr'
  intro rank
  apply forall_congr'
  intro env
  apply forall_congr'
  intro obs
  apply imp_congr_right
  intro _
  simpa only [CommonNominalFinite.maskedProbeAt_nil] using
    optional_type_exact [] label source depth rank env obs

/-- Full required-target default decomposition by finite presence and an
ordinary child comparison. No optional semantic obligation remains. -/
theorem default_required_projected_iff (label : Nat) (source fallback target : CommonNominalCarrier.Ty) :
    CommonNominalCarrier.Subtype (CommonNominalCarrier.recordDefault label source fallback) (CommonNominalCarrier.required label target) ↔
      ProfileBelow (optionalType [] label source) target ∧
        (CommonNominalDefaultRequired.present label source = true ∨ CommonNominalCarrier.Subtype fallback target) := by
  exact (CommonNominalDefaultRequired.default_required_iff label source fallback target).trans
    (and_congr (optional_payload_exact label source target) Iff.rfl)

theorem default_record_projected_iff (label : Nat) (source fallback target tail : CommonNominalCarrier.Ty) :
    CommonNominalCarrier.Subtype (CommonNominalCarrier.recordDefault label source fallback) (CommonNominalCarrier.record label target tail) ↔
      ProfileBelow (optionalType [] label source) target ∧
        (CommonNominalDefaultRequired.present label source = true ∨ CommonNominalCarrier.Subtype fallback target) ∧
        CommonNominalCarrier.RecordTailLe [label] source tail := by
  exact (CommonNominalDefaultRequired.default_record_iff label source fallback target tail).trans
    (and_congr (optional_payload_exact label source target) Iff.rfl)

end Yulang.CommonNominalPayloadProjection
