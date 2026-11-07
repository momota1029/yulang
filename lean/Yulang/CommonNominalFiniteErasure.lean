import Yulang.CommonNominalFullFiniteConstructors
import Yulang.Common

/-!
# A proof-witness erasure for old Common existential reflection

Dedicated nominals and Float remain unchanged in the language carrier. This
map is only a proposed way to replace intermediate existential witnesses in an
old-source derivation: erase new atomic heads to the old unit atom, preserve
every old constructor and row. Its order preservation requires a separate
all-negative-rank proof; a syntactic retraction alone does not establish it.
-/

namespace Yulang.CommonNominalFiniteErasure

abbrev Row := Common.Row
abbrev New := CommonNominalFullDemand.Ty Row
abbrev Old := CommonFinite.Ty Row
abbrev NewLe (rank : Nat) := CommonNominalFullDemand.ProducerLeAt Common.rowLe rank
abbrev OldLe (rank : Nat) := CommonFinite.ProducerLeAt Common.rowLe rank
abbrev Head := CommonNominalFullDemand.Head

def erase : New → Old
  | .base scalar => .base scalar
  | .float | .nominal _ _ => .base .unit
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (erase first) (erase last)
  | .inter first last => .inter (erase first) (erase last)
  | .pair first last => .pair (erase first) (erase last)
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty
  | .record label payload rest => .record label (erase payload) (erase rest)
  | .recordDefault label source fallback => .recordDefault label (erase source) (erase fallback)
  | .variant label payload => .variant label (erase payload)
  | .arrow input incoming output outgoing => .arrow (erase input) incoming (erase output) outgoing
  | .mask hidden source => .mask hidden (erase source)

private def collapseHead : Head → ProducerContextual.Head
  | .base scalar => .base scalar
  | .float | .nominal _ _ => .base .unit
  | .pair => .pair
  | .records => .records
  | .variant label => .variant label
  | .arrow => .arrow

/-- Every positively traversed head; negative inputs are handled at the
preceding rank with their own finite environment. -/
private def heads : New → List Head
  | .base scalar => [.base scalar]
  | .float => [.float]
  | .nominal name arguments => [.nominal name arguments.length]
  | .bottom | .top => []
  | .union first last | .inter first last => heads first ++ heads last
  | .pair first last => .pair :: (heads first ++ heads last)
  | .emptyRecord | .exactEmpty => [.records]
  | .record _ first last | .recordDefault _ first last => .records :: (heads first ++ heads last)
  | .variant label payload => .variant label :: heads payload
  | .arrow _ _ result _ => .arrow :: heads result
  | .mask _ source => heads source

private def Supported (inventory : List Head) (type : New) : Prop :=
  ∀ head ∈ heads type, head ∈ inventory

private def inputs : New → List New
  | .base _ | .float | .nominal _ _ | .bottom | .top | .emptyRecord | .exactEmpty => []
  | .union first last | .inter first last | .pair first last |
      .record _ first last | .recordDefault _ first last => inputs first ++ inputs last
  | .variant _ payload | .mask _ payload => inputs payload
  | .arrow input _ result _ => input :: inputs result

private def Compatible (oldEnv : CommonFinite.Environment Row)
    (newEnv : CommonNominalFullDemand.Environment Row)
    (oldArg : Old → Old → Prop) (newArg : New → New → Prop) : New → Prop
  | .base _ | .float | .nominal _ _ | .bottom | .top | .emptyRecord | .exactEmpty => True
  | .union first last | .inter first last | .pair first last |
      .record _ first last | .recordDefault _ first last =>
      Compatible oldEnv newEnv oldArg newArg first ∧ Compatible oldEnv newEnv oldArg newArg last
  | .variant _ payload | .mask _ payload => Compatible oldEnv newEnv oldArg newArg payload
  | .arrow input _ result _ =>
      (∀ name, newArg (newEnv.types name) input ↔ oldArg (oldEnv.types name) (erase input)) ∧
        Compatible oldEnv newEnv oldArg newArg result

private theorem compatible_iff (oldEnv : CommonFinite.Environment Row)
    (newEnv : CommonNominalFullDemand.Environment Row)
    (oldArg : Old → Old → Prop) (newArg : New → New → Prop) (type : New) :
    Compatible oldEnv newEnv oldArg newArg type ↔
      ∀ input ∈ inputs type, ∀ name,
        newArg (newEnv.types name) input ↔ oldArg (oldEnv.types name) (erase input) := by
  induction type using CommonNominalFinite.Ty.rec
    (motive_2 := fun _ => True) (motive_3 := fun _ => True) <;>
    simp_all [Compatible, inputs, List.mem_append, or_imp, forall_and]

private def baseSlot : Inference.Base → Nat
  | .int => 0
  | .str => 1
  | .bool => 2
  | .unit => 3

private def roleSlots (inventory : List Head) (roles : Nat → List ProducerContextual.Head) :
    Nat → List Head
  | 0 => inventory.filter (fun head => decide (collapseHead head = .base .int))
  | 1 => inventory.filter (fun head => decide (collapseHead head = .base .str))
  | 2 => inventory.filter (fun head => decide (collapseHead head = .base .bool))
  | 3 => inventory.filter (fun head => decide (collapseHead head = .base .unit))
  | name + 4 => inventory.filter (fun head => decide (collapseHead head ∈ roles name))

private theorem base_member (inventory : List Head) (roles : Nat → List ProducerContextual.Head)
    (head : Head) (scalar : Inference.Base) (present : head ∈ inventory) :
    head ∈ roleSlots inventory roles (baseSlot scalar) ↔ collapseHead head = .base scalar := by
  cases scalar <;> simp [baseSlot, roleSlots, List.mem_filter, present]

private theorem role_member (inventory : List Head) (roles : Nat → List ProducerContextual.Head)
    (head : Head) (name : Nat) (present : head ∈ inventory) :
    head ∈ roleSlots inventory roles (name + 4) ↔ collapseHead head ∈ roles name := by
  simp [roleSlots, List.mem_filter, present]

private def translate : CommonFinite.Observation Row → CommonNominalFullDemand.Observation Row
  | .trivial => .trivial
  | .impossible => .impossible
  | .base scalar => .role (baseSlot scalar)
  | .records => .records
  | .role name => .role (name + 4)
  | .pairFirst obs => .pairFirst (translate obs)
  | .pairLast obs => .pairLast (translate obs)
  | .field label obs => .field label (translate obs)
  | .optional label obs => .optional label (translate obs)
  | .variant label obs => .variant label (translate obs)
  | .arrowArgument name => .arrowArgument name
  | .arrowResult obs => .arrowResult (translate obs)
  | .arrowInputRow row => .arrowInputRow row
  | .arrowOutputRow row => .arrowOutputRow row

@[simp] private theorem translate_trivial (obs : CommonFinite.Observation Row) :
    translate obs = .trivial ↔ obs = .trivial := by
  cases obs <;> simp [translate]

private theorem project_step (oldEnv : CommonFinite.Environment Row)
    (newEnv : CommonNominalFullDemand.Environment Row) (inventory : List Head)
    (roles : newEnv.roles = roleSlots inventory oldEnv.roles)
    (oldArg : Old → Old → Prop) (newArg : New → New → Prop) (type : New)
    (compatible : Compatible oldEnv newEnv oldArg newArg type)
    (supported : Supported inventory type) (hidden : List Nat) (obs : CommonFinite.Observation Row) :
    CommonNominalFullDemand.MaskedProbeStep Common.rowLe newEnv newArg hidden type (translate obs) ↔
      CommonFinite.MaskedProbeStep Common.rowLe oldEnv oldArg hidden (erase type) obs := by
  have baseRoles (head : Head) (scalar : Inference.Base) :
      head ∈ newEnv.roles (baseSlot scalar) ↔
        head ∈ inventory ∧ collapseHead head = .base scalar := by
    rw [roles]
    cases scalar <;> simp [roleSlots, baseSlot, List.mem_filter]
  have roleRoles (head : Head) (name : Nat) :
      head ∈ newEnv.roles (name + 4) ↔
        head ∈ inventory ∧ collapseHead head ∈ oldEnv.roles name := by
    rw [roles]
    simp [roleSlots, List.mem_filter]
  induction type using CommonNominalFinite.Ty.rec
    (motive_2 := fun _ => True) (motive_3 := fun _ => True) generalizing hidden obs with
  | base scalar =>
      have present : CommonNominalFullDemand.Head.base scalar ∈ inventory := supported _ (by simp [heads])
      cases obs <;> simp [erase, translate, CommonNominalFullDemand.MaskedProbeStep,
        CommonFinite.MaskedProbeStep, baseRoles, roleRoles, collapseHead, present]
  | float =>
      have present : CommonNominalFullDemand.Head.float ∈ inventory := supported _ (by simp [heads])
      cases obs <;> simp [erase, translate, CommonNominalFullDemand.MaskedProbeStep,
        CommonFinite.MaskedProbeStep, baseRoles, roleRoles, collapseHead, present]
  | nominal name arguments _ =>
      have present : CommonNominalFullDemand.Head.nominal name arguments.length ∈ inventory := supported _ (by simp [heads])
      cases obs <;> simp [erase, translate, CommonNominalFullDemand.MaskedProbeStep,
        CommonFinite.MaskedProbeStep, baseRoles, roleRoles, collapseHead, present]
  | bottom | top =>
      cases obs <;> simp [erase, translate, CommonNominalFullDemand.MaskedProbeStep,
        CommonFinite.MaskedProbeStep]
  | emptyRecord | exactEmpty =>
      have present : CommonNominalFullDemand.Head.records ∈ inventory := supported _ (by simp [heads])
      cases obs <;> simp [erase, translate, CommonNominalFullDemand.MaskedProbeStep,
        CommonFinite.MaskedProbeStep, baseRoles, roleRoles, collapseHead, present]
  | union first last ihf ihl | inter first last ihf ihl =>
      have firstSupport : Supported inventory first := fun head member =>
        supported head (by simp [heads, member])
      have lastSupport : Supported inventory last := fun head member =>
        supported head (by simp [heads, member])
      have before := ihf compatible.1 firstSupport
      have after := ihl compatible.2 lastSupport
      cases obs <;> simp [erase, translate, CommonNominalFullDemand.MaskedProbeStep,
        ← before, ← after]
  | pair first last ihf ihl =>
      have present : CommonNominalFullDemand.Head.pair ∈ inventory := supported _ (by simp [heads])
      have firstSupport : Supported inventory first := fun head member =>
        supported head (by simp [heads, member])
      have lastSupport : Supported inventory last := fun head member =>
        supported head (by simp [heads, member])
      have before := ihf compatible.1 firstSupport
      have after := ihl compatible.2 lastSupport
      cases obs <;> simp [erase, translate, CommonNominalFullDemand.MaskedProbeStep,
        CommonFinite.MaskedProbeStep, ← before, ← after, baseRoles, roleRoles, collapseHead, present]
  | record label first last ihf ihl | recordDefault label first last ihf ihl =>
      have present : CommonNominalFullDemand.Head.records ∈ inventory := supported _ (by simp [heads])
      have firstSupport : Supported inventory first := fun head member =>
        supported head (by simp [heads, member])
      have lastSupport : Supported inventory last := fun head member =>
        supported head (by simp [heads, member])
      have before := ihf compatible.1 firstSupport
      have after := ihl compatible.2 lastSupport
      cases obs <;> simp [erase, translate, CommonNominalFullDemand.MaskedProbeStep,
        CommonFinite.MaskedProbeStep, ← before, ← after, baseRoles, roleRoles, collapseHead, present]
  | variant label payload ih =>
      have present : CommonNominalFullDemand.Head.variant label ∈ inventory := supported _ (by simp [heads])
      have payloadSupport : Supported inventory payload := fun head member =>
        supported head (by simp [heads, member])
      have inner := ih compatible payloadSupport
      cases obs <;> simp [erase, translate, CommonNominalFullDemand.MaskedProbeStep,
        CommonFinite.MaskedProbeStep, ← inner, baseRoles, roleRoles, collapseHead, present]
  | mask more source ih =>
      have inner := ih compatible supported
      cases obs <;> simp [erase, translate, CommonNominalFullDemand.MaskedProbeStep,
        CommonFinite.MaskedProbeStep, ← inner]
  | arrow input incoming result outgoing _ ihr =>
      have present : CommonNominalFullDemand.Head.arrow ∈ inventory := supported _ (by simp [heads])
      have resultSupport : Supported inventory result := fun head member =>
        supported head (by simp [heads, member])
      have output := ihr compatible.2 resultSupport
      cases obs <;> simp [erase, translate, CommonNominalFullDemand.MaskedProbeStep,
        CommonFinite.MaskedProbeStep, ← output, compatible.1, baseRoles, roleRoles, collapseHead, present]
  | nil | cons | inl | inr => trivial

private def meet : List New → New
  | [] => .top
  | first :: rest => .inter first (meet rest)

private theorem meet_member (rank : Nat) (family : List New) (input : New)
    (present : input ∈ family) : NewLe rank (meet family) input := by
  apply (CommonNominalFullDemand.producerLeAt_iff_probe _ _ _).mpr
  intro env obs accepted
  induction family with
  | nil => cases present
  | cons first rest ih =>
      change CommonNominalFullDemand.ProbeAt Common.rowLe rank env (.inter first (meet rest)) obs
      apply (CommonNominalFullDemand.probeAt_inter _ _ _ _).mpr
      rcases List.mem_cons.mp present with rfl | later
      · exact Or.inl accepted
      · exact Or.inr (ih later)

private theorem below_erased_meet (rank : Nat) (type : Old) (family : List New)
    (below : ∀ input ∈ family, OldLe rank type (erase input)) :
    OldLe rank type (erase (meet family)) := by
  apply (CommonFinite.producerLeAt_iff_probe _ _ _).mpr
  intro env obs accepted
  induction family with
  | nil =>
      have trivialObs : obs = .trivial := by
        cases rank <;> cases obs <;>
          simp_all [meet, erase, CommonFinite.ProbeAt, CommonFinite.ProbeStep,
            CommonFinite.MaskedProbeStep]
      subst obs
      exact CommonFinite.probeAt_trivial rank type
  | cons first rest ih =>
      have atFirst := below first (by simp)
      have atRest : ∀ input ∈ rest, OldLe rank type (erase input) :=
        fun input member => below input (by simp [member])
      have split : CommonFinite.ProbeAt Common.rowLe rank env (erase first) obs ∨
          CommonFinite.ProbeAt Common.rowLe rank env (erase (meet rest)) obs := by
        simpa only [meet, erase, CommonFinite.probeAt_inter] using accepted
      rcases split with before | after
      · exact (CommonFinite.producerLeAt_iff_probe _ _ _).mp atFirst env obs before
      · exact ih atRest after

private noncomputable def witness (rank : Nat) (parameter : Old) (family : List New) : New := by
  classical
  exact meet (family.filter fun input => decide (OldLe rank parameter (erase input)))

private theorem witness_exact (rank : Nat)
    (previous : ∀ first last : New, NewLe rank first last → OldLe rank (erase first) (erase last))
    (parameter : Old) (family : List New) (input : New) (present : input ∈ family) :
    NewLe rank (witness rank parameter family) input ↔ OldLe rank parameter (erase input) := by
  classical
  let selected := family.filter fun input => decide (OldLe rank parameter (erase input))
  have belowWitness : OldLe rank parameter (erase (witness rank parameter family)) := by
    apply below_erased_meet rank parameter selected
    intro chosen member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  constructor
  · intro accepted
    have after := previous _ _ accepted
    exact fun env demand valid => belowWitness env demand (after env demand valid)
  · intro accepted
    exact meet_member rank selected input (List.mem_filter.mpr ⟨present, by simp [accepted]⟩)

private noncomputable def witnessEnvironment (rank : Nat) (oldEnv : CommonFinite.Environment Row)
    (family : List New) (inventory : List Head) : CommonNominalFullDemand.Environment Row :=
  ⟨fun name => witness rank (oldEnv.types name) family, roleSlots inventory oldEnv.roles⟩

private theorem project_zero (oldEnv : CommonFinite.Environment Row) (inventory : List Head)
    (type : New) (supported : Supported inventory type) (obs : CommonFinite.Observation Row) :
    CommonNominalFullDemand.ProbeAt Common.rowLe 0
        ⟨fun _ => .bottom, roleSlots inventory oldEnv.roles⟩ type (translate obs) ↔
      CommonFinite.ProbeAt Common.rowLe 0 oldEnv (erase type) obs := by
  apply project_step oldEnv _ inventory rfl (fun _ _ => True) (fun _ _ => True)
    type _ supported [] obs
  apply (compatible_iff _ _ _ _ _).mpr
  intro input _ name
  rfl

private theorem project_successor (rank : Nat)
    (previous : ∀ first last : New, NewLe rank first last → OldLe rank (erase first) (erase last))
    (oldEnv : CommonFinite.Environment Row) (family : List New) (inventory : List Head)
    (type : New) (inputSupport : ∀ input ∈ inputs type, input ∈ family)
    (headSupport : Supported inventory type) (obs : CommonFinite.Observation Row) :
    CommonNominalFullDemand.ProbeAt Common.rowLe (rank + 1)
        (witnessEnvironment rank oldEnv family inventory) type (translate obs) ↔
      CommonFinite.ProbeAt Common.rowLe (rank + 1) oldEnv (erase type) obs := by
  apply project_step oldEnv _ inventory rfl
    (fun expected input => ∀ next obs,
      CommonFinite.ProbeAt Common.rowLe rank next input obs →
        CommonFinite.ProbeAt Common.rowLe rank next expected obs)
    (fun expected input => ∀ next obs,
      CommonNominalFullDemand.ProbeAt Common.rowLe rank next input obs →
        CommonNominalFullDemand.ProbeAt Common.rowLe rank next expected obs)
    type _ headSupport [] obs
  apply (compatible_iff _ _ _ _ _).mpr
  intro input present name
  exact (CommonNominalFullDemand.producerLeAt_iff_probe _ _ _).symm.trans
    ((witness_exact rank previous (oldEnv.types name) family input (inputSupport input present)).trans
      (CommonFinite.producerLeAt_iff_probe _ _ _))

/-- Every pair of arbitrary new finite types and every negative rank. The
map preserves all old structural constructors/rows and forgets new atomic
heads only for replacing old-source existential witnesses. It is not the
language meaning or a representation of nominal argument invariance. -/
theorem finite_rank_monotone (rank : Nat) (first last : New)
    (below : NewLe rank first last) : OldLe rank (erase first) (erase last) := by
  induction rank generalizing first last with
  | zero =>
      apply (CommonFinite.producerLeAt_iff_probe _ _ _).mpr
      intro env obs accepted
      let inventory := heads first ++ heads last
      have firstSupport : Supported inventory first :=
        fun _ member => List.mem_append.mpr (Or.inl member)
      have lastSupport : Supported inventory last :=
        fun _ member => List.mem_append.mpr (Or.inr member)
      exact (project_zero env inventory first firstSupport obs).mp
        ((CommonNominalFullDemand.producerLeAt_iff_probe _ _ _).mp below _ _
          ((project_zero env inventory last lastSupport obs).mpr accepted))
  | succ rank previous =>
      apply (CommonFinite.producerLeAt_iff_probe _ _ _).mpr
      intro env obs accepted
      let inventory := heads first ++ heads last
      let family := inputs first ++ inputs last
      have firstSupport : Supported inventory first :=
        fun _ member => List.mem_append.mpr (Or.inl member)
      have lastSupport : Supported inventory last :=
        fun _ member => List.mem_append.mpr (Or.inr member)
      have firstInput : ∀ input ∈ inputs first, input ∈ family :=
        fun _ member => List.mem_append.mpr (Or.inl member)
      have lastInput : ∀ input ∈ inputs last, input ∈ family :=
        fun _ member => List.mem_append.mpr (Or.inr member)
      exact (project_successor rank previous env family inventory first firstInput firstSupport obs).mp
        ((CommonNominalFullDemand.producerLeAt_iff_probe _ _ _).mp below _ _
          ((project_successor rank previous env family inventory last lastInput lastSupport obs).mpr accepted))

theorem finite_monotone (first last : New)
    (below : CommonNominalFullDemand.ProducerLe Common.rowLe first last) :
    CommonFinite.ProducerLe Common.rowLe (erase first) (erase last) :=
  fun rank => finite_rank_monotone rank first last (below rank)

end Yulang.CommonNominalFiniteErasure
