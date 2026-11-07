import Yulang.CommonNominalEmbedding
import Yulang.CommonNominalFullCarrier

/-!
# Old Common order under full nominal/Float role environments

At each negative rank, a finite family of old arrow inputs is observed. For
an arbitrary extended parameter, intersect exactly those old inputs above it.
This single old witness realizes all comparisons in that family simultaneously.
The induction uses the previous rank's conservativity, not a restriction of
extended parameters or an added assumption on solved instances.
-/

namespace Yulang.CommonNominalFullConservativity

abbrev Row := Common.Row
abbrev Old := CommonFinite.Ty Row
abbrev New := CommonNominalFullDemand.Ty Row
abbrev embed := @CommonNominalEmbedding.finite Row
abbrev OldLe (rank : Nat) := CommonFinite.ProducerLeAt Common.rowLe rank
abbrev NewLe (rank : Nat) := CommonNominalFullDemand.ProducerLeAt Common.rowLe rank


private def liftHead : ProducerContextual.Head → CommonNominalFullDemand.Head
  | .base scalar => .base scalar
  | .pair => .pair
  | .records => .records
  | .variant label => .variant label
  | .arrow => .arrow

private def projectHead : CommonNominalFullDemand.Head → Option ProducerContextual.Head
  | .base scalar => some (.base scalar)
  | .pair => some .pair
  | .records => some .records
  | .variant label => some (.variant label)
  | .arrow => some .arrow
  | .float | .nominal _ _ => none

@[simp] private theorem projectHead_liftHead (head : ProducerContextual.Head) :
    projectHead (liftHead head) = some head := by
  cases head <;> rfl

private theorem liftHead_injective : Function.Injective liftHead := by
  intro a b same
  have projected := congrArg projectHead same
  simpa only [projectHead_liftHead, Option.some.injEq] using projected

@[simp] private theorem projected_member (heads : List CommonNominalFullDemand.Head)
    (head : ProducerContextual.Head) :
    head ∈ heads.filterMap projectHead ↔ liftHead head ∈ heads := by
  induction heads with
  | nil => simp
  | cons first rest ih =>
      cases first <;> cases head <;> simp_all [projectHead, liftHead]

private def RolesCompatible (oldEnv : CommonFinite.Environment Row)
    (newEnv : CommonNominalFullDemand.Environment Row) : Prop :=
  ∀ name head, head ∈ oldEnv.roles name ↔ liftHead head ∈ newEnv.roles name

private def meet : List Old → Old
  | [] => .top
  | head :: tail => .inter head (meet tail)

private theorem new_trans {rank : Nat} {a b c : New}
    (first : NewLe rank a b) (last : NewLe rank b c) : NewLe rank a c :=
  fun env demand accepted => first env demand (last env demand accepted)

private theorem new_top (rank : Nat) (type : New) : NewLe rank type .top := by
  apply (CommonNominalFullDemand.producerLeAt_iff_probe _ _ _).mpr
  intro env obs accepted
  cases rank <;> cases obs <;>
    simp_all [CommonNominalFullDemand.ProbeAt, CommonNominalFullDemand.ProbeStep,
      CommonNominalFullDemand.MaskedProbeStep]

private theorem new_meet (rank : Nat) (type : New) (inputs : List Old) :
    NewLe rank type (embed (meet inputs)) ↔ ∀ input ∈ inputs, NewLe rank type (embed input) := by
  induction inputs with
  | nil =>
      constructor
      · intro _ input member; cases member
      · intro _; exact new_top rank type
  | cons head tail ih =>
      change NewLe rank type (.inter (embed head) (embed (meet tail))) ↔ _
      have split : NewLe rank type (.inter (embed head) (embed (meet tail))) ↔
          NewLe rank type (embed head) ∧ NewLe rank type (embed (meet tail)) := by
        simp only [NewLe, CommonNominalFullDemand.producerLeAt_iff_probe,
          CommonNominalFullDemand.probeAt_inter, or_imp, forall_and]
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

end Yulang.CommonNominalFullConservativity

namespace Yulang.CommonNominalFullConservativity

private def project : CommonNominalFullDemand.Observation Row → CommonFinite.Observation Row
  | .trivial => .trivial
  | .impossible => .impossible
  | .base scalar => .base scalar
  | .records => .records
  | .role name => .role name
  | .pairFirst obs => .pairFirst (project obs)
  | .pairLast obs => .pairLast (project obs)
  | .field label obs => .field label (project obs)
  | .optional label obs => .optional label (project obs)
  | .variant label obs => .variant label (project obs)
  | .arrowArgument name => .arrowArgument name
  | .arrowResult obs => .arrowResult (project obs)
  | .arrowInputRow row => .arrowInputRow row
  | .arrowOutputRow row => .arrowOutputRow row
  | .float | .nominalHead _ _ | .nominalLower _ _ | .nominalUpper _ _ |
      .nominalRowLower _ _ | .nominalRowUpper _ _ => .impossible

private def lift : CommonFinite.Observation Row → CommonNominalFullDemand.Observation Row
  | .trivial => .trivial
  | .impossible => .impossible
  | .base scalar => .base scalar
  | .records => .records
  | .role name => .role name
  | .pairFirst obs => .pairFirst (lift obs)
  | .pairLast obs => .pairLast (lift obs)
  | .field label obs => .field label (lift obs)
  | .optional label obs => .optional label (lift obs)
  | .variant label obs => .variant label (lift obs)
  | .arrowArgument name => .arrowArgument name
  | .arrowResult obs => .arrowResult (lift obs)
  | .arrowInputRow row => .arrowInputRow row
  | .arrowOutputRow row => .arrowOutputRow row

@[simp] private theorem project_lift (obs : CommonFinite.Observation Row) : project (lift obs) = obs := by
  induction obs <;> simp [lift, project, *]

@[simp] private theorem project_trivial (obs : CommonNominalFullDemand.Observation Row) :
    project obs = .trivial ↔ obs = .trivial := by
  cases obs <;> simp [project]

private def inputs : Old → List Old
  | .base _ | .bottom | .top | .emptyRecord | .exactEmpty => []
  | .union first last | .inter first last | .pair first last |
      .record _ first last | .recordDefault _ first last => inputs first ++ inputs last
  | .variant _ payload | .mask _ payload => inputs payload
  | .arrow input _ result _ => input :: inputs result

private def Compatible (oldEnv : CommonFinite.Environment Row)
    (newEnv : CommonNominalFullDemand.Environment Row)
    (oldArg : Old → Old → Prop) (newArg : New → New → Prop) : Old → Prop
  | .base _ | .bottom | .top | .emptyRecord | .exactEmpty => True
  | .union first last | .inter first last | .pair first last |
      .record _ first last | .recordDefault _ first last =>
      Compatible oldEnv newEnv oldArg newArg first ∧ Compatible oldEnv newEnv oldArg newArg last
  | .variant _ payload | .mask _ payload => Compatible oldEnv newEnv oldArg newArg payload
  | .arrow input _ result _ =>
      (∀ name, newArg (newEnv.types name) (embed input) ↔ oldArg (oldEnv.types name) input) ∧
        Compatible oldEnv newEnv oldArg newArg result

private theorem compatible_iff (oldEnv : CommonFinite.Environment Row)
    (newEnv : CommonNominalFullDemand.Environment Row)
    (oldArg : Old → Old → Prop) (newArg : New → New → Prop) (type : Old) :
    Compatible oldEnv newEnv oldArg newArg type ↔
      ∀ input ∈ inputs type, ∀ name,
        newArg (newEnv.types name) (embed input) ↔ oldArg (oldEnv.types name) input := by
  induction type <;> simp [Compatible, inputs, *, List.mem_append, or_imp, forall_and]

private theorem project_step (oldEnv : CommonFinite.Environment Row)
    (newEnv : CommonNominalFullDemand.Environment Row) (roles : RolesCompatible oldEnv newEnv)
    (oldArg : Old → Old → Prop) (newArg : New → New → Prop) (type : Old)
    (compatible : Compatible oldEnv newEnv oldArg newArg type)
    (hidden : List Nat) (obs : CommonNominalFullDemand.Observation Row) :
    CommonNominalFullDemand.MaskedProbeStep Common.rowLe newEnv newArg hidden (embed type) obs ↔
      CommonFinite.MaskedProbeStep Common.rowLe oldEnv oldArg hidden type (project obs) := by
  have baseRoles : ∀ name scalar,
      CommonNominalFullDemand.Head.base scalar ∈ newEnv.roles name ↔
        ProducerContextual.Head.base scalar ∈ oldEnv.roles name :=
    fun name scalar => (roles name (.base scalar)).symm
  have pairRoles : ∀ name, CommonNominalFullDemand.Head.pair ∈ newEnv.roles name ↔
      ProducerContextual.Head.pair ∈ oldEnv.roles name := fun name => (roles name .pair).symm
  have recordRoles : ∀ name, CommonNominalFullDemand.Head.records ∈ newEnv.roles name ↔
      ProducerContextual.Head.records ∈ oldEnv.roles name := fun name => (roles name .records).symm
  have variantRoles : ∀ name label, CommonNominalFullDemand.Head.variant label ∈ newEnv.roles name ↔
      ProducerContextual.Head.variant label ∈ oldEnv.roles name :=
    fun name label => (roles name (.variant label)).symm
  have arrowRoles : ∀ name, CommonNominalFullDemand.Head.arrow ∈ newEnv.roles name ↔
      ProducerContextual.Head.arrow ∈ oldEnv.roles name := fun name => (roles name .arrow).symm
  induction type generalizing hidden obs with
  | base scalar | bottom | top | emptyRecord | exactEmpty =>
      cases obs <;> simp [embed, CommonNominalEmbedding.finite, project,
        CommonNominalFullDemand.MaskedProbeStep, CommonFinite.MaskedProbeStep, baseRoles, recordRoles]
  | union first last ihf ihl | inter first last ihf ihl | pair first last ihf ihl =>
      have forward := ihf compatible.1
      have backward := ihl compatible.2
      cases obs <;> simp [embed, CommonNominalEmbedding.finite, project,
        CommonNominalFullDemand.MaskedProbeStep, CommonFinite.MaskedProbeStep,
        forward, backward, pairRoles]
  | record label head tail ihh iht | recordDefault label head tail ihh iht =>
      have forward := ihh compatible.1
      have backward := iht compatible.2
      cases obs <;> simp [embed, CommonNominalEmbedding.finite, project,
        CommonNominalFullDemand.MaskedProbeStep, CommonFinite.MaskedProbeStep,
        forward, backward, recordRoles]
  | variant label payload ih | mask hidden' payload ih =>
      have inner := ih compatible
      cases obs <;> simp [embed, CommonNominalEmbedding.finite, project,
        CommonNominalFullDemand.MaskedProbeStep, CommonFinite.MaskedProbeStep, inner, variantRoles]
  | arrow input inputRow result resultRow _ ihr =>
      have output := ihr compatible.2
      cases obs <;> simp [embed, CommonNominalEmbedding.finite, project,
        CommonNominalFullDemand.MaskedProbeStep, CommonFinite.MaskedProbeStep,
        output, compatible.1, arrowRoles]

end Yulang.CommonNominalFullConservativity

namespace Yulang.CommonNominalFullConservativity

private theorem project_zero (oldEnv : CommonFinite.Environment Row)
    (newEnv : CommonNominalFullDemand.Environment Row) (roles : RolesCompatible oldEnv newEnv)
    (type : Old) (obs : CommonNominalFullDemand.Observation Row) :
    CommonNominalFullDemand.ProbeAt Common.rowLe 0 newEnv (embed type) obs ↔
      CommonFinite.ProbeAt Common.rowLe 0 oldEnv type (project obs) := by
  apply project_step oldEnv newEnv roles (fun _ _ => True) (fun _ _ => True) type _ [] obs
  apply (compatible_iff _ _ _ _ _).mpr
  intro input _ name
  rfl

private noncomputable def oldWitnessEnvironment (rank : Nat) (newEnv : CommonNominalFullDemand.Environment Row)
    (family : List Old) : CommonFinite.Environment Row :=
  ⟨fun name => witness rank (newEnv.types name) family,
    fun name => (newEnv.roles name).filterMap projectHead⟩

private def newEnvironment (oldEnv : CommonFinite.Environment Row) :
    CommonNominalFullDemand.Environment Row :=
  ⟨fun name => embed (oldEnv.types name), fun name => (oldEnv.roles name).map liftHead⟩

private theorem oldWitness_roles (rank : Nat) (env : CommonNominalFullDemand.Environment Row)
    (family : List Old) : RolesCompatible (oldWitnessEnvironment rank env family) env := by
  intro name head
  exact projected_member (env.roles name) head

private theorem newEnvironment_roles (env : CommonFinite.Environment Row) :
    RolesCompatible env (newEnvironment env) := by
  intro name head
  change head ∈ env.roles name ↔ liftHead head ∈ (env.roles name).map liftHead
  simp only [List.mem_map, liftHead_injective.eq_iff, exists_eq_right]

private theorem project_successor_new (rank : Nat)
    (previous : ∀ first last : Old, NewLe rank (embed first) (embed last) ↔ OldLe rank first last)
    (newEnv : CommonNominalFullDemand.Environment Row) (family : List Old) (type : Old)
    (supported : ∀ input ∈ inputs type, input ∈ family)
    (obs : CommonNominalFullDemand.Observation Row) :
    CommonNominalFullDemand.ProbeAt Common.rowLe (rank + 1) newEnv (embed type) obs ↔
      CommonFinite.ProbeAt Common.rowLe (rank + 1)
        (oldWitnessEnvironment rank newEnv family) type (project obs) := by
  apply project_step (oldWitnessEnvironment rank newEnv family) newEnv
    (oldWitness_roles rank newEnv family)
    (fun expected input => ∀ next obs,
      CommonFinite.ProbeAt Common.rowLe rank next input obs →
        CommonFinite.ProbeAt Common.rowLe rank next expected obs)
    (fun expected input => ∀ next obs,
      CommonNominalFullDemand.ProbeAt Common.rowLe rank next input obs →
        CommonNominalFullDemand.ProbeAt Common.rowLe rank next expected obs) type _ [] obs
  apply (compatible_iff _ _ _ _ _).mpr
  intro input present name
  exact (CommonNominalFullDemand.producerLeAt_iff_probe _ _ _).symm.trans
    ((witness_exact rank previous (newEnv.types name) family input (supported input present)).trans
      (CommonFinite.producerLeAt_iff_probe _ _ _))

private theorem project_successor_old (rank : Nat)
    (previous : ∀ first last : Old, NewLe rank (embed first) (embed last) ↔ OldLe rank first last)
    (oldEnv : CommonFinite.Environment Row) (type : Old)
    (obs : CommonNominalFullDemand.Observation Row) :
    CommonNominalFullDemand.ProbeAt Common.rowLe (rank + 1) (newEnvironment oldEnv) (embed type) obs ↔
      CommonFinite.ProbeAt Common.rowLe (rank + 1) oldEnv type (project obs) := by
  apply project_step oldEnv (newEnvironment oldEnv) (newEnvironment_roles oldEnv)
    (fun expected input => ∀ next obs,
      CommonFinite.ProbeAt Common.rowLe rank next input obs →
        CommonFinite.ProbeAt Common.rowLe rank next expected obs)
    (fun expected input => ∀ next obs,
      CommonNominalFullDemand.ProbeAt Common.rowLe rank next input obs →
        CommonNominalFullDemand.ProbeAt Common.rowLe rank next expected obs) type _ [] obs
  apply (compatible_iff _ _ _ _ _).mpr
  intro input _ name
  exact (CommonNominalFullDemand.producerLeAt_iff_probe _ _ _).symm.trans
    ((previous (oldEnv.types name) input).trans (CommonFinite.producerLeAt_iff_probe _ _ _))

/-- Every rank and every pair of old finite types. The forward and backward
proofs quantify arbitrary extended environments; no nominal-free environment
premise is introduced. The finite intersection witness is shared by every
arrow input observed in both endpoints. -/
theorem finite_order_rank_exact (rank : Nat) (first last : Old) :
    NewLe rank (embed first) (embed last) ↔ OldLe rank first last := by
  induction rank generalizing first last with
  | zero =>
      constructor
      · intro below
        apply (CommonFinite.producerLeAt_iff_probe _ _ _).mpr
        intro env obs accepted
        have translated : CommonNominalFullDemand.ProbeAt Common.rowLe 0
            (newEnvironment env) (embed last) (lift obs) := by
          apply (project_zero env (newEnvironment env) (newEnvironment_roles env) last (lift obs)).mpr
          simpa only [project_lift] using accepted
        have supplied := (CommonNominalFullDemand.producerLeAt_iff_probe _ _ _).mp below _ _ translated
        simpa only [project_lift] using
          (project_zero env (newEnvironment env) (newEnvironment_roles env) first (lift obs)).mp supplied
      · intro below
        apply (CommonNominalFullDemand.producerLeAt_iff_probe _ _ _).mpr
        intro env obs accepted
        let oldEnv : CommonFinite.Environment Row := ⟨fun _ => .bottom, fun name => (env.roles name).filterMap projectHead⟩
        apply (project_zero oldEnv env (fun name head => projected_member (env.roles name) head) first obs).mpr
        exact (CommonFinite.producerLeAt_iff_probe _ _ _).mp below _ _
          ((project_zero oldEnv env (fun name head => projected_member (env.roles name) head) last obs).mp accepted)
  | succ rank previous =>
      constructor
      · intro below
        apply (CommonFinite.producerLeAt_iff_probe _ _ _).mpr
        intro env obs accepted
        have translated : CommonNominalFullDemand.ProbeAt Common.rowLe (rank + 1)
            (newEnvironment env) (embed last) (lift obs) := by
          apply (project_successor_old rank previous env last (lift obs)).mpr
          simpa only [project_lift] using accepted
        have supplied := (CommonNominalFullDemand.producerLeAt_iff_probe _ _ _).mp below _ _ translated
        simpa only [project_lift] using
          (project_successor_old rank previous env first (lift obs)).mp supplied
      · intro below
        apply (CommonNominalFullDemand.producerLeAt_iff_probe _ _ _).mpr
        intro env obs accepted
        let family := inputs first ++ inputs last
        have firstSupport : ∀ input ∈ inputs first, input ∈ family :=
          fun _ member => List.mem_append.mpr (Or.inl member)
        have lastSupport : ∀ input ∈ inputs last, input ∈ family :=
          fun _ member => List.mem_append.mpr (Or.inr member)
        apply (project_successor_new rank previous env family first firstSupport obs).mpr
        exact (CommonFinite.producerLeAt_iff_probe _ _ _).mp below _ _
          ((project_successor_new rank previous env family last lastSupport obs).mp accepted)

/-- The previously missing finite conservativity proposition, now proved. -/
theorem finite_order_conservative (first last : CommonFinite.Ty Row) :
    CommonNominalFullDemand.ProducerLe Common.rowLe (embed first) (embed last) ↔
      CommonFinite.ProducerLe Common.rowLe first last := by
  exact forall_congr' fun rank => finite_order_rank_exact rank first last

/-- Arbitrary old Common types, with arbitrary regular graphs, default/mask
records, arrows and rows. Their order is preserved and reflected in the full
nested nominal/float carrier, without an extra hypothesis. -/
theorem common_subtype_exact (first last : Common.Ty) :
    CommonNominalFullCarrier.Subtype (CommonNominalEmbedding.embed first) (CommonNominalEmbedding.embed last) ↔
      Common.Subtype first last := by
  unfold CommonNominalFullCarrier.Subtype Common.Subtype
  apply forall_congr'
  intro depth
  change CommonNominalFullDemand.ProducerLe Common.rowLe
      (CommonNominalCarrier.observeTy depth (CommonNominalEmbedding.embed first))
      (CommonNominalCarrier.observeTy depth (CommonNominalEmbedding.embed last)) ↔ _
  rw [CommonNominalEmbedding.observe_embed, CommonNominalEmbedding.observe_embed]
  exact finite_order_conservative _ _

end Yulang.CommonNominalFullConservativity
