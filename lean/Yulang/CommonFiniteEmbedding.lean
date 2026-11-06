import Yulang.CommonFinite

/-!
# Conservativity of contextual comparison inside the common finite carrier

The demand environment may contain arbitrary new presence, default and mask
producer types. To compare finitely many old types, each such parameter is
represented by a finite intersection of the old arrow domains that it satisfies.
This finite witness preserves every relevant negative test. It is constructed
only in the proof and is not a restriction on allowed parameter assignments.
-/

namespace Yulang.CommonFiniteEmbedding

open Inference

universe u
variable {Row : Type u}

/-- The old finite constructors embed without changing any type or row slot. -/
def embedOld : StructuralBase.Ty Row → CommonFinite.Ty Row
  | .base base => .base base
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (embedOld first) (embedOld last)
  | .inter first last => .inter (embedOld first) (embedOld last)
  | .pair first last => .pair (embedOld first) (embedOld last)
  | .emptyRecord => .emptyRecord
  | .record label payload rest => .record label (embedOld payload) (embedOld rest)
  | .variant label payload => .variant label (embedOld payload)
  | .arrow input inputRow output outputRow => .arrow (embedOld input) inputRow (embedOld output) outputRow

/-- Every old observation is still available literally. -/
def embedObservation : ProducerContextual.Observation Row → CommonFinite.Observation Row
  | .trivial => .trivial
  | .impossible => .impossible
  | .base base => .base base
  | .records => .records
  | .role name => .role name
  | .pairFirst obs => .pairFirst (embedObservation obs)
  | .pairLast obs => .pairLast (embedObservation obs)
  | .field label obs => .field label (embedObservation obs)
  | .variant label obs => .variant label (embedObservation obs)
  | .arrowArgument name => .arrowArgument name
  | .arrowResult obs => .arrowResult (embedObservation obs)
  | .arrowInputRow row => .arrowInputRow row
  | .arrowOutputRow row => .arrowOutputRow row

/-- On old producers optional-trivial asks for record shape; every other
optional observation asks for the old field observation of its payload. -/
def projectObservation : CommonFinite.Observation Row → ProducerContextual.Observation Row
  | .trivial => .trivial
  | .impossible => .impossible
  | .base base => .base base
  | .records => .records
  | .role name => .role name
  | .pairFirst obs => .pairFirst (projectObservation obs)
  | .pairLast obs => .pairLast (projectObservation obs)
  | .field label obs => .field label (projectObservation obs)
  | .optional _ .trivial => .records
  | .optional label obs => .field label (projectObservation obs)
  | .variant label obs => .variant label (projectObservation obs)
  | .arrowArgument name => .arrowArgument name
  | .arrowResult obs => .arrowResult (projectObservation obs)
  | .arrowInputRow row => .arrowInputRow row
  | .arrowOutputRow row => .arrowOutputRow row

@[simp] theorem project_embed_observation (obs : ProducerContextual.Observation Row) :
    projectObservation (embedObservation obs) = obs := by
  induction obs <;> simp_all [embedObservation, projectObservation]

@[simp] theorem project_observation_trivial (obs : CommonFinite.Observation Row) :
    projectObservation obs = .trivial ↔ obs = .trivial := by
  cases obs with
  | optional label payload => cases payload <;> simp [projectObservation]
  | _ => simp [projectObservation]

@[simp] theorem project_optional_trivial (label : Nat) :
    projectObservation (.optional label (.trivial : CommonFinite.Observation Row)) = .records := rfl

theorem project_optional_nontrivial (label : Nat) (obs : CommonFinite.Observation Row)
    (nontrivial : obs ≠ .trivial) :
    projectObservation (.optional label obs) = .field label (projectObservation obs) := by
  cases obs <;> simp_all [projectObservation]

/-- A finite list suffices for all negative observations of one old type.
Repeated domains are harmless and preserve the original syntax identities. -/
def arrowDomains : StructuralBase.Ty Row → List (StructuralBase.Ty Row)
  | .base _ | .bottom | .top | .emptyRecord => []
  | .union first last | .inter first last | .pair first last |
      .record _ first last => arrowDomains first ++ arrowDomains last
  | .variant _ payload => arrowDomains payload
  | .arrow input _ output _ => input :: (arrowDomains input ++ arrowDomains output)

variable {leRow : Row → Row → Prop}

/-- Transport of one observation, assuming agreement only on the finitely
many arrow domains actually present in the observed old producer. -/
theorem probeStep_embed_project
    (newEnv : CommonFinite.Environment Row) (oldEnv : ProducerContextual.Environment Row)
    (newOrder : CommonFinite.Ty Row → CommonFinite.Ty Row → Prop)
    (oldOrder : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (roles : newEnv.roles = oldEnv.roles) (type : StructuralBase.Ty Row)
    (arguments : ∀ name domain, domain ∈ arrowDomains type →
      (newOrder (newEnv.types name) (embedOld domain) ↔ oldOrder (oldEnv.types name) domain))
    (obs : CommonFinite.Observation Row) :
    CommonFinite.ProbeStep leRow newEnv newOrder (embedOld type) obs ↔
      ProducerContextual.ProbeStep leRow oldEnv oldOrder type (projectObservation obs) := by
  induction type generalizing obs with
  | bottom => simp [embedOld, CommonFinite.probeStep_bottom, ProducerContextual.probeStep_bottom]
  | top =>
      cases obs with
      | optional label payload => cases payload <;>
          simp [embedOld, projectObservation, CommonFinite.ProbeStep,
            CommonFinite.MaskedProbeStep, ProducerContextual.ProbeStep]
      | _ => simp [embedOld, projectObservation, CommonFinite.ProbeStep,
          CommonFinite.MaskedProbeStep, ProducerContextual.ProbeStep]
  | base base =>
      cases obs with
      | optional label payload => cases payload <;>
          simp [embedOld, projectObservation, CommonFinite.ProbeStep,
            CommonFinite.MaskedProbeStep, ProducerContextual.ProbeStep]
      | _ => simp [embedOld, projectObservation, CommonFinite.ProbeStep,
          CommonFinite.MaskedProbeStep, ProducerContextual.ProbeStep, roles]
  | union first last ihf ihl =>
      have firstArgs := fun name domain member => arguments name domain (List.mem_append_left _ member)
      have lastArgs := fun name domain member => arguments name domain (List.mem_append_right _ member)
      exact (CommonFinite.probeStep_union _ _ obs).trans
        ((and_congr (ihf firstArgs obs) (ihl lastArgs obs)).trans
          (ProducerContextual.probeStep_union first last (projectObservation obs)).symm)
  | inter first last ihf ihl =>
      have firstArgs := fun name domain member => arguments name domain (List.mem_append_left _ member)
      have lastArgs := fun name domain member => arguments name domain (List.mem_append_right _ member)
      exact (CommonFinite.probeStep_inter _ _ obs).trans
        ((or_congr (ihf firstArgs obs) (ihl lastArgs obs)).trans
          (ProducerContextual.probeStep_inter first last (projectObservation obs)).symm)
  | pair first last ihf ihl =>
      have firstArgs := fun name domain member => arguments name domain (List.mem_append_left _ member)
      have lastArgs := fun name domain member => arguments name domain (List.mem_append_right _ member)
      cases obs with
      | pairFirst obs => exact ihf firstArgs obs
      | pairLast obs => exact ihl lastArgs obs
      | optional label payload => cases payload <;>
          simp [embedOld, projectObservation, CommonFinite.ProbeStep,
            CommonFinite.MaskedProbeStep, ProducerContextual.ProbeStep]
      | _ => simp [embedOld, projectObservation, CommonFinite.ProbeStep,
          CommonFinite.MaskedProbeStep, ProducerContextual.ProbeStep, roles]
  | emptyRecord =>
      cases obs with
      | optional label payload =>
          cases payload <;> simp [embedOld, projectObservation, CommonFinite.ProbeStep,
            CommonFinite.MaskedProbeStep, ProducerContextual.ProbeStep]
      | _ => simp [embedOld, projectObservation, CommonFinite.ProbeStep,
          CommonFinite.MaskedProbeStep, ProducerContextual.ProbeStep, roles]
  | record current payload rest ihp ihr =>
      have payloadArgs := fun name domain member => arguments name domain (List.mem_append_left _ member)
      have restArgs := fun name domain member => arguments name domain (List.mem_append_right _ member)
      cases obs with
      | field label obs =>
          by_cases same : label = current
          · subst label
            simpa [embedOld, projectObservation, CommonFinite.ProbeStep,
              CommonFinite.MaskedProbeStep, ProducerContextual.ProbeStep] using ihp payloadArgs obs
          · simpa [embedOld, projectObservation, CommonFinite.ProbeStep,
              CommonFinite.MaskedProbeStep, ProducerContextual.ProbeStep, same] using
              ihr restArgs (.field label obs)
      | optional label obs =>
          by_cases trivial : obs = .trivial
          · subst obs
            simp [embedOld, projectObservation, CommonFinite.ProbeStep,
              CommonFinite.MaskedProbeStep, ProducerContextual.ProbeStep]
          · rw [project_optional_nontrivial label obs trivial]
            by_cases same : label = current
            · subst label
              simpa [embedOld, CommonFinite.ProbeStep,
                CommonFinite.MaskedProbeStep, ProducerContextual.ProbeStep] using ihp payloadArgs obs
            · simpa [embedOld, CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep,
                ProducerContextual.ProbeStep, project_optional_nontrivial label obs trivial,
                same, trivial] using ihr restArgs (.optional label obs)
      | _ => simp [embedOld, projectObservation, CommonFinite.ProbeStep,
          CommonFinite.MaskedProbeStep, ProducerContextual.ProbeStep, roles]
  | variant current payload ih =>
      cases obs with
      | variant label obs => exact and_congr Iff.rfl (ih arguments obs)
      | optional label payload => cases payload <;>
          simp [embedOld, projectObservation, CommonFinite.ProbeStep,
            CommonFinite.MaskedProbeStep, ProducerContextual.ProbeStep]
      | _ => simp [embedOld, projectObservation, CommonFinite.ProbeStep,
          CommonFinite.MaskedProbeStep, ProducerContextual.ProbeStep, roles]
  | arrow input inputRow output outputRow ihi iho =>
      have outputArgs := fun name domain member =>
        arguments name domain (List.mem_cons_of_mem _ (List.mem_append_right _ member))
      cases obs with
      | arrowArgument name => exact arguments name input List.mem_cons_self
      | arrowResult obs => exact iho outputArgs obs
      | optional label payload => cases payload <;>
          simp [embedOld, projectObservation, CommonFinite.ProbeStep,
            CommonFinite.MaskedProbeStep, ProducerContextual.ProbeStep]
      | _ => simp [embedOld, projectObservation, CommonFinite.ProbeStep,
          CommonFinite.MaskedProbeStep, ProducerContextual.ProbeStep, roles]


/-- Observation-only form of the independently defined ranked order. -/
def NewCompare (leRow : Row → Row → Prop) (rank : Nat)
    (source target : CommonFinite.Ty Row) : Prop :=
  ∀ env obs, CommonFinite.ProbeAt leRow rank env target obs →
    CommonFinite.ProbeAt leRow rank env source obs

def OldCompare (leRow : Row → Row → Prop) (rank : Nat)
    (source target : StructuralBase.Ty Row) : Prop :=
  ∀ env obs, ProducerContextual.ProbeAt leRow rank env target obs →
    ProducerContextual.ProbeAt leRow rank env source obs

private theorem newCompare_trans (rank : Nat) {first middle last : CommonFinite.Ty Row}
    (left : NewCompare leRow rank first middle) (right : NewCompare leRow rank middle last) :
    NewCompare leRow rank first last :=
  fun env obs accepted => left env obs (right env obs accepted)

private theorem newCompare_top (rank : Nat) (source : CommonFinite.Ty Row) :
    NewCompare leRow rank source .top := by
  intro env obs accepted
  cases obs <;> cases rank <;>
    simp_all [CommonFinite.ProbeAt, CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]

private theorem newCompare_inter_iff (rank : Nat) (source first last : CommonFinite.Ty Row) :
    NewCompare leRow rank source (.inter first last) ↔
      NewCompare leRow rank source first ∧ NewCompare leRow rank source last := by
  simp only [NewCompare, CommonFinite.probeAt_inter, or_imp, forall_and]

/-- A finite intersection of old types, with the genuine top as empty meet. -/
def meet : List (StructuralBase.Ty Row) → StructuralBase.Ty Row
  | [] => .top
  | type :: rest => .inter type (meet rest)

private theorem oldMeet_below (rank : Nat) (types : List (StructuralBase.Ty Row))
    (type : StructuralBase.Ty Row) (member : type ∈ types) :
    OldCompare leRow rank (meet types) type := by
  induction types with
  | nil => cases member
  | cons first rest ih =>
      intro env obs accepted
      change ProducerContextual.ProbeAt leRow rank env (.inter first (meet rest)) obs
      apply (ProducerContextual.probeAt_inter rank first (meet rest) obs).mpr
      rcases List.mem_cons.mp member with rfl | member
      · exact .inl accepted
      · exact .inr (ih member env obs accepted)

private theorem newCompare_meet_iff (rank : Nat) (source : CommonFinite.Ty Row)
    (types : List (StructuralBase.Ty Row)) :
    NewCompare leRow rank source (embedOld (meet types)) ↔
      ∀ type ∈ types, NewCompare leRow rank source (embedOld type) := by
  induction types with
  | nil =>
      simp only [meet, embedOld, List.not_mem_nil, false_implies, implies_true]
      exact iff_true_intro (newCompare_top rank source)
  | cons first rest ih =>
      simpa only [meet, embedOld, List.mem_cons, forall_eq_or_imp, newCompare_inter_iff] using
        and_congr_right (fun _ => ih)

/-- Proof witness for finitely many negative queries. The actual environment
remains unrestricted; filtering by ranked truth is not part of inference. -/
noncomputable def relevantMeet (leRow : Row → Row → Prop) (rank : Nat)
    (types : List (StructuralBase.Ty Row)) (parameter : CommonFinite.Ty Row) : StructuralBase.Ty Row := by
  classical
  exact meet (types.filter fun type => decide (NewCompare leRow rank parameter (embedOld type)))

private theorem parameter_below_relevantMeet (rank : Nat) (types : List (StructuralBase.Ty Row))
    (parameter : CommonFinite.Ty Row) :
    NewCompare leRow rank parameter (embedOld (relevantMeet leRow rank types parameter)) := by
  classical
  apply (newCompare_meet_iff rank parameter _).mpr
  intro type member
  exact of_decide_eq_true (List.mem_filter.mp member).2

/-- The finite meet represents precisely the parameter's truth values on the
specified domains. Only preservation at the lower rank is needed. -/
theorem relevantMeet_exact (rank : Nat)
    (preserves : ∀ first last, OldCompare leRow rank first last →
      NewCompare leRow rank (embedOld first) (embedOld last))
    (types : List (StructuralBase.Ty Row)) (parameter : CommonFinite.Ty Row)
    (type : StructuralBase.Ty Row) (member : type ∈ types) :
    NewCompare leRow rank parameter (embedOld type) ↔
      OldCompare leRow rank (relevantMeet leRow rank types parameter) type := by
  classical
  constructor
  · intro accepted
    exact oldMeet_below rank _ type (List.mem_filter.mpr ⟨member, by simpa using accepted⟩)
  · intro accepted
    exact newCompare_trans rank (parameter_below_relevantMeet rank types parameter)
      (preserves _ _ accepted)

def embedEnvironment (env : ProducerContextual.Environment Row) : CommonFinite.Environment Row :=
  ⟨fun name => embedOld (env.types name), env.roles⟩

noncomputable def realizeEnvironment (leRow : Row → Row → Prop) (rank : Nat)
    (types : List (StructuralBase.Ty Row)) (env : CommonFinite.Environment Row) :
    ProducerContextual.Environment Row :=
  ⟨fun name => relevantMeet leRow rank types (env.types name), env.roles⟩

/-- The extended environment adds no order between old finite types. Its
parameters may still be arbitrary exact/default/masked producer types. -/
theorem comparison_embedding_exact (leRow : Row → Row → Prop) (rank : Nat)
    (source target : StructuralBase.Ty Row) :
    NewCompare leRow rank (embedOld source) (embedOld target) ↔
      OldCompare leRow rank source target := by
  induction rank generalizing source target with
  | zero =>
      constructor
      · intro below env obs accepted
        have transport (type : StructuralBase.Ty Row) :
            CommonFinite.ProbeAt leRow 0 (embedEnvironment env) (embedOld type) (embedObservation obs) ↔
              ProducerContextual.ProbeAt leRow 0 env type obs := by
          simpa only [CommonFinite.ProbeAt, ProducerContextual.ProbeAt, project_embed_observation] using
            probeStep_embed_project (leRow := leRow) (embedEnvironment env) env
              (fun _ _ => True) (fun _ _ => True) rfl type (fun _ _ _ => Iff.rfl) (embedObservation obs)
        exact (transport source).mp (below (embedEnvironment env) (embedObservation obs)
          ((transport target).mpr accepted))
      · intro below env obs accepted
        let oldEnv : ProducerContextual.Environment Row := ⟨fun _ => .top, env.roles⟩
        have transport (type : StructuralBase.Ty Row) :
            CommonFinite.ProbeAt leRow 0 env (embedOld type) obs ↔
              ProducerContextual.ProbeAt leRow 0 oldEnv type (projectObservation obs) :=
          probeStep_embed_project env oldEnv (fun _ _ => True) (fun _ _ => True) rfl type
            (fun _ _ _ => Iff.rfl) obs
        exact (transport source).mpr (below oldEnv (projectObservation obs) ((transport target).mp accepted))
  | succ rank ih =>
      constructor
      · intro below env obs accepted
        have transport (type : StructuralBase.Ty Row) :
            CommonFinite.ProbeAt leRow (rank + 1) (embedEnvironment env) (embedOld type) (embedObservation obs) ↔
              ProducerContextual.ProbeAt leRow (rank + 1) env type obs := by
          change CommonFinite.ProbeStep leRow (embedEnvironment env) (NewCompare leRow rank)
            (embedOld type) (embedObservation obs) ↔
              ProducerContextual.ProbeStep leRow env (OldCompare leRow rank) type obs
          simpa only [project_embed_observation] using
            probeStep_embed_project (leRow := leRow) (embedEnvironment env) env
              (NewCompare leRow rank) (OldCompare leRow rank) rfl type
              (fun name domain _ => ih (env.types name) domain) (embedObservation obs)
        exact (transport source).mp (below (embedEnvironment env) (embedObservation obs)
          ((transport target).mpr accepted))
      · intro below env obs accepted
        let types := arrowDomains source ++ arrowDomains target
        let oldEnv := realizeEnvironment leRow rank types env
        have preserves : ∀ first last, OldCompare leRow rank first last →
            NewCompare leRow rank (embedOld first) (embedOld last) :=
          fun first last => (ih first last).mpr
        have transport (type : StructuralBase.Ty Row)
            (available : ∀ domain ∈ arrowDomains type, domain ∈ types) :
            CommonFinite.ProbeAt leRow (rank + 1) env (embedOld type) obs ↔
              ProducerContextual.ProbeAt leRow (rank + 1) oldEnv type (projectObservation obs) := by
          exact probeStep_embed_project env oldEnv (NewCompare leRow rank) (OldCompare leRow rank) rfl type
            (fun name domain member => relevantMeet_exact rank preserves types (env.types name) domain
              (available domain member)) obs
        have sourceTransport := transport source (fun _ member => List.mem_append_left _ member)
        have targetTransport := transport target (fun _ member => List.mem_append_right _ member)
        exact sourceTransport.mpr (below oldEnv (projectObservation obs) (targetTransport.mp accepted))

/-- Rank-by-rank preservation and reflection, without a finite restriction on
the common demand parameter family and without row preorder assumptions. -/
theorem contextual_embedding_exact_at (leRow : Row → Row → Prop) (rank : Nat)
    (source target : StructuralBase.Ty Row) :
    CommonFinite.ProducerLeAt leRow rank (embedOld source) (embedOld target) ↔
      ProducerContextual.ProducerLeAt leRow rank source target :=
  (CommonFinite.producerLeAt_iff_probe rank _ _).trans
    ((comparison_embedding_exact leRow rank source target).trans
      (ProducerContextual.producerLeAt_iff_probe rank source target).symm)

/-- Arbitrary old finite types, including nested arrows, arbitrary common
parameter assignments, all ranks and every row relation. -/
theorem contextual_embedding_exact (leRow : Row → Row → Prop)
    (source target : StructuralBase.Ty Row) :
    CommonFinite.ProducerLe leRow (embedOld source) (embedOld target) ↔
      ProducerContextual.ProducerLe leRow source target :=
  forall_congr' fun rank => contextual_embedding_exact_at leRow rank source target

end Yulang.CommonFiniteEmbedding
