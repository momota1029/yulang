import Yulang.GeneralRebaseSliceCertificate283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseSliceEvidence283
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedEvidence231 (Certificate Instance)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralRebaseSliceCertificate283 (readPlan certificate)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSeedLedger237 (Recorded)
open GeneralNominalVersionedMixedRegistry234 (LegacyEmpty)
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralRebaseInstallCache283 (Valid interpret)
open GeneralRebaseSliceJournal283 (sliced journalReads)

def Local (family : List (Plan roles)) (r : Registry) (s : GeneralNominalCenteredSteps.State roles)
    (m : Assignment) : LocalInstance roles :=
  fun focus key children => ∃ p ∈ family, Certificate r s m focus key children p

def Evidence (family : List (Plan roles)) (r : Registry) (s : State roles)
    (m : Assignment) (focus : Occurrence roles) (payload : Payload) : Prop :=
  ErasedEvidence (Local family r s.core m) focus payload

def reads (family : List (Plan roles)) := family.flatMap readPlan

theorem local_eq (family : List (Plan roles)) (r : Registry) (s : State roles)
    {a b : Assignment} (rows : ∀ n, (a n).2 = (b n).2)
    (types : ∀ n ∈ reads family, (a n).1 = (b n).1) :
    Local family r s.core a = Local family r s.core b := by
  funext focus key children
  apply propext
  apply exists_congr; intro plan
  apply and_congr_right; intro present
  exact certificate r s.core plan rows
    (fun n found => types n (List.mem_flatMap.mpr ⟨plan,present,found⟩)) focus key children

theorem evidence_iff (family : List (Plan roles)) (r : Registry) (s : State roles)
    {a b : Assignment} (rows : ∀ n, (a n).2 = (b n).2)
    (types : ∀ n ∈ reads family, (a n).1 = (b n).1) (focus : Occurrence roles) (data : Payload) :
    Evidence family r s a focus data ↔ Evidence family r s b focus data := by
  unfold Evidence
  rw [local_eq family r s rows types]

theorem indexed_mono {roles : Roles.RoleDecls} {A B : LocalInstance roles}
    (local_mono : ∀ focus key cs, A focus key cs → B focus key cs)
    {tree : Dictionary roles} (h : GeneralSourceDictionaries.Evidence A tree) :
    GeneralSourceDictionaries.Evidence B tree := by
  induction h with
  | node instanceRule children ih => exact .node (local_mono _ _ _ instanceRule) ih

theorem subset {s : State roles} {r : Registry} {m : Assignment} {A B : List (Plan roles)} (h : A ⊆ B) {tree : Dictionary roles}
    (ev : GeneralSourceDictionaries.Evidence (Local A r s.core m) tree) :
    GeneralSourceDictionaries.Evidence (Local B r s.core m) tree := by
  apply indexed_mono ?_ ev
  rintro _ _ _ ⟨p,present,certificate⟩
  exact ⟨p,h present,certificate⟩

theorem combine (r : Registry) (s : State roles) (m : Assignment) (children : List (Dictionary roles))
    (provided : ∀ c ∈ children, ∃ family, GeneralSourceDictionaries.Evidence (Local family r s.core m) c) :
    ∃ family, ∀ c ∈ children, GeneralSourceDictionaries.Evidence (Local family r s.core m) c := by
  induction children with
  | nil => exact ⟨[],fun _ member => False.elim (List.not_mem_nil member)⟩
  | cons head rest ih =>
    obtain ⟨front,left⟩ := provided head List.mem_cons_self
    obtain ⟨back,right⟩ := ih (fun c mem => provided c (List.mem_cons_of_mem _ mem))
    refine ⟨front ++ back,?_⟩
    intro child listed
    rcases List.mem_cons.mp listed with rfl|listed
    · exact subset (fun {_} h => List.mem_append_left _ h) left
    · exact subset (fun {_} h => List.mem_append_right _ h) (right child listed)

theorem finite_choices (r : Registry) (s : State roles) (a : Assignment) {tree : Dictionary roles}
    (held : GeneralSourceDictionaries.Evidence (Instance r s.core a) tree) :
    ∃ family, GeneralSourceDictionaries.Evidence (Local family r s.core a) tree := by
  induction held with
  | @node focus key cs instanceRule children ih =>
    obtain ⟨p,frame⟩ := instanceRule
    obtain ⟨tail,evidence⟩ := combine r s a cs ih
    refine ⟨p :: tail,.node ⟨p,List.mem_cons_self,frame⟩ ?_⟩
    exact fun child present => subset (fun {_} h => List.mem_cons_of_mem _ h) (evidence child present)

theorem full (r : Registry) (s : State roles) (a : Assignment) (focus : Occurrence roles) (data : Payload) :
    GeneralNominalVersionedEvidence231.Evidence r s.core a focus data ↔ ∃ family, Evidence family r s a focus data := by
  constructor
  · rintro ⟨tree,erase,held⟩
    obtain ⟨family,limited⟩ := finite_choices r s a held
    exact ⟨family,tree,erase,limited⟩
  · rintro ⟨family,tree,erase,held⟩
    refine ⟨tree,erase,indexed_mono ?_ held⟩
    rintro _ _ _ ⟨p,_,certificate⟩
    exact ⟨p,certificate⟩

theorem evidence_slice {cache : List (Entry Nat)} {state : State roles}
    (valid : Valid cache state) (rec : Recorded state) (r : Registry)
    (family : List (Plan roles)) {query : List Nat} (covered : reads family ⊆ query)
    (base : Assignment) (focus : Occurrence roles) (data : Payload) :
    Evidence family r state (sliced cache query base) focus data ↔
      Evidence family r state (interpret cache base) focus data :=
  evidence_iff family r state (GeneralRebaseSliceJournal283.rows_same cache query base)
    (fun n seen => congrArg Prod.fst (GeneralRebaseSliceJournal283.agrees valid rec query base n (covered seen))) focus data

theorem exact_finite_query {cache : List (Entry Nat)} {state : State roles}
    (valid : Valid cache state) (rec : Recorded state) (empty : LegacyEmpty state) (r : Registry)
    (base : Assignment) (focus : Occurrence roles) (data : Payload) :
    (Models state (interpret cache base) ∧ GeneralNominalVersionedEvidence231.Evidence r state.core (interpret cache base) focus data) ↔
    ∃ family, Models state (sliced cache (journalReads state ++ reads family) base) ∧
      Evidence family r state (sliced cache (journalReads state ++ reads family) base) focus data := by
  rw [full]
  constructor
  · rintro ⟨model,family,held⟩
    exact ⟨family,(GeneralRebaseSliceJournal283.journal valid rec empty (fun {_} h => List.mem_append_left _ h) base).mpr model,
      (evidence_slice valid rec r family (fun {_} h => List.mem_append_right _ h) base focus data).mpr held⟩
  · rintro ⟨family,model,held⟩
    exact ⟨(GeneralRebaseSliceJournal283.journal valid rec empty (fun {_} h => List.mem_append_left _ h) base).mp model,
      family,(evidence_slice valid rec r family (fun {_} h => List.mem_append_right _ h) base focus data).mp held⟩

end Yulang.GeneralRebaseSliceEvidence283
