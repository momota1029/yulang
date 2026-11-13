import Yulang.GeneralNominalDownstreamSupport

/-! Value-subterm support for provisional outputs. Certified paths use the
same normalized structural and explicit nominal argument edges as journal K2.
They never traverse nominal bodies. A variable capture does not erase a known
head below its value. This module defines the stronger support contract; a
concrete multiargument execution is a separate obligation. -/
namespace Yulang.GeneralNominalValueSupport
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportChoices
open GeneralNominalRecursiveInspection (Test)

abbrev Available := @GeneralNominalDownstreamSupport.Available
abbrev View := @GeneralNominalDownstreamSupport.View
abbrev Waiting := @GeneralNominalDownstreamSupport.Waiting

abbrev Realizes (state : State roles) (origin : GeneralNominalRecursiveInspection.Origin) (identity : Nat) :=
  GeneralNominalDemandMerging.SameOrigin (Models state) origin (.source identity)

/-- At least one where-generation edge, with alias-aware waiting before
and after it. A producer's irrelevant unused capture is not a new dependency. -/
def ProperWaiting (state : State roles) (producer child : Occurrence roles) : Prop :=
  ∃ parent first, Waiting state producer parent ∧ (parent,first) ∈ state.edges ∧
    ¬ Discharged state first ∧ Waiting state first child

theorem proper_prefix (leading : Waiting state first middle) (path : ProperWaiting state middle last) :
    ProperWaiting state first last := by
  obtain ⟨parent,child,before,edge,unresolved,after⟩ := path
  exact ⟨parent,child,GeneralNominalDownstreamSupport.waiting_trans leading before,edge,unresolved,after⟩

/-- Old inspection reads and known subterm heads of generated unnamed inputs.
Paths are checked against a certified observation view of the full journal;
unknown subterms supply no head and are not converted into rejection. -/
inductive Need (registry : Registry) (state : Tracked roles) (producer focus : Occurrence roles) : Nat → Test → Prop
  | head : GeneralNominalDownstreamSupport.Need registry state focus identity test →
      Need registry state producer focus identity test
  | value : ProperWaiting state.current producer focus → (observed : State roles) → View state.current observed →
      (index : Fin (roles focus.demand.role).arity) →
      GeneralNominalFeedbackK2.Path observed (focus.demand.arguments index).1 identity →
      (test : Test) → Available state identity test → Need registry state producer focus identity test
  | retained : ProperWaiting state.current producer focus → (observed : State roles) → View state.current observed →
      (site : GeneralNominalDemandMerging.Site roles) → site ∈ observed.sites → site.occurrence = focus →
      (position : Nat) → (origin : GeneralNominalRecursiveInspection.Origin) →
      site.inputs[position]? = some (some origin) → (source : Nat) → Realizes observed origin source →
      GeneralNominalFeedbackK2.Path observed source identity →
      (test : Test) → Available state identity test → Need registry state producer focus identity test

theorem need_prefix (leading : Waiting state.current first middle)
    (needed : Need registry state middle child identity test) : Need registry state first child identity test := by
  cases needed with
  | head old => exact .head old
  | value proper observed view index path test available =>
    exact .value (proper_prefix leading proper) observed view index path test available
  | retained proper observed view site member same position origin recorded source realizes path test available =>
    exact .retained (proper_prefix leading proper) observed view site member same position origin recorded source realizes path test available

theorem need_without_child_path (absent : ¬ ProperWaiting state.current producer focus) :
    Need registry state producer focus identity test ↔
      GeneralNominalDownstreamSupport.Need registry state focus identity test := by
  constructor
  · intro needed
    cases needed with
    | head old => exact old
    | value proper => exact False.elim (absent proper)
    | retained proper => exact False.elim (absent proper)
  · exact Need.head

/-- Only the chosen explanation is followed. An unrelated cyclic explanation
cannot invalidate a source or discharged explanation. No installed-packet
premise is imposed on a child whose needed head is being justified. -/
inductive Grounded (registry : Registry) (state : Tracked roles) : Occurrence roles → Prop
  | discharged (producer : Occurrence roles) : Discharged state.current producer → Grounded registry state producer
  | provisional (producer : Occurrence roles)
      (supports : Occurrence roles → Nat → Test → List (Occurrence roles)) :
      (∀ child, Waiting state.current producer child → ¬ Discharged state.current child →
        ∀ identity test, Need registry state producer child identity test →
          HeadSupported state (supports child identity test) identity test) →
      (∀ child, Waiting state.current producer child → ¬ Discharged state.current child →
        ∀ identity test, Need registry state producer child identity test →
          ∀ dependency ∈ supports child identity test, Grounded registry state dependency) →
      Grounded registry state producer

def Supported (registry : Registry) (state : Tracked roles) (support : List (Occurrence roles)) : Prop :=
  ∀ producer ∈ support, Grounded registry state producer

def PacketGuard (state : Tracked roles) (packet : Packet roles) (support : List (Occurrence roles)) : Prop :=
  GeneralNominalSupportChoices.PacketGuard state packet support ∧ Supported packet.registry state support

def DecisionGuard (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (support : List (Occurrence roles)) : Prop :=
  GeneralNominalSupport.DecisionGuard state registry root support ∧ Supported registry state support

theorem empty_supported (registry : Registry) (state : Tracked roles) : Supported registry state [] := by
  intro _ impossible; cases impossible

theorem source_packet (state : Tracked roles) (packet : Packet roles)
    (guard : GeneralNominalSupportChoices.PacketGuard state packet []) : PacketGuard state packet [] :=
  ⟨guard,empty_supported _ _⟩

theorem source_decision (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (guard : GeneralNominalSupport.DecisionGuard state registry root []) : DecisionGuard registry state root [] :=
  ⟨guard,empty_supported _ _⟩

theorem discharged_supported (registry : Registry) (state : Tracked roles) (support : List (Occurrence roles))
    (done : ∀ producer ∈ support, Discharged state.current producer) : Supported registry state support :=
  fun producer member => .discharged producer (done producer member)

/-- Acyclic provisional explanations remain usable; no child dictionary is
required when the child's available heads already have independent support. -/
theorem provisional_source (registry : Registry) (state : Tracked roles) (producer : Occurrence roles)
    (source : ∀ child, Waiting state.current producer child → ¬ Discharged state.current child →
      ∀ identity test, Need registry state producer child identity test → HeadSupported state [] identity test) :
    Grounded registry state producer :=
  .provisional producer (fun _ _ _ => []) source (by intro _ _ _ _ _ _ _ impossible; cases impossible)

theorem alias_grounded (registry : Registry) (state : Tracked roles)
    (first last : GeneralNominalDemandMerging.Site roles)
    (one : first ∈ state.current.sites) (two : last ∈ state.current.sites)
    (same : Alias state.current first.occurrence.identity last.occurrence.identity)
    (grounded : Grounded registry state first.occurrence) : Grounded registry state last.occurrence := by
  classical
  by_cases done : Discharged state.current last.occurrence
  · exact .discharged _ done
  have firstOpen : ¬ Discharged state.current first.occurrence :=
    fun resolved => done (.alias first last one two same resolved)
  cases grounded with
  | discharged _ resolved => exact False.elim (firstOpen resolved)
  | provisional _ supports heads dependencies =>
    have path : Waiting state.current first.occurrence last.occurrence :=
      .alias first last (.root firstOpen) one two same done
    exact .provisional _ supports
      (fun child reached unresolved identity test needed =>
        heads child (GeneralNominalDownstreamSupport.waiting_trans path reached) unresolved identity test (need_prefix path needed))
      (fun child reached unresolved identity test needed =>
        dependencies child (GeneralNominalDownstreamSupport.waiting_trans path reached) unresolved identity test (need_prefix path needed))

/-- A closed set of unresolved producers with unavoidable head-support return
edges has no inductive justification. The focus need not belong to this set. -/
theorem trap_excluded (registry : Registry) (state : Tracked roles) (trap : Occurrence roles → Prop)
    (unresolved : ∀ producer, trap producer → ¬ Discharged state.current producer)
    (returns : ∀ producer, trap producer → ∃ child,
      Waiting state.current producer child ∧ ¬ Discharged state.current child ∧
      ∃ identity test, Need registry state producer child identity test ∧
        ∀ support, HeadSupported state support identity test → ∃ dependency ∈ support, trap dependency)
    (producer : Occurrence roles) (grounded : Grounded registry state producer) : ¬ trap producer := by
  induction grounded with
  | discharged producer done => exact fun member => unresolved producer member done
  | provisional producer supports heads dependencies ih =>
    intro member
    obtain ⟨child,path,openChild,identity,test,needed,back⟩ := returns producer member
    obtain ⟨dependency,included,trapped⟩ := back (supports child identity test)
      (heads child path openChild identity test needed)
    exact ih child path openChild identity test needed dependency included trapped

theorem downstream_blocked (registry : Registry) (state : Tracked roles)
    (identity : Nat) (test : Test) (trap : Occurrence roles → Prop)
    (excluded : ∀ producer, trap producer → ¬ Grounded registry state producer)
    (necessary : ∀ support, HeadSupported state support identity test → ∃ producer ∈ support, trap producer)
    (support : List (Occurrence roles)) (allowed : Supported registry state support) :
    ¬ HeadSupported state support identity test := by
  intro head
  obtain ⟨producer,member,trapped⟩ := necessary support head
  exact excluded producer trapped (allowed producer member)

theorem need_available (needed : Need registry state producer focus identity test) : Available state identity test := by
  cases needed with
  | head old => exact GeneralNominalDownstreamSupport.need_available old
  | value _ _ _ _ _ _ known => exact known
  | retained _ _ _ _ _ _ _ _ _ _ _ _ _ known => exact known

theorem empty_ledger_grounded (registry : Registry) (state : Tracked roles) (empty : state.facts = [])
    (producer : Occurrence roles) : Grounded registry state producer := by
  apply provisional_source
  intro child _ _ identity test needed
  have supported := need_available needed
  simpa only [GeneralNominalDownstreamSupport.Available,dependencyPool,empty,List.flatMap_nil] using supported

theorem source_conservative_grounded (registry : Registry) (state : Tracked roles)
    (conservative : ∀ model, GeneralNominalState.Models state.source.state model → AllModels state model)
    (producer : Occurrence roles) : Grounded registry state producer := by
  apply provisional_source
  intro child _ _ identity test needed
  obtain ⟨snapshot,observation,head,entailed⟩ := need_available needed
  exact ⟨snapshot,observation,head,fun model valid =>
    entailed model (all_models_slice state _ model (conservative model valid.1))⟩

/-- Forgetting the additional value dependencies recovers the old contract. -/
theorem grounded_old (grounded : Grounded registry state producer) :
    GeneralNominalDownstreamSupport.Grounded registry state producer := by
  induction grounded with
  | discharged producer done => exact .discharged producer done
  | provisional producer supports heads dependencies ih =>
    exact .provisional producer supports
      (fun child path unresolved identity test needed => heads child path unresolved identity test (.head needed))
      (fun child path unresolved identity test needed dependency member =>
        ih child path unresolved identity test (.head needed) dependency member)

theorem supported_old (supported : Supported registry state support) :
    GeneralNominalDownstreamSupport.Supported registry state support :=
  fun producer member => grounded_old (supported producer member)

theorem packet_old (guard : PacketGuard state packet support) :
    GeneralNominalDownstreamSupport.PacketGuard state packet support := ⟨guard.1,supported_old guard.2⟩

theorem decision_old (guard : DecisionGuard registry state root support) :
    GeneralNominalDownstreamSupport.DecisionGuard registry state root support := ⟨guard.1,supported_old guard.2⟩

/-- A known explicit nominal argument remains a dependency even when the
candidate matches it with a variable rather than inspecting its head. -/
theorem nominal_argument_needed (state : Tracked roles) (producer focus : Occurrence roles)
    (proper : ProperWaiting state.current producer focus)
    (index : Fin (roles focus.demand.role).arity) (identity : Nat) (test : Test)
    (parent : (focus.demand.arguments index).1 ∈ GeneralNominalState.sources state.current.context.state)
    (child : identity ∈ GeneralNominalState.sources state.current.context.state)
    (argument : GeneralNominalFeedbackK2.Argument state.current (focus.demand.arguments index).1 identity)
    (known : Available state identity test) : Need registry state producer focus identity test :=
  .value proper state.current .current index (.cons ⟨parent,child,Or.inr argument⟩ (.nil identity)) test known

/-- Equality of endpoints identifies an already retained value. No value
inside a strict interval is selected by this bridge. -/
theorem point_origin_realizes (state : State roles) (site : GeneralNominalDemandMerging.Site roles)
    (member : site ∈ state.sites) (index : Fin (roles site.occurrence.demand.role).arity)
    (origin : GeneralNominalRecursiveInspection.Origin)
    (recorded : site.inputs[index.val]? = some (some origin))
    (equal : GeneralNominalFeedbackSites.EndpointEqual state (site.occurrence.demand.arguments index)) :
    Realizes state origin (site.occurrence.demand.arguments index).1 := by
  intro model valid
  obtain ⟨existsValue,fits⟩ := valid.2.2 site member index origin recorded
  refine ⟨existsValue,⟨_,.source _⟩,?_⟩
  intro actual endpoint seen source
  cases source
  have interval := fits actual seen
  exact ⟨CommonNominalFullCarrier.subtype_trans interval.2 (equal model valid).2,interval.1⟩

/-- Actual-mode materialization equates a named source with a retained
capture origin even when the capture's endpoint interval is not a point. -/
theorem materialized_origin_realizes (state : State roles) (packet : Packet roles)
    (member : packet ∈ state.packets) (name identity : Nat)
    (entry : (⟨name,.source identity,.actual⟩ : GeneralNominalMaterialization.Use) ∈
      (GeneralNominalPacketSupport.namedSchema packet).variables)
    (captured : GeneralNominalRecursiveInspection.Capture packet.context.state)
    (present : captured ∈ (GeneralNominalPacketSupport.report packet).captures)
    (same : name = captured.name) (origin : GeneralNominalRecursiveInspection.Origin)
    (recorded : captured.origin = some origin) : Realizes state origin identity := by
  intro model valid
  have outputs := (GeneralNominalPacketSupport.packet_exact packet model).mp (valid.2.1 packet member) |>.2.2
  have anchor := GeneralNominalCaptureAnchors.report_anchored packet.context packet.declaration packet.bounds
    captured present origin recorded
  have captureExists := (valid.2.1 packet member).2.1.1 (origin,captured.bounds) anchor |>.1
  refine ⟨?_,⟨_,.source identity⟩,?_⟩
  · exact captureExists
  · intro actual endpoint seen source
    cases source
    have eq := outputs.2.2.2 _ entry captured present same rfl origin recorded _ _ (.source identity) seen
    exact ⟨eq.2,eq.1⟩

/-- Two unresolved producers whose waiting inputs expose each other's
unavoidable subterm support cannot ground either output. -/
theorem mutual_value_trap (registry : Registry) (state : Tracked roles)
    (first second : Occurrence roles)
    (unresolved : ∀ producer, producer = first ∨ producer = second → ¬ Discharged state.current producer)
    (returns : ∀ producer, producer = first ∨ producer = second → ∃ child,
      Waiting state.current producer child ∧ ¬ Discharged state.current child ∧
      ∃ identity test, Need registry state producer child identity test ∧
        ∀ support, HeadSupported state support identity test →
          ∃ dependency ∈ support, dependency = first ∨ dependency = second) :
    ¬ Grounded registry state first ∧ ¬ Grounded registry state second :=
  ⟨fun grounded => trap_excluded registry state (fun producer => producer = first ∨ producer = second)
      unresolved returns first grounded (Or.inl rfl),
    fun grounded => trap_excluded registry state (fun producer => producer = first ∨ producer = second)
      unresolved returns second grounded (Or.inr rfl)⟩

/-- A child value that unavoidably uses its unresolved producer's output
cannot justify that producer. The generation edge is an explicit premise. -/
theorem child_value_trap (registry : Registry) (state : Tracked roles)
    (producer child : Occurrence roles) (unresolved : ¬ Discharged state.current producer)
    (waiting : Waiting state.current producer child) (openChild : ¬ Discharged state.current child)
    (proper : ProperWaiting state.current producer child)
    (index : Fin (roles child.demand.role).arity) (identity : Nat) (test : Test)
    (path : GeneralNominalFeedbackK2.Path state.current (child.demand.arguments index).1 identity)
    (known : Available state identity test)
    (necessary : ∀ support, HeadSupported state support identity test → producer ∈ support) :
    ¬ Grounded registry state producer := by
  intro grounded
  apply trap_excluded registry state (fun current => current = producer) ?_ ?_ producer grounded rfl
  · intro current same
    subst current
    exact unresolved
  · intro current same
    subst current
    refine ⟨child,waiting,openChild,identity,test,
      .value proper state.current .current index path test known,?_⟩
    intro support head
    exact ⟨producer,necessary support head,rfl⟩

/-- A concrete model after deleting every fact requiring one producer.
The other producers' equations and every independent alternative remain. -/
structure CutModel (state : Tracked roles) (producer : Occurrence roles)
    (model : GeneralNominalCommonBridge.Assignment) : Prop where
  source : GeneralNominalState.Models state.source.state model
  facts : ∀ fact ∈ state.facts, producer ∉ fact.dependencies → fact.Holds model

theorem cut_slice {roles : Roles.RoleDecls} {state : Tracked roles} {producer : Occurrence roles}
    {model : GeneralNominalCommonBridge.Assignment}
    (cut : CutModel state producer model) (support : List (Occurrence roles))
    (absent : producer ∉ support) : Slice state support model :=
  ⟨cut.source,fun fact member included => cut.facts fact member (fun required => absent (included producer required))⟩

theorem nominal_support_requires_producer (state : Tracked roles) (producer : Occurrence roles)
    (model : GeneralNominalCommonBridge.Assignment) (cut : CutModel state producer model)
    (identity name arity : Nat) (scalar : (model identity).1 = .base .int)
    (support : List (Occurrence roles))
    (supported : HeadSupported state support identity (.nominal name arity)) : producer ∈ support := by
  classical
  apply Classical.byContradiction
  intro absent
  obtain ⟨snapshot,observation,head,entailed⟩ := supported
  have valid := entailed model (cut_slice cut support absent)
  generalize tagEq : GeneralNominalRecursiveInspection.Test.nominal name arity = tag at head
  cases head with
  | scalar => cases tagEq
  | structural => cases tagEq
  | nominal slot descriptor recorded =>
    cases tagEq
    obtain ⟨arguments,_,equal⟩ := valid
    rw [scalar] at equal
    exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (equal.1 0) 0
      ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead _ arguments.length) ⟨rfl,by simp⟩

end Yulang.GeneralNominalValueSupport
