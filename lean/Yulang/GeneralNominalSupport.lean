import Yulang.GeneralNominalPacketSupport

/-! Finite provenance supports, independent of evaluation. An output premise
points back to its producing obligation. Together with the producer's
unresolved where-dependency path, that premise closes a dependency cycle.
Support alternatives are existential: an irrelevant cyclic derivation cannot
invalidate an available source derivation. Refreshes never become premises. -/
namespace Yulang.GeneralNominalSupport

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Test)
open GeneralCanonicalObservations (Observation Recorded)

inductive Discharged (state : State roles) : Occurrence roles → Prop
  | packet (packet : Packet roles) : packet ∈ state.packets →
      (∀ child ∈ packet.children, Discharged state child) → Discharged state packet.site.occurrence
  | alias (first last : GeneralNominalDemandMerging.Site roles) :
      first ∈ state.sites → last ∈ state.sites → Alias state first.occurrence.identity last.occurrence.identity →
      Discharged state first.occurrence → Discharged state last.occurrence

def External (state : State roles) (focus producer : Occurrence roles) : Prop :=
  Discharged state producer ∨ ¬ Generated state producer focus

inductive Fact (roles : Roles.RoleDecls) where
  | inputs (packet : Packet roles) (support : List (Occurrence roles))
  | outputs (packet : Packet roles) (support : List (Occurrence roles))
  | merge (first last : GeneralNominalDemandMerging.Site roles) (support : List (Occurrence roles))

def Fact.dependencies : Fact roles → List (Occurrence roles)
  | .inputs _ support => support
  | .outputs packet support => packet.site.occurrence :: support
  | .merge first last support => first.occurrence :: last.occurrence :: support

def Fact.Holds : Fact roles → Assignment → Prop
  | .inputs packet _, model => GeneralNominalPacketSupport.Inputs packet model
  | .outputs packet _, model => GeneralNominalPacketSupport.Outputs packet model
  | .merge first last _, model => PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalDemandMerging.outputAtoms first last)

structure Tracked (roles : Roles.RoleDecls) where
  source : GeneralNominalCandidates.Context
  current : State roles
  facts : List (Fact roles) := []

def Slice (state : Tracked roles) (support : List (Occurrence roles)) (model : Assignment) : Prop :=
  GeneralNominalState.Models state.source.state model ∧
    ∀ fact ∈ state.facts, (∀ producer ∈ fact.dependencies, producer ∈ support) → fact.Holds model

def AllModels (state : Tracked roles) (model : Assignment) : Prop :=
  GeneralNominalState.Models state.source.state model ∧ ∀ fact ∈ state.facts, fact.Holds model

def Entails (state : Tracked roles) (support : List (Occurrence roles)) (claim : Assignment → Prop) : Prop :=
  ∀ model, Slice state support model → claim model

def Admissible (state : Tracked roles) (focus : Occurrence roles) (support : List (Occurrence roles)) : Prop :=
  ∀ producer ∈ support, External state.current focus producer

def Justified (state : Tracked roles) (focus : Occurrence roles) (claim : Assignment → Prop) : Prop :=
  ∃ support, Admissible state focus support ∧ Entails state support claim

inductive Head (snapshot : GeneralNominalState.State) : Nat → Test → Observation → Prop
  | scalar (slot : Fin snapshot.base.slots) (base : Inference.Base) : snapshot.view.heads slot = .scalar base →
      Head snapshot (snapshot.base.source slot) (.scalar base) (.normalized snapshot.base slot (.base base))
  | structural (slot : Fin snapshot.base.slots) (kind : Fin snapshot.view.kinds)
      (children : Fin (snapshot.view.shapes kind).arity → Fin snapshot.base.slots) :
      snapshot.view.heads slot = .structural kind children →
      Head snapshot (snapshot.base.source slot) (.structural (snapshot.view.shapes kind))
        (.normalized snapshot.base slot ((snapshot.view.shapes kind).term children))
  | nominal (slot : Fin snapshot.base.slots) (descriptor : GeneralNominalState.Descriptor snapshot.base.slots) :
      snapshot.nominals slot = some descriptor →
      Head snapshot (snapshot.base.source slot) (.nominal descriptor.declaration.name descriptor.arguments.length)
        (.nominal snapshot.base slot descriptor)

theorem head_recorded (head : Head snapshot identity test observation) : Recorded snapshot observation := by
  cases head with
  | scalar _ _ seen => exact .scalar _ _ seen
  | structural _ _ _ seen => exact .structural _ _ _ seen
  | nominal _ _ seen => exact .nominal _ _ seen

def HeadSupported (state : Tracked roles) (support : List (Occurrence roles)) (identity : Nat) (test : Test) : Prop :=
  ∃ snapshot observation, Head snapshot identity test observation ∧ Entails state support observation.Holds

/-- A support may use a broader descriptor than the currently cached one;
only the inspected head must coincide. -/
def ReadyAt (state : Tracked roles) (support : List (Occurrence roles)) (identity : Nat) : Prop :=
  ∃ test observation, Head state.current.context.state identity test observation ∧ HeadSupported state support identity test

/- Read exactly the endpoint heads used by the recursive inspector. Variable
patterns add no nested reads; scalar patterns do not read the upper head. -/
mutual
  def reads (snapshot : GeneralNominalState.State) (query : GeneralNominalInspection.Query)
      (bounds : GeneralNominalInspection.Bounds snapshot) : List (Fin snapshot.base.slots) :=
    match query with
    | .variables _ | .deferred _ => []
    | .scalar _ => [bounds.1]
    | .node expected patterns =>
        match snapshot.view.heads bounds.1 with
        | .scalar _ => [bounds.1]
        | _ => [bounds.1,bounds.2] ++ match snapshot.view.heads bounds.1,snapshot.view.heads bounds.2 with
        | .structural lower children,.structural upper targets =>
            if snapshot.view.shapes lower = expected ∧ snapshot.view.shapes upper = expected then
              readsMany snapshot patterns ((List.ofFn children).zip (List.ofFn targets)) else []
        | _,_ => []
    | .nominal expected patterns =>
        bounds.1 :: (match snapshot.nominals bounds.1 with
        | none => []
        | some lower => if lower.declaration.name = expected then
            match GeneralNominalRecursiveInspection.typeArguments lower.arguments with
            | none => []
            | some arguments =>
                if bounds.1 = bounds.2 then readsMany snapshot patterns arguments else bounds.2 ::
                  (match snapshot.nominals bounds.2 with
                  | none => []
                  | some upper => if upper.declaration.name = expected then
                      match GeneralNominalRecursiveInspection.typeArguments upper.arguments with
                      | none => []
                      | some targets => readsMany snapshot patterns arguments ++ readsMany snapshot patterns targets
                    else [])
          else [])
  termination_by sizeOf query

  def readsMany (snapshot : GeneralNominalState.State) : List GeneralNominalInspection.Query →
      List (GeneralNominalInspection.Bounds snapshot) → List (Fin snapshot.base.slots)
    | query :: queries,bounds :: intervals => reads snapshot query bounds ++ readsMany snapshot queries intervals
    | _,_ => []
  termination_by queries _ => sizeOf queries
end

def Roots (state : Tracked roles) (support : List (Occurrence roles)) (root : Occurrence roles) : Prop :=
  ∀ index, ReadyAt state support (root.demand.arguments index).1

def Inspection (state : Tracked roles) (support : List (Occurrence roles))
    (declaration : Declaration) (bounds : List (GeneralNominalInspection.Bounds state.current.context.state)) : Prop :=
  ∀ slot ∈ readsMany state.current.context.state
    (GeneralNominalInspection.queries state.current.context.state state.current.context.interpretation declaration) bounds,
      ReadyAt state support (state.current.context.state.base.source slot)

def Guard (state : Tracked roles) (root : Occurrence roles) (declaration : Declaration)
    (bounds : List (GeneralNominalInspection.Bounds state.current.context.state)) (support : List (Occurrence roles)) : Prop :=
  Admissible state root support ∧ Roots state support root ∧ Inspection state support declaration bounds

/-- Negative applicability decisions need support as well as surviving ones. -/
def DecisionGuard (state : Tracked roles) (registry : Registry) (root : Occurrence roles)
    (support : List (Occurrence roles)) : Prop :=
  Admissible state root support ∧ Roots state support root ∧
    ∀ declaration ∈ registry.declarations, declaration.role = root.demand.role →
      ∀ bounds, GeneralNominalRecursiveCandidates.arguments state.current.context root = some bounds →
        Inspection state support declaration bounds

def initial (context : GeneralNominalCandidates.Context) (root : Occurrence roles) : Tracked roles :=
  ⟨context,GeneralNominalSaturationState.initial context root,[]⟩

theorem source_supported (state : Tracked roles) (identity : Nat) (test : Test) (observation : Observation)
    (source : Head state.source.state identity test observation) (support : List (Occurrence roles)) :
    HeadSupported state support identity test :=
  ⟨state.source.state,observation,source,fun model valid =>
    GeneralCanonicalObservations.recorded_sound _ model valid.1 (head_recorded source)⟩

theorem source_ready (state : Tracked roles) (identity : Nat) (test : Test) (old current : Observation)
    (source : Head state.source.state identity test old)
    (seen : Head state.current.context.state identity test current) (support : List (Occurrence roles)) :
    ReadyAt state support identity := ⟨test,current,seen,source_supported state identity test old source support⟩

theorem source_guard (state : Tracked roles) (root : Occurrence roles) (declaration : Declaration)
    (bounds : List (GeneralNominalInspection.Bounds state.current.context.state))
    (roots : ∀ index, ∃ test old current, Head state.source.state (root.demand.arguments index).1 test old ∧
      Head state.current.context.state (root.demand.arguments index).1 test current)
    (inspected : ∀ slot ∈ readsMany state.current.context.state
      (GeneralNominalInspection.queries state.current.context.state state.current.context.interpretation declaration) bounds,
        ∃ test old current, Head state.source.state (state.current.context.state.base.source slot) test old ∧
          Head state.current.context.state (state.current.context.state.base.source slot) test current) :
    Guard state root declaration bounds [] := by
  refine ⟨(by intro _ impossible; cases impossible),?_,?_⟩
  · intro index
    obtain ⟨test,old,current,source,seen⟩ := roots index
    exact source_ready state _ test old current source seen []
  · intro slot member
    obtain ⟨test,old,current,source,seen⟩ := inspected slot member
    exact source_ready state _ test old current source seen []

theorem discharged_external (state : State roles) (focus producer : Occurrence roles)
    (done : Discharged state producer) : External state focus producer := Or.inl done

theorem cycle_excluded (state : Tracked roles) (focus producer : Occurrence roles)
    (path : Generated state.current producer focus) (unresolved : ¬ Discharged state.current producer)
    (support : List (Occurrence roles)) (allowed : Admissible state focus support) : producer ∉ support := by
  intro member
  rcases allowed producer member with discharged | absent
  · exact unresolved discharged
  · exact absent path

theorem entails_source (state : Tracked roles) (focus : Occurrence roles) (claim : Assignment → Prop)
    (source : ∀ model, GeneralNominalState.Models state.source.state model → claim model) : Justified state focus claim :=
  ⟨[],(by intro _ impossible; cases impossible),fun model valid => source model valid.1⟩

theorem refresh_support_unchanged (state : Tracked roles) (context : GeneralNominalCandidates.Context)
    (support : List (Occurrence roles)) (claim : Assignment → Prop) :
    Entails {state with current := regenerate state.current context} support claim ↔ Entails state support claim := Iff.rfl

theorem all_models_slice (state : Tracked roles) (support : List (Occurrence roles))
    (model : Assignment) (valid : AllModels state model) : Slice state support model :=
  ⟨valid.1,fun fact member _ => valid.2 fact member⟩

theorem support_sound (state : Tracked roles) (support : List (Occurrence roles)) (claim : Assignment → Prop)
    (entailed : Entails state support claim) (model : Assignment) (valid : AllModels state model) : claim model :=
  entailed model (all_models_slice state support model valid)

theorem discharged_support (state : Tracked roles) (focus : Occurrence roles) (support : List (Occurrence roles))
    (done : ∀ producer ∈ support, Discharged state.current producer) (claim : Assignment → Prop)
    (entailed : Entails state support claim) : Justified state focus claim :=
  ⟨support,fun producer member => Or.inl (done producer member),entailed⟩

theorem unsupported_decision_defers (state : Tracked roles) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (role : declaration.role = root.demand.role)
    (bounds : List (GeneralNominalInspection.Bounds state.current.context.state))
    (located : GeneralNominalRecursiveCandidates.arguments state.current.context root = some bounds)
    (unsupported : ∀ support, Admissible state root support → ¬ Inspection state support declaration bounds) :
    ¬ ∃ support, DecisionGuard state registry root support := by
  rintro ⟨support,allowed,_,inspected⟩
  exact unsupported support allowed (inspected declaration visible role bounds located)

end Yulang.GeneralNominalSupport
