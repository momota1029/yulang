import Yulang.GeneralNominalSharedEmission

/-! Only coherently substituted, settled output packets justify new heads.
The readback ledger contains finite terms derived from actual schema recipes;
output-only binders refer to earlier readbacks, not new atomic leaves. -/
namespace Yulang.GeneralNominalSharedSupport
open GeneralNominalSaturationState GeneralNominalSupport GeneralSourceDictionaries
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalOriginTerms GeneralNominalSharedCaptures
open GeneralNominalCommonBridge (Assignment)

abbrev Readbacks := List (Nat × Expr Origin)
abbrev Models := @GeneralNominalSettledSupport.Models

def Delta (packet : Packet roles) (model : Assignment) : Prop :=
  GeneralNominalPacketSupport.Inputs packet model ∧ GeneralNominalPacketSupport.Outputs packet model

def Recipes (packet : Packet roles) : Prop :=
  ∀ output ∈ packet.site.occurrence.demand.outputs, ∃ term,
    Recipe (GeneralNominalPacketSupport.namedSchema packet) (.source output.target) term

structure OutputCertificate (state : Tracked roles) (facts : List (Fact roles))
    (readbacks : Readbacks) (packet : Packet roles) where
  substitution : Nat → Expr Origin
  recipes : Recipes packet
  inputs : ∀ entry ∈ (GeneralNominalPacketSupport.namedSchema packet).variables,
    entry.mode = .actual → entry.name ∉ packet.declaration.outputNames →
      ∃ origin, substitution entry.name = .leaf origin ∧
        Captured packet (fun model => Models state facts model ∧ Delta packet model) entry.name origin
  binders : ∀ entry ∈ (GeneralNominalPacketSupport.namedSchema packet).variables,
    entry.mode = .actual → entry.name ∈ packet.declaration.outputNames →
      ((GeneralNominalPacketSupport.capture packet).outputs entry.name, substitution entry.name) ∈ readbacks
  uses : ∀ model, Models state facts model → Delta packet model →
    ∀ entry ∈ (GeneralNominalPacketSupport.namedSchema packet).variables, entry.mode = .actual →
      Holds model (substitution entry.name) entry.origin

theorem certificate_coherent (certificate : OutputCertificate state facts readbacks packet)
    (model : Assignment) (source : Models state facts model) (delta : Delta packet model) :
    Coherent model (GeneralNominalPacketSupport.namedSchema packet) certificate.substitution :=
  coherent_of_uses delta.2 (certificate.uses model source delta)

/-- Input facts are checked before this packet's output is available. A
full-branch certificate would erase a dependency on an unfinished output. -/
def InputExplanation (state : Tracked roles) (facts : List (Fact roles)) (packet : Packet roles) : Prop :=
  ∀ entry ∈ (GeneralNominalPacketSupport.inputSchema packet).variables, entry.mode = .actual →
    ∃ origin,
      Captured packet (fun model => Models state facts model ∧ GeneralNominalPacketSupport.Inputs packet model)
        entry.name origin ∧
      ∀ model, Models state facts model → GeneralNominalPacketSupport.Inputs packet model →
        Same model entry.origin origin

theorem empty_input_explanation (empty : (GeneralNominalPacketSupport.inputSchema packet).variables = []) :
    InputExplanation state facts packet := by
  intro entry member
  rw [empty] at member
  cases member

inductive Trusted (state : Tracked roles) : List (Fact roles) → Readbacks → Prop
  | source : Trusted state [] []
  | input (packet : Packet roles) (support : List (Occurrence roles)) :
      Trusted state facts readbacks → Fact.inputs packet support ∈ state.facts →
      GeneralNominalSettledSupport.Readback state facts packet → InputExplanation state facts packet →
      Trusted state (Fact.inputs packet support :: facts) readbacks
  | output (packet : Packet roles) (support : List (Occurrence roles))
      (certificate : OutputCertificate state facts readbacks packet) (target : Nat) (term : Expr Nat) :
      Trusted state facts readbacks → Fact.outputs packet support ∈ state.facts →
      Fact.inputs packet support ∈ facts → GeneralNominalSettledSupport.PacketSettled state.current packet →
      Recipe (GeneralNominalPacketSupport.namedSchema packet) (.source target) term →
      Trusted state (Fact.outputs packet support :: facts)
        ((target,term.bind certificate.substitution) :: readbacks)
  | merge (first last : GeneralNominalDemandMerging.Site roles) (support : List (Occurrence roles)) :
      Trusted state facts readbacks → Fact.merge first last support ∈ state.facts →
      GeneralNominalSettledSupport.MergeEvidence (Models state facts) first last →
      Trusted state (Fact.merge first last support :: facts) readbacks

theorem trusted_old (trusted : Trusted state facts readbacks) : GeneralNominalSettledSupport.Trusted state facts := by
  induction trusted with
  | source => exact .source
  | input packet support _ member readback coherence ih => exact .input packet support ih member readback
  | output packet support certificate target term _ member included done recipe ih =>
      exact .output packet support ih member included done
  | merge first last support _ member evidence ih => exact .merge first last support ih member evidence

private theorem tail_models (model : Assignment) (valid : Models state (fact :: facts) model) :
    Models state facts model := ⟨valid.1,fun entry member => valid.2 entry (List.mem_cons_of_mem _ member)⟩

theorem settled_readback (trusted : Trusted state facts readbacks)
    (member : (target,term) ∈ readbacks) (model : Assignment) (valid : Models state facts model) :
    Holds model term (.source target) := by
  induction trusted with
  | source => cases member
  | input packet support previous present readback coherence ih => exact ih member (tail_models model valid)
  | merge first last support previous present evidence ih => exact ih member (tail_models model valid)
  | output packet support certificate target' term' previous present included done recipe ih =>
      rcases List.mem_cons.mp member with equal | member
      · cases equal
        have input := (tail_models model valid).2 _ included
        have output := valid.2 _ (List.mem_cons_self ..)
        exact recipe_readback recipe (certificate_coherent certificate model (tail_models model valid) ⟨input,output⟩)
      · exact ih member (tail_models model valid)

/-- Every requested output of a promoted packet has a uniform finite term.
The substitution leaves remain input-origin/earlier-readback leaves. -/
theorem promoted_outputs (trusted : Trusted state facts readbacks)
    (present : Fact.outputs packet support ∈ facts)
    (output : GeneralSourceState.Output) (outputMem : output ∈ packet.site.occurrence.demand.outputs) :
    ∃ term : Expr Origin, ∀ model, Models state facts model → Holds model term (.source output.target) := by
  induction trusted with
  | source => cases present
  | input added dependencies previous member readback coherence ih =>
      rcases List.mem_cons.mp present with impossible | present
      · cases impossible
      · obtain ⟨term,valid⟩ := ih present
        exact ⟨term,fun model models => valid model (tail_models model models)⟩
  | merge first last dependencies previous member evidence ih =>
      rcases List.mem_cons.mp present with impossible | present
      · cases impossible
      · obtain ⟨term,valid⟩ := ih present
        exact ⟨term,fun model models => valid model (tail_models model models)⟩
  | output added dependencies certificate target expression previous member included done recipe ih =>
      rcases List.mem_cons.mp present with equal | present
      · cases equal
        obtain ⟨term,recipe⟩ := certificate.recipes output outputMem
        refine ⟨term.bind certificate.substitution,?_⟩
        intro model models
        have old := tail_models model models
        exact recipe_readback recipe (certificate_coherent certificate model old
          ⟨old.2 _ included,models.2 _ (List.mem_cons_self ..)⟩)
      · obtain ⟨term,valid⟩ := ih present
        exact ⟨term,fun model models => valid model (tail_models model models)⟩

def inputOrigins (facts : List (Fact roles)) : List Origin :=
  facts.flatMap fun fact => match fact with
    | .outputs packet _ => (inheritedReport packet).captures.filterMap (fun captured => captured.origin)
    | _ => []

private theorem origins_tail (member : origin ∈ inputOrigins facts) :
    origin ∈ inputOrigins (fact :: facts) := by
  simp only [inputOrigins,List.flatMap_cons,List.mem_append] at *
  exact Or.inr member

private theorem certificate_leaves (certificate : OutputCertificate state facts readbacks packet)
    (recipe : Recipe (GeneralNominalPacketSupport.namedSchema packet) root term)
    (prior : ∀ target expression, (target,expression) ∈ readbacks →
      ∀ origin ∈ expression.leaves, origin ∈ inputOrigins facts) :
    ∀ origin ∈ (term.bind certificate.substitution).leaves,
      origin ∈ inputOrigins (Fact.outputs packet support :: facts) := by
  intro origin member
  obtain ⟨name,used,member⟩ := (leaves_bind term certificate.substitution origin).mp member
  obtain ⟨whereUsed,entry⟩ := recipe_leaf_use recipe used
  by_cases output : name ∈ packet.declaration.outputNames
  · exact origins_tail (prior _ _ (certificate.binders _ entry rfl output) origin member)
  · obtain ⟨recorded,equal,captured⟩ := certificate.inputs _ entry rfl output
    rw [equal] at member
    have same : origin = recorded := by simpa [Expr.leaves] using member
    subst origin
    obtain ⟨capture,present,_,recorded⟩ := captured.1
    simp only [inputOrigins,List.flatMap_cons,List.mem_append]
    exact Or.inl (List.mem_filterMap.mpr ⟨capture,present,recorded⟩)

/-- The finite trusted history supplies a finite leaf basis. This basis grows
with the history; it is not yet a bound fixed by the initial source. -/
theorem settled_readback_leaves (trusted : Trusted state facts readbacks) :
    ∀ target expression, (target,expression) ∈ readbacks →
      ∀ origin ∈ expression.leaves, origin ∈ inputOrigins facts := by
  induction trusted with
  | source => intro target expression member; cases member
  | input packet support previous member readback coherence ih =>
      intro target expression member origin leaf
      exact origins_tail (ih target expression member origin leaf)
  | merge first last support previous member evidence ih =>
      intro target expression member origin leaf
      exact origins_tail (ih target expression member origin leaf)
  | output packet support certificate target term previous member included done recipe ih =>
      intro target' expression present origin leaf
      rcases List.mem_cons.mp present with equal | present
      · cases equal
        exact certificate_leaves certificate recipe ih origin leaf
      · exact origins_tail (ih target' expression present origin leaf)

theorem promoted_output_readback (trusted : Trusted state facts readbacks)
    (present : Fact.outputs packet support ∈ facts)
    (output : GeneralSourceState.Output) (outputMem : output ∈ packet.site.occurrence.demand.outputs) :
    ∃ term : Expr Origin,
      (∀ model, Models state facts model → Holds model term (.source output.target)) ∧
      ∀ origin ∈ term.leaves, origin ∈ inputOrigins facts := by
  induction trusted with
  | source => cases present
  | input added dependencies previous member readback coherence ih =>
      rcases List.mem_cons.mp present with impossible | present
      · cases impossible
      · obtain ⟨term,valid,leaves⟩ := ih present
        exact ⟨term,fun model models => valid model (tail_models model models),
          fun origin member => origins_tail (leaves origin member)⟩
  | merge first last dependencies previous member evidence ih =>
      rcases List.mem_cons.mp present with impossible | present
      · cases impossible
      · obtain ⟨term,valid,leaves⟩ := ih present
        exact ⟨term,fun model models => valid model (tail_models model models),
          fun origin member => origins_tail (leaves origin member)⟩
  | output added dependencies certificate target expression previous member included done recipe ih =>
      rcases List.mem_cons.mp present with equal | present
      · cases equal
        obtain ⟨term,recipe⟩ := certificate.recipes output outputMem
        refine ⟨term.bind certificate.substitution,?_,
          certificate_leaves certificate recipe (settled_readback_leaves previous)⟩
        intro model models
        have old := tail_models model models
        exact recipe_readback recipe (certificate_coherent certificate model old
          ⟨old.2 _ included,models.2 _ (List.mem_cons_self ..)⟩)
      · obtain ⟨term,valid,leaves⟩ := ih present
        exact ⟨term,fun model models => valid model (tail_models model models),
          fun origin member => origins_tail (leaves origin member)⟩

def HeadJustified (state : Tracked roles) (identity : Nat) (test : Test) : Prop :=
  ∃ facts readbacks, Trusted state facts readbacks ∧ ∃ snapshot observation,
    GeneralNominalSupport.Head snapshot identity test observation ∧
      ∀ model, Models state facts model → observation.Holds model

def ReadyAt (state : Tracked roles) (identity : Nat) : Prop :=
  ∃ test observation, GeneralNominalSupport.Head state.current.context.state identity test observation ∧
    HeadJustified state identity test

def DecisionGuard (registry : GeneralDeclarations.Registry) (state : Tracked roles) (root : Occurrence roles) : Prop :=
  (∀ index, ReadyAt state (root.demand.arguments index).1) ∧
    ∀ declaration ∈ registry.declarations, declaration.role = root.demand.role →
      ∀ bounds, GeneralNominalRecursiveCandidates.arguments state.current.context root = some bounds →
        ∀ slot ∈ readsMany state.current.context.state
          (GeneralNominalInspection.queries state.current.context.state state.current.context.interpretation declaration) bounds,
          ReadyAt state (state.current.context.state.base.source slot)

theorem head_old (known : HeadJustified state identity test) :
    GeneralNominalSettledSupport.HeadJustified state identity test := by
  obtain ⟨facts,readbacks,trusted,snapshot,observation,head,holds⟩ := known
  exact ⟨facts,trusted_old trusted,snapshot,observation,head,holds⟩

theorem decision_old (guard : DecisionGuard registry state root) :
    GeneralNominalSettledSupport.DecisionGuard registry state root := by
  have ready (identity) (known : ReadyAt state identity) : GeneralNominalSettledSupport.ReadyAt state identity := by
    obtain ⟨test,observation,head,known⟩ := known
    exact ⟨test,observation,head,head_old known⟩
  exact ⟨fun index => ready _ (guard.1 index),
    fun declaration member role bounds located slot read => ready _ (guard.2 declaration member role bounds located slot read)⟩

theorem source_head (state : Tracked roles)
    (head : GeneralNominalSupport.Head state.source.state identity test observation) : HeadJustified state identity test :=
  ⟨[],[],.source,state.source.state,observation,head,fun model valid =>
    GeneralCanonicalObservations.recorded_sound _ model valid.1 (head_recorded head)⟩

end Yulang.GeneralNominalSharedSupport
