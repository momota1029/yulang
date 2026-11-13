import Yulang.GeneralNominalInvocationAncestry
import Yulang.GeneralNominalPacketCodes

/-! Allocation and ordinary propagation introduce only reserved keys or
already listed endpoint IDs. Observation changes cannot enlarge that pool. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralNominalAllocationSupport
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalAllocation GeneralNominalState
open GeneralNominalRecursiveInspection
variable {bindings : Bindings}

def Endpoints (bindings : Bindings) (pool : List Nat) : Prop :=
  ∀ binding ∈ bindings, binding.2.1 ∈ pool ∧ binding.2.2 ∈ pool

theorem slot_source (state : GeneralNominalState.State) (slot : Fin state.base.slots) :
    state.base.source slot ∈ sources state :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot,rfl⟩)))

theorem report_endpoints (state : GeneralNominalState.State) (report : Report state) :
    Endpoints (GeneralNominalRecursiveInspection.bindings state report) (sources state) := by
  intro entry member
  obtain ⟨capture,present,rfl⟩ := List.mem_map.mp member
  exact ⟨slot_source state capture.bounds.1,slot_source state capture.bounds.2⟩

theorem occurrences_endpoints (supported : Endpoints bindings pool) (name : Nat)
    (bounds : GeneralSourceState.Interval) (member : bounds ∈ occurrences bindings name) :
    bounds.1 ∈ pool ∧ bounds.2 ∈ pool := by
  obtain ⟨entry,filtered,rfl⟩ := List.mem_map.mp member
  exact supported entry (List.mem_filter.mp filtered).1

theorem lower_sources (bounds : List GeneralSourceState.Interval)
    (supported : ∀ pair ∈ bounds, pair.1 ∈ pool ∧ pair.2 ∈ pool) :
    typeSources (lower bounds) ⊆ pool := by
  induction bounds with
  | nil => intro _ impossible; cases impossible
  | cons head tail ih =>
    cases tail with
    | nil => intro source member; cases List.mem_singleton.mp member; exact (supported head (by simp)).1
    | cons next rest =>
      intro source member
      rcases List.mem_append.mp member with first | later
      · cases List.mem_singleton.mp first; exact (supported head (by simp)).1
      · exact ih (fun pair present => supported pair (List.mem_cons_of_mem _ present)) later

theorem upper_sources (bounds : List GeneralSourceState.Interval)
    (supported : ∀ pair ∈ bounds, pair.1 ∈ pool ∧ pair.2 ∈ pool) :
    typeSources (upper bounds) ⊆ pool := by
  induction bounds with
  | nil => intro _ impossible; cases impossible
  | cons head tail ih =>
    cases tail with
    | nil => intro source member; cases List.mem_singleton.mp member; exact (supported head (by simp)).2
    | cons next rest =>
      intro source member
      rcases List.mem_append.mp member with first | later
      · cases List.mem_singleton.mp first; exact (supported head (by simp)).2
      · exact ih (fun pair present => supported pair (List.mem_cons_of_mem _ present)) later

theorem equation_sources (target : Nat) (term : Core.PresenceGeneration.TyTerm Nat)
    (known : target ∈ pool) (leaves : typeSources term ⊆ pool) (atom : PresenceNormalForm.Atom Nat)
    (member : atom ∈ equations target term) : atomSources atom ⊆ pool := by
  rcases List.mem_cons.mp member with same | rest
  · cases same
    intro identity present
    rcases List.mem_append.mp present with one | two
    · cases List.mem_singleton.mp one; exact known
    · exact leaves two
  · cases List.mem_singleton.mp rest
    intro identity present
    rcases List.mem_append.mp present with one | two
    · exact leaves one
    · cases List.mem_singleton.mp two; exact known

theorem cross_sources (supported : Endpoints bindings pool) (atom : PresenceNormalForm.Atom Nat)
    (member : atom ∈ cross bindings) : atomSources atom ⊆ pool := by
  obtain ⟨first,one,rest⟩ := List.mem_flatMap.mp member
  obtain ⟨last,two,member⟩ := List.mem_flatMap.mp rest
  split at member
  · cases List.mem_singleton.mp member
    intro identity present
    rcases List.mem_append.mp present with left | right
    · cases List.mem_singleton.mp left; exact (supported first one).1
    · cases List.mem_singleton.mp right; exact (supported last two).2
  · cases member

theorem input_key (visible : declaration ∈ registry.declarations) (member : name ∈ declaration.inputNames)
    (side : purpose = 0 ∨ purpose = 1) : origin parent declaration.id purpose name 0 ∈ keys registry parent := by
  apply List.mem_flatMap.mpr
  refine ⟨declaration,visible,List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨name,member,?_⟩))⟩
  rcases side with rfl | rfl <;> simp

theorem output_key (visible : declaration ∈ registry.declarations) (member : name ∈ declaration.outputNames) :
    origin parent declaration.id 2 name 0 ∈ keys registry parent :=
  List.mem_flatMap.mpr ⟨declaration,visible,List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.mpr ⟨name,member,rfl⟩))⟩

theorem clause_output_key (visible : declaration ∈ registry.declarations)
    (member : clause ∈ declaration.requirements) (output : equation ∈ clause.outputs) :
    origin parent declaration.id 5 equation.id 0 ∈ keys registry parent :=
  List.mem_flatMap.mpr ⟨declaration,visible,List.mem_append_right _
    (List.mem_flatMap.mpr ⟨clause,member,List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_map.mpr ⟨equation,output,rfl⟩))⟩)⟩

theorem reservation (state : GeneralNominalState.State) (key : GeneralNominalAllocation.Origin) (member : key ∈ keys registry parent) :
    source state registry parent key ∈ reserved state registry parent := List.mem_map.mpr ⟨key,member,rfl⟩

theorem merges_sources (state : GeneralNominalState.State) (visible : declaration ∈ registry.declarations)
    (supported : Endpoints bindings pool) (reservations : reserved state registry parent ⊆ pool)
    (atom : PresenceNormalForm.Atom Nat) (member : atom ∈ merges state registry parent declaration bindings) :
    atomSources atom ⊆ pool := by
  obtain ⟨name,declared,member⟩ := List.mem_flatMap.mp member
  split at member
  · cases member
  · have lo : ((capture state registry parent declaration.id bindings).inputs name).1 ∈ pool := by
      simp only [capture]
      exact reservations (reservation state _ (input_key visible declared (Or.inl rfl)))
    have hi : ((capture state registry parent declaration.id bindings).inputs name).2 ∈ pool := by
      simp only [capture]
      exact reservations (reservation state _ (input_key visible declared (Or.inr rfl)))
    rcases List.mem_append.mp member with left | right
    · exact equation_sources _ _ lo (lower_sources _ (occurrences_endpoints supported name)) atom left
    · exact equation_sources _ _ hi (upper_sources _ (occurrences_endpoints supported name)) atom right

theorem checks_sources (state : GeneralNominalState.State) (report : Report state)
    (supported : sources state ⊆ pool) (atom : PresenceNormalForm.Atom Nat)
    (member : atom ∈ selfChecks state report) : atomSources atom ⊆ pool := by
  obtain ⟨bounds,present,rfl⟩ := List.mem_map.mp member
  intro identity present
  rcases List.mem_append.mp present with first | last
  · cases List.mem_singleton.mp first; exact supported (slot_source state bounds.1)
  · cases List.mem_singleton.mp last; exact supported (slot_source state bounds.2)

theorem extend_sources (state : GeneralNominalState.State) (newSources : List Nat)
    (atoms : List (PresenceNormalForm.Atom Nat)) (old : sources state ⊆ pool)
    (reserved : newSources ⊆ pool) (generated : ∀ atom ∈ atoms, atomSources atom ⊆ pool) :
    sources (GeneralNominalState.extend state newSources atoms) ⊆ pool := by
  intro identity member
  have split : identity ∈ sources state ∨ identity ∈ newSources ∨ identity ∈ atoms.flatMap atomSources := by
    simpa only [sources,GeneralNominalState.extend,List.flatMap_append,List.mem_append,or_assoc,
      or_left_comm,or_comm] using member
  rcases split with before | added | equation
  · exact old before
  · exact reserved added
  · obtain ⟨atom,present,member⟩ := List.mem_flatMap.mp equation
    exact generated atom present member

theorem private_sources (packet : Packet roles) (visible : packet.declaration ∈ packet.registry.declarations)
    (old : sources packet.context.state ⊆ pool)
    (reservations : reserved packet.context.state packet.registry packet.site.occurrence.identity ⊆ pool) :
    sources packet.privateContext.state ⊆ pool := by
  refine extend_sources _ [] _ ?_ (by intro _ impossible; cases impossible) ?_
  · apply extend_sources packet.context.state _ _ old reservations
    intro atom member
    have endpoints : Endpoints packet.bindings pool := by
      intro entry member
      have prior := report_endpoints packet.context.state (GeneralNominalPacketSupport.report packet) entry member
      exact ⟨old prior.1,old prior.2⟩
    rcases List.mem_append.mp member with cross | merged
    · exact cross_sources endpoints atom cross
    · exact merges_sources packet.context.state visible endpoints reservations atom merged
  · exact checks_sources packet.context.state (GeneralNominalPacketSupport.report packet) old

theorem child_output_reserved (packet : Packet roles) (visible : packet.declaration ∈ packet.registry.declarations)
    (child : Occurrence roles) (member : child ∈ packet.children)
    (output : GeneralSourceState.Output) (requested : output ∈ child.demand.outputs) :
    output.target ∈ reserved packet.context.state packet.registry packet.site.occurrence.identity := by
  unfold Packet.children GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children at member
  obtain ⟨emission,present,rfl⟩ := List.mem_map.mp member
  have old := (GeneralCanonicalChildOrder.canonicalEmit_perm packet.site.occurrence.identity
    packet.declaration packet.checked _ _).mem_iff.mpr present
  unfold GeneralDeclarationDemands.emitAll at old
  obtain ⟨clause,_,same⟩ := List.mem_map.mp old
  cases same
  obtain ⟨equation,present,same⟩ := List.mem_map.mp requested
  cases same
  unfold GeneralDeclarationDemands.outputTarget
  split
  · split
    · rename_i name equationAt declared
      exact reservation _ _ (output_key visible declared)
    · exact reservation _ _ (clause_output_key visible clause.property present)
  · exact reservation _ _ (clause_output_key visible clause.property present)

end Yulang.GeneralNominalAllocationSupport
