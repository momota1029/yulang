import YulangClosure.OriginalSourceEnvironment

/-!
R186 v3: an INCOMPLETE construction artifact for the unchanged inference root.

The independently solved, all-constructor generation relation is not defined
here. Both permitted direct checks were consumed (missing unused import, then
elaboration diagnostics). Failed declarations were removed; this final module
has not been rechecked. These declarations expose the raw App candidate data
and its first raw
admission goal. They do not assume or establish Build satisfaction, source
typing, a concrete descriptor interpretation, or InferenceSoundness.

Source owners: selected Generalize construction sections 3.1--3.3 and 4;
contextual Function membership sections 2--3. No port projection replaces the
joint generated clauses. Every candidate below keeps eta and the joint witness
from the given decoded assignment; descriptor/interface arguments are data,
not independently admitted replacement witnesses.
-/
namespace YulangClosure.ConcreteGenerationSoundnessR186V2

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment

/-- Raw candidate assembly. No admission or source judgment is a field. The
whole descriptor and whole output interface must be constructed by the still
missing independent interpretation; no scalar port factorization is presumed. -/
def appLogical (state : Decoded s View) (site : Site)
    (descriptor : s.Descriptor) (output : s.Interface) : Logical s View :=
  { descriptors := [(⟨site, .descriptor⟩, descriptor)]
    interfaces := [(⟨site, .callableImage⟩, output)]
    viewMeaning := state.viewMeaning
    eta := state.assignment.event.eta
    witness := state.assignment.event.witness }

def appCandidate (environment : Environment (Payload s View))
    (state : Decoded s View) (site occurrence : Nat)
    (descriptor : s.Descriptor) (output : s.Interface) : ScopedValue (Payload s View) :=
  scopeCandidate environment occurrence (.logical .viewLogic
    (appLogical state site descriptor output))

theorem app_candidate_readout (readout : RuntimeReadout s View)
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) (site occurrence : Nat)
    (descriptor : s.Descriptor) (output : s.Interface) :
    decode readout (environment.extend ⟨site, .viewLogic, 0⟩
      (appCandidate environment state site occurrence descriptor output)) =
      some (state.logical (appLogical state site descriptor output)) := by
  exact decode_extend readout environment ⟨site, .viewLogic, 0⟩
    (appCandidate environment state site occurrence descriptor output) state decoded

theorem app_candidate_descriptor (state : Decoded s View) (site : Site)
    (descriptor : s.Descriptor) (output : s.Interface) :
    (state.logical (appLogical state site descriptor output)).assignment.descriptor
      ⟨site, .descriptor⟩ = descriptor := by
  simp [Decoded.logical, appLogical, put]

theorem app_candidate_output (state : Decoded s View) (site : Site)
    (descriptor : s.Descriptor) (output : s.Interface) :
    (state.logical (appLogical state site descriptor output)).interfaces
      ⟨site, .callableImage⟩ = output := by
  simp [Decoded.logical, appLogical, put]

/-- Explicit same-assignment/same-witness preservation for this one logical
frame. It is not the all-binder induction invariant required by the parent. -/
theorem app_candidate_keeps_shared_data (state : Decoded s View) (site : Site)
    (descriptor : s.Descriptor) (output : s.Interface) :
    let next := state.logical (appLogical state site descriptor output)
    next.assignment.event = state.assignment.event ∧
    next.assignment.value = state.assignment.value ∧
    next.assignment.root = state.assignment.root ∧
    next.assignment.binding = state.assignment.binding ∧
    next.active = state.active ∧ next.callOwners = state.callOwners := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/- The first open application equation is source admission of this exact
candidate. No theorem asserting that admission or an independent solver's
implication to it is delivered. See the leased handoff for the exact sequent,
source clauses, failed checks and the unchanged full-parent ledger. -/

end YulangClosure.ConcreteGenerationSoundnessR186V2

#check @YulangClosure.ConcreteGenerationSoundnessR186V2.app_candidate_readout
#print axioms YulangClosure.ConcreteGenerationSoundnessR186V2.app_candidate_readout
#check @YulangClosure.ConcreteGenerationSoundnessR186V2.app_candidate_descriptor
#print axioms YulangClosure.ConcreteGenerationSoundnessR186V2.app_candidate_descriptor
#check @YulangClosure.ConcreteGenerationSoundnessR186V2.app_candidate_output
#print axioms YulangClosure.ConcreteGenerationSoundnessR186V2.app_candidate_output
#check @YulangClosure.ConcreteGenerationSoundnessR186V2.app_candidate_keeps_shared_data
#print axioms YulangClosure.ConcreteGenerationSoundnessR186V2.app_candidate_keeps_shared_data
