import Yulang.GeneralDictionaryNominalPair178
import Yulang.GeneralDictionaryCenteredGuard177
import Yulang.GeneralDictionaryReachableRootIntervals

/-! Arbitrary finite nominal parameter lists need only source endpoint head
support. Variable patterns do not inspect their interior bounds. -/
namespace Yulang.GeneralDictionaryNominalPairSourceSupport178
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSupport
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralDictionaryNominalPair178

 theorem variables_read_none (state : GeneralNominalState.State) {n : Nat}
    (names : Fin n → Nat) (bounds : Fin n → GeneralNominalInspection.Bounds state) :
    readsMany state (List.ofFn fun i => .variables [names i]) (List.ofFn bounds) = [] := by
  induction n with
  | zero => simp [readsMany]
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ]
    simp only [readsMany,reads,List.nil_append]
    exact ih (fun i => names i.succ) (fun i => bounds i.succ)

 theorem reads_exact (context : Context) (declaration : Declaration) (shape : Shape context declaration) :
    readsMany context.state (GeneralNominalInspection.queries context.state context.interpretation declaration)
      [(shape.lower,shape.upper)] = [shape.lower,shape.upper] := by
  rw [shape.query]
  simp only [readsMany,reads,shape.recorded,shape.recordedRight,shape.parameters,shape.parametersRight,
    GeneralNominalLinearCaptureFacts.typeArguments_exact,shape.different,shape.same,↓reduceIte]
  rw [variables_read_none,variables_read_none]
  simp

 theorem located_arguments (context : Context) (root : Occurrence roles)
    (lower upper : Fin context.state.base.slots)
    (located : arguments context root = some [(lower,upper)]) :
    ∀ index, root.demand.arguments index =
      (context.state.base.source lower,context.state.base.source upper) := by
  have recovered := GeneralDictionaryReachableRootIntervals.locate_sources context.state.base
    (List.ofFn root.demand.arguments) [(lower,upper)] located
  intro index
  have member : root.demand.arguments index ∈ List.ofFn root.demand.arguments := List.mem_ofFn.mpr ⟨index,rfl⟩
  rw [←recovered] at member
  exact List.mem_singleton.mp member

 theorem nominal_source_ready (context : Context) (root : Occurrence roles)
    (slot : Fin context.state.base.slots) (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals slot = some descriptor) :
    ReadyAt (initial context root) [] (context.state.base.source slot) :=
  source_ready (initial context root) _ _ _ _
    (Head.nominal (snapshot := context.state) slot descriptor recorded)
    (Head.nominal (snapshot := context.state) slot descriptor recorded) []

 theorem inspection (context : Context) (root : Occurrence roles) (declaration : Declaration)
    (shape : Shape context declaration) :
    Inspection (initial context root) [] declaration [(shape.lower,shape.upper)] := by
  intro slot member
  change slot ∈ readsMany context.state
    (GeneralNominalInspection.queries context.state context.interpretation declaration) [(shape.lower,shape.upper)] at member
  rw [reads_exact context declaration shape] at member
  rcases List.mem_cons.mp member with same | member
  · subst slot
    exact nominal_source_ready context root shape.lower shape.left shape.recorded
  · have same := List.mem_singleton.mp member
    subst slot
    exact nominal_source_ready context root shape.upper shape.right shape.recordedRight

 theorem guard (context : Context) (root : Occurrence roles) (declaration : Declaration)
    (shape : Shape context declaration)
    (located : arguments context root = some [(shape.lower,shape.upper)]) :
    Guard (initial context root) root declaration [(shape.lower,shape.upper)] [] := by
  refine ⟨?_,?_,inspection context root declaration shape⟩
  · intro _ member; cases member
  · intro index
    rw [located_arguments context root shape.lower shape.upper located index]
    exact nominal_source_ready context root shape.lower shape.left shape.recorded

 theorem decisions (context : Context) (root : Occurrence roles) (declaration : Declaration)
    (shape : Shape context declaration) (registry : Registry)
    (singleton : registry.declarations = [declaration])
    (located : arguments context root = some [(shape.lower,shape.upper)]) :
    DecisionGuard (initial context root) registry root [] := by
  refine ⟨?_,(guard context root declaration shape located).2.1,?_⟩
  · intro _ member; cases member
  · intro other member role intervals found
    rw [singleton] at member
    cases List.mem_singleton.mp member
    have same := Option.some.inj (located.symm.trans found)
    subst intervals
    exact inspection context root declaration shape

 theorem value_guard (context : Context) (root : Occurrence roles) (declaration : Declaration)
    (shape : Shape context declaration) (registry : Registry)
    (singleton : registry.declarations = [declaration])
    (checked : DeclarationChecked registry.constructors roles declaration)
    (site : GeneralNominalDemandMerging.Site roles) (same : site.occurrence = root)
    (located : arguments context root = some [(shape.lower,shape.upper)]) :
    GeneralNominalValueSupport.PacketGuard (initial context root)
      (⟨registry,context,site,declaration,checked,[(shape.lower,shape.upper)]⟩ : GeneralNominalSaturationState.Packet roles) [] := by
  apply GeneralNominalValueSupport.source_packet
  subst root
  exact ⟨guard context site.occurrence declaration shape located,
    decisions context site.occurrence declaration shape registry singleton located⟩
end Yulang.GeneralDictionaryNominalPairSourceSupport178
