import Yulang.GeneralDictionary171InputDiscovery
import Yulang.GeneralDictionary171CheckedSpine

/-! Discover arbitrary-depth unary nominal input spines from actual inspection.
The point-descriptor restriction is sufficient and explicit, not a language rule.
No stored Spine, Tree, semantic Evidence, or successful selection is assumed. -/
namespace Yulang.GeneralDictionary172CoverageInput
open GeneralNominalInspection (Query)
open GeneralNominalRecursiveInspection GeneralNominalSpineFacts
open GeneralDictionary171LocalInspectionObservation (PointInspection)

/-- Syntactic fragment: unary nominal wrappers ending in a variable-argument
nominal leaf. Repeated names are permitted here; later projection uses injectivity. -/
inductive Syntax (names : Fin n → Nat) : Query → Prop
  | leaf (name : Nat) : Syntax names (.nominal name (List.ofFn fun i => .variables [names i]))
  | wrap (name : Nat) (inner : Syntax names query) : Syntax names (.nominal name [query])

private theorem finished_append (first last : Report state) :
    Finished (first.append last) ↔ Finished first ∧ Finished last := by
  simp only [Finished,Report.append,List.append_eq_nil_iff]
  constructor
  · rintro ⟨⟨a,b⟩,⟨c,d⟩,e,f⟩; exact ⟨⟨a,c,e⟩,b,d,f⟩
  · rintro ⟨⟨a,c,e⟩,b,d,f⟩; exact ⟨⟨a,b⟩,⟨c,d⟩,e,f⟩

private theorem many_length (state : GeneralNominalState.State)
    (queries : List Query) (bounds : List (GeneralNominalInspection.Bounds state))
    (origins : Nat → Option Origin) (index : Nat)
    (finished : Finished (inspectMany state queries bounds origins index)) : queries.length = bounds.length := by
  induction queries generalizing bounds index with
  | nil => cases bounds with
    | nil => rfl
    | cons b bs => simp [inspectMany,Finished] at finished
  | cons q qs ih => cases bounds with
    | nil => simp [inspectMany,Finished] at finished
    | cons b bs =>
      rw [inspectMany] at finished
      simpa using ih bs (index+1) ((finished_append _ _).mp finished).2

/-- Every finite unary syntax depth is recovered from the actual successful
inspection. Point descriptors restrict representation, not semantic typing. -/
theorem inspected_spine (state : GeneralNominalState.State)
    (names : Fin n → Nat)
    (form : Syntax names query) (slot : Fin state.base.slots) (origin : Option Origin)
    (finished : Finished (inspect state query (slot,slot) origin))
    (points : PointInspection state (inspect state query (slot,slot) origin)) :
    ∃ bounds : Fin n → GeneralNominalInspection.Bounds state,
      ∃ spine : Spine state names bounds slot, spine.query = query := by
  induction form generalizing slot origin with
  | leaf name => exact GeneralDictionary171InputDiscovery.inspected_leaf state name names slot origin finished
  | @wrap query name inner ih =>
    simp only [inspect] at finished
    split at finished
    · split at finished <;> simp [Finished,block,Report.visit] at finished
    · rename_i descriptor recorded
      split at finished
      · rename_i sameName
        have rootMember : (slot,slot) ∈ (inspect state (.nominal name [query]) (slot,slot) origin).inspected := by
          simp [inspect,recorded,sameName,Report.visit]
        obtain ⟨k,slots,parameters⟩ := points (slot,slot) rootMember descriptor recorded
        have arguments := GeneralNominalLinearCaptureFacts.typeArguments_exact (fun i => (slots i,slots i))
        rw [parameters,arguments] at finished
        simp only [↓reduceIte] at finished
        have len := many_length state [query] (List.ofFn fun i => (slots i,slots i)) _ _ finished
        have one : k = 1 := by simpa using len.symm
        subst k
        let child := slots 0
        have params : descriptor.arguments = [.type (child,child)] := by
          simpa [List.ofFn_succ,child] using parameters
        have sub : Finished (inspect state query (child,child)
            (some (.nominal (origin.getD (.source (state.base.source slot))) name 0))) := by
          simpa [List.ofFn_succ,inspectMany,Report.visit,Report.append,Finished,child] using finished
        have subpoints : PointInspection state (inspect state query (child,child)
            (some (.nominal (origin.getD (.source (state.base.source slot))) name 0))) := by
          intro pair member desc found
          apply points pair _ desc found
          have full := GeneralNominalSpineFacts.inspect_wrap state slot child descriptor recorded params query origin
          rw [sameName] at full
          rw [full]
          exact List.mem_cons_of_mem _ member
        obtain ⟨bounds,spine,equal⟩ := ih child _ sub subpoints
        exact ⟨bounds,.wrap slot child descriptor recorded params spine,by simp [Spine.query,equal,sameName]⟩
      · simp [Finished,Report.visit] at finished
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalRecursiveCandidates

/-- Recover the complete input certificate for a terminal declaration from
its syntactic finite spine and actual report, at arbitrary wrapper depth. -/
theorem input_exists (context : Context) (root : Occurrence roles) (declaration : Declaration)
    (terminal : declaration.requirements = []) (role : declaration.role = root.demand.role)
    (slot : Fin context.state.base.slots) (names : Fin n → Nat)
    (distinct : Function.Injective names) (inputs : declaration.inputNames = List.ofFn names)
    (form : Syntax names query)
    (queries : GeneralNominalInspection.queries context.state context.interpretation declaration = [query])
    (located : arguments context root = some [(slot,slot)])
    (defined : GeneralNominalMaterialization.RootDefined declaration root)
    (finished : Finished (report context declaration [(slot,slot)]))
    (points : PointInspection context.state (report context declaration [(slot,slot)])) :
    ∃ input : GeneralDictionary171SpineDiscovery.Input context root declaration, input.slot = slot := by
  have inspected : Finished (inspect context.state query (slot,slot) none) := by
    simpa only [Finished,report,queries,inspectMany,Report.append,List.append_nil] using finished
  have inspectedPoints : PointInspection context.state (inspect context.state query (slot,slot) none) := by
    simpa only [PointInspection,report,queries,inspectMany,Report.append,List.append_nil] using points
  obtain ⟨bounds,spine,same⟩ := inspected_spine context.state names form slot none inspected inspectedPoints
  exact ⟨⟨terminal,role,slot,n,names,distinct,inputs,bounds,spine,by rw [same]; exact queries,located,defined⟩,rfl⟩

/-- A finite nested input is discovered rather than supplied. Successful
request checking then yields one terminal payload uniformly in all models.
This is a sufficient fragment: checker false is not language rejection. -/
theorem checked_uniform_evidence (registry : Registry) (context : Context)
    (root : Occurrence roles) (declaration : Declaration)
    (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (terminal : declaration.requirements = []) (role : declaration.role = root.demand.role)
    (slot : Fin context.state.base.slots) (names : Fin n → Nat)
    (distinct : Function.Injective names) (inputs : declaration.inputNames = List.ofFn names)
    (form : Syntax names query)
    (queries : GeneralNominalInspection.queries context.state context.interpretation declaration = [query])
    (located : arguments context root = some [(slot,slot)])
    (defined : GeneralNominalMaterialization.RootDefined declaration root)
    (finished : Finished (report context declaration [(slot,slot)]))
    (points : PointInspection context.state (report context declaration [(slot,slot)]))
    (success : GeneralDictionary171RequestChecker.checkRequests context.state context.interpretation
      (GeneralNominalMaterialization.requests context.state registry root declaration checked
        (bindings context.state (report context declaration [(slot,slot)]))) = true)
    (metadata : Metadata registry context) :
    ∀ model, GeneralNominalState.Models context.state model →
      GeneralDictionaryRecursiveEvidence.Evidence registry context model root (.node declaration.id []) := by
  obtain ⟨input,same⟩ := input_exists context root declaration terminal role slot names
    distinct inputs form queries located defined finished points
  apply GeneralDictionary171CheckedSpine.uniform_evidence registry context root declaration visible checked input
  · simpa only [GeneralDictionary171CheckedSpine.check,GeneralDictionary171CheckedSpine.requests,same] using success
  · exact metadata
end Yulang.GeneralDictionary172CoverageInput
