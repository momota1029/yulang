import Yulang.GeneralDictionary171SpineDiscovery

/-! Recover the finite nominal input leaf from successful real inspection.
The nominal query syntax and distinct input names remain explicit, but no
stored descriptor, parameter bounds or Spine certificate is supplied. -/
namespace Yulang.GeneralDictionary171InputDiscovery
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query)
open GeneralNominalSpineFacts

private theorem finished_append (first last : Report state) :
    Finished (first.append last) ↔ Finished first ∧ Finished last := by
  simp only [Finished,Report.append,List.append_eq_nil_iff]
  constructor
  · rintro ⟨⟨a,b⟩,⟨c,d⟩,e,f⟩; exact ⟨⟨a,c,e⟩,b,d,f⟩
  · rintro ⟨⟨a,c,e⟩,b,d,f⟩; exact ⟨⟨a,b⟩,⟨c,d⟩,e,f⟩

private theorem many_length (state : GeneralNominalState.State)
    (queries : List Query) (bounds : List (GeneralNominalInspection.Bounds state)) (origins : Nat → Option Origin) (index : Nat)
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

/-- A successful actual type-argument traversal preserves every argument,
including nonpoint intervals; row parameters cannot disappear silently. -/
theorem type_arguments_exact (parameters : List (GeneralNominalState.Parameter slots))
    (bounds : List (Fin slots × Fin slots)) (found : typeArguments parameters = some bounds) :
    parameters = bounds.map GeneralNominalState.Parameter.type := by
  induction parameters generalizing bounds with
  | nil => simp [typeArguments] at found; subst bounds; rfl
  | cons parameter rest ih =>
    cases parameter with
    | row row => simp [typeArguments,List.mapM_cons] at found
    | type pair =>
      cases result : typeArguments rest with
      | none =>
        unfold typeArguments at result
        simp [typeArguments,List.mapM_cons,result] at found
      | some tail =>
        have equation := result
        unfold typeArguments at equation
        have value : bounds = pair :: tail := by
          simpa [typeArguments,List.mapM_cons,equation] using found.symm
        subst bounds
        simp only [List.map_cons]
        rw [ih tail result]

/-- Arbitrary finite arity input capture obtains its actual descriptor and
ordered interval bounds from Finished, rather than taking them as a witness. -/
theorem inspected_leaf (state : GeneralNominalState.State) (name : Nat)
    (names : Fin n → Nat) (slot : Fin state.base.slots) (origin : Option Origin)
    (finished : Finished (inspect state (.nominal name (List.ofFn fun i => .variables [names i]))
      (slot,slot) origin)) :
    ∃ bounds : Fin n → GeneralNominalInspection.Bounds state,
      ∃ spine : Spine state names bounds slot,
        spine.query = .nominal name (List.ofFn fun i => .variables [names i]) := by
  simp only [inspect] at finished
  split at finished
  · split at finished <;> simp [Finished,block,Report.visit] at finished
  · rename_i descriptor recorded
    split at finished
    · rename_i sameName
      split at finished
      · simp [Finished,block,Report.visit] at finished
      · rename_i arguments found
        simp only [↓reduceIte] at finished
        have len := many_length state _ arguments _ _ finished
        have length : n = arguments.length := by simpa using len
        let bounds : Fin n → GeneralNominalInspection.Bounds state := fun i => arguments[i.val]'(by omega)
        have bounds_eq : List.ofFn bounds = arguments := by
          apply List.ext_getElem
          · simp [length]
          · intro i hi hj; simp [bounds]
        have parameters := type_arguments_exact descriptor.arguments arguments found
        have exactParameters : descriptor.arguments = List.ofFn fun i => GeneralNominalState.Parameter.type (bounds i) := by
          rw [parameters,← bounds_eq,List.map_ofFn]
          rfl
        exact ⟨bounds,.leaf slot descriptor recorded exactParameters,by simp [Spine.query,sameName]⟩
    · simp [Finished,Report.visit] at finished
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalRecursiveCandidates

/-- A real completed candidate report discovers the input-side spine witness
for a variable-parameter nominal head. The format is explicit; arbitrary
branching heads and repeated binders are not included by this constructor. -/
theorem input_exists (context : Context) (root : Occurrence roles) (declaration : Declaration)
    (terminal : declaration.requirements = []) (role : declaration.role = root.demand.role)
    (slot : Fin context.state.base.slots) (name : Nat) (names : Fin n → Nat)
    (distinct : Function.Injective names) (inputs : declaration.inputNames = List.ofFn names)
    (queries : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal name (List.ofFn fun i => .variables [names i])])
    (located : arguments context root = some [(slot,slot)])
    (defined : GeneralNominalMaterialization.RootDefined declaration root)
    (finished : Finished (report context declaration [(slot,slot)])) :
    ∃ input : GeneralDictionary171SpineDiscovery.Input context root declaration, input.slot = slot := by
  have inspected : Finished (inspect context.state (.nominal name (List.ofFn fun i => .variables [names i]))
      (slot,slot) none) := by
    simpa only [Finished,report,queries,inspectMany,Report.append,List.append_nil] using finished
  obtain ⟨bounds,spine,same⟩ := inspected_leaf context.state name names slot none inspected
  exact ⟨⟨terminal,role,slot,n,names,distinct,inputs,bounds,spine,by rw [same]; exact queries,located,defined⟩,rfl⟩
end Yulang.GeneralDictionary171InputDiscovery
