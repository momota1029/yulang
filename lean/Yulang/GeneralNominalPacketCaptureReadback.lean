import Yulang.GeneralNominalFallbackReadback

/-! The actual installing packet supplies finite readbacks for all usable
captures, including original-report endpoint fallbacks after structural
descent. Each capture is bounded by the total input-label mass. -/
set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalPacketCaptureReadback
open GeneralNominalRecursiveInspection GeneralNominalFallbackReadback
open GeneralNominalGroundAccessibility GeneralNominalGroundForests
open GeneralNominalInspection (Query Bounds)
open GeneralNominalSaturationState GeneralDeclarationPatterns
open GeneralNominalSharedCaptures
open GeneralNominalPatersonLineage (mass)

theorem locate_sources (base : GeneralSourceState.State) (inputs : List GeneralSourceState.Interval)
    (bounds : List (Fin base.slots × Fin base.slots))
    (located : GeneralCandidateBoundaryParts.locate base inputs = some bounds) :
    bounds.map (fun interval => (base.source interval.1,base.source interval.2)) = inputs := by
  have general {α β : Type} (f : α → Option β) (g : β → α)
      (inverse : ∀ a b, f a = some b → g b = a) (xs : List α) (ys : List β)
      (found : xs.mapM f = some ys) : ys.map g = xs := by
    induction xs generalizing ys with
    | nil => simp at found; subst ys; rfl
    | cons head tail ih =>
      cases first : f head <;> simp only [List.mapM_cons,first] at found
      · cases found
      · rename_i value
        cases rest : tail.mapM f <;> simp only [rest] at found
        · cases found
        · rename_i next
          cases Option.some.inj found
          simp only [List.map_cons,inverse head value first,ih next rest]
  apply general _ _ ?_ inputs bounds located
  intro input output found
  change ((GeneralDictionaryBinderLocations.sourceSlot base input.1).bind fun lower =>
    (GeneralDictionaryBinderLocations.sourceSlot base input.2).bind fun upper => some (lower,upper)) = some output at found
  cases lower : GeneralDictionaryBinderLocations.sourceSlot base input.1 <;>
    simp only [lower,Option.bind_none,Option.bind_some] at found
  · cases found
  · rename_i a
    cases upper : GeneralDictionaryBinderLocations.sourceSlot base input.2 <;>
      simp only [upper,Option.bind_none,Option.bind_some] at found
    · cases found
    · rename_i b
      cases Option.some.inj found
      exact Prod.ext ((GeneralDictionaryBinderLocations.sourceSlot_exact _ _ _).mp lower)
        ((GeneralDictionaryBinderLocations.sourceSlot_exact _ _ _).mp upper)

theorem many_capture (state : GeneralNominalState.State) (queries : List Query)
    (bounds : List (Bounds state)) (origins : Nat → Option Origin) (offset : Nat)
    {capture : Capture state} (member : capture ∈ (inspectMany state queries bounds origins offset).captures) :
    ∃ index query interval, queries[index]? = some query ∧ bounds[index]? = some interval ∧
      capture ∈ (inspect state query interval (origins (offset+index))).captures := by
  induction queries generalizing bounds offset with
  | nil => cases bounds <;> simp [inspectMany] at member
  | cons query rest ih =>
    cases bounds with
    | nil => simp [inspectMany] at member
    | cons head tail =>
      simp only [inspectMany,Report.append] at member
      rcases List.mem_append.mp member with first | last
      · exact ⟨0,query,head,rfl,rfl,by simpa only [Nat.add_zero] using first⟩
      · obtain ⟨index,child,interval,queryAt,boundsAt,present⟩ := ih tail (offset+1) last
        exact ⟨index+1,child,interval,queryAt,boundsAt,by
          simpa only [Nat.add_assoc,Nat.add_comm 1 index] using present⟩

theorem member_mass (patterns : List Pattern) (member : pattern ∈ patterns) : mass [pattern] ≤ mass patterns := by
  induction patterns with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · simp [mass,counted,normalizeArgs,encodeArgs,Roles.argsSize]
    · have bound := ih member
      simp only [mass,counted,normalizeArgs,encodeArgs,Roles.argsSize] at *
      omega

theorem packet_capture {model : GeneralNominalCommonBridge.Assignment}
    (state : State roles) (packet : Packet roles) (same : state.context = packet.context)
    (safe : GeneralNominalActualInspectionSteps.Safe state packet)
    (located : GeneralNominalRecursiveCandidates.arguments packet.context packet.site.occurrence = some packet.bounds)
    (valid : Models state model) (known : Inputs context model packet.site labels)
    {capture : Capture packet.context.state} (member : capture ∈ (inheritedReport packet).captures)
    (recorded : capture.origin = some origin) (observed : Observes model origin actual) :
    Bounded context model (mass labels) origin := by
  obtain ⟨index,query,interval,queryAt,boundsAt,present⟩ := many_capture packet.context.state _ packet.bounds _ 0 member
  simp only [Nat.zero_add] at present
  have boundsLength : packet.bounds.length = (roles packet.site.occurrence.demand.role).arity := by
    simpa only [List.length_ofFn] using GeneralNominalPacketCodes.locate_length packet.context.state.base
      (List.ofFn packet.site.occurrence.demand.arguments) packet.bounds located
  have inside : index < (roles packet.site.occurrence.demand.role).arity := by
    rw [← boundsLength]
    exact (List.getElem?_eq_some_iff.mp boundsAt).1
  let position : Fin (roles packet.site.occurrence.demand.role).arity := ⟨index,inside⟩
  have inputInside : index < packet.site.inputs.length := by rw [packet.site.arity]; exact inside
  have sources := congrArg (fun inputs => inputs[index]?)
    (locate_sources packet.context.state.base (List.ofFn packet.site.occurrence.demand.arguments) packet.bounds located)
  have sources : (packet.context.state.base.source interval.1,packet.context.state.base.source interval.2) =
      packet.site.occurrence.demand.arguments position := by
    simpa only [List.getElem?_map,boundsAt,Option.map_some,List.getElem?_ofFn,inside,dite_eq_left,Option.some.injEq]
      using sources
  let localState : State roles := {state with context := packet.context}
  have localEq : localState = state := by simp only [localState,← same]
  have supported := inspect_supported (context := context) (budget := mass labels) localState (localEq ▸ valid) query interval
    ((packet.site.inputs[index]?).join)
  apply supported ?_ ?_ capture present origin recorded actual observed
  · intro ref kept
    have entry : packet.site.inputs[index]? = some (some ref) := by
      rw [List.getElem?_eq_getElem inputInside] at kept ⊢
      cases entry : packet.site.inputs[index]'inputInside with
      | none => simp [entry] at kept
      | some value => simpa [entry] using kept
    obtain ⟨term,closed,_,retained⟩ := known.2 position
    exact ⟨_,term,closed,retained ref entry,member_mass labels (List.getElem_mem _)⟩
  · intro absent constructor
    have missing : packet.site.inputs[index]? = some none := by
      rw [List.getElem?_eq_getElem inputInside] at absent ⊢
      cases entry : packet.site.inputs[index]'inputInside with
      | none => rfl
      | some value => simp [entry] at absent
    obtain ⟨pattern,term,labelAt,closed,lower,upper⟩ := missing_constructor_meanings state packet safe located
      position queryAt constructor missing valid known
    have bounded := member_mass labels ((List.getElem?_eq_some_iff.mp labelAt).2 ▸
      List.getElem_mem (List.getElem?_eq_some_iff.mp labelAt).1)
    have endpoints : Endpoints context model (mass labels) packet.context.state interval := by
      unfold Endpoints
      rw [show packet.context.state.base.source interval.1 = (packet.site.occurrence.demand.arguments position).1
        from congrArg Prod.fst sources,
        show packet.context.state.base.source interval.2 = (packet.site.occurrence.demand.arguments position).2
        from congrArg Prod.snd sources]
      exact ⟨⟨pattern,term,closed,lower,bounded⟩,⟨pattern,term,closed,upper,bounded⟩⟩
    exact endpoints

theorem usable_closed {model : GeneralNominalCommonBridge.Assignment}
    (state : State roles) (packet : Packet roles) (same : state.context = packet.context)
    (safe : GeneralNominalActualInspectionSteps.Safe state packet)
    (located : GeneralNominalRecursiveCandidates.arguments packet.context packet.site.occurrence = some packet.bounds)
    (valid : Models state model) (branch : packet.Holds model) (known : Inputs context model packet.site labels)
    (usable : Usable packet name origin) : Bounded context model (mass labels) origin := by
  obtain ⟨capture,member,_,recorded⟩ := usable.1.1
  obtain ⟨actual,observed⟩ := (usable.2 model branch).1
  exact packet_capture state packet same safe located valid known member recorded observed

end Yulang.GeneralNominalPacketCaptureReadback
