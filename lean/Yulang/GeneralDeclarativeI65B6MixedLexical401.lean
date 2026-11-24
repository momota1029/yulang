import Yulang.GeneralDeclarativeI65B6TypedPlanConservative401

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarativeWhere319 (Capture)
open CommonDeclaredNominalInspection (Kind)
open GeneralDeclarationPatterns (Pattern normalize variablesArgs)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDictionaryAssociatedProvenance (Body Supplies)
open GeneralDeclarations (Checked Declaration)
open GeneralDeclarativeEmissionForest322 (Placement)

/-- The B6 annotation changes how a reference is evaluated, not
which lexical source it names. Includes duplicates in source order,
rather than passing to a set or guessing a new slot for a primitive. -/
theorem mixed_reads_are_exact_original_variables401 {s c p} (plan : B6MixedRhs401 s c p) :
    (mixedRhsNeeds401 plan).map Prod.fst = p.variables := by
  refine MixedRhs401.rec
    (motive_1 := fun _ p t => (mixedRhsNeeds401 t).map Prod.fst = p.variables)
    (motive_2 := fun _ _ p t => (mixedArgNeeds401 t).map Prod.fst = p.variables)
    (motive_3 := fun _ _ ps t => (mixedArgsNeeds401 t).map Prod.fst = variablesArgs ps)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ plan
  · intros; rfl
  · intro c p q label a b ha hb
    simp [mixedRhsNeeds401,Pattern.variables,ha,hb]
  · intro c p tag a ha; exact ha
  · intro c a b x y ha hb
    simp [mixedRhsNeeds401,Pattern.variables,ha,hb]
  · intro ps c params n use kinds exacts a ha; exact ha
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro c a b n use kind x y hx hy
    simp [mixedRhsNeeds401,Pattern.variables,variablesArgs,hx,hy]
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro p pat c kind compound a ha; exact ha
  · intros; rfl
  · intro c ap aps p ps a b ha hb
    simp [mixedArgsNeeds401,variablesArgs,ha,hb]

/-- This is only the emitted syntax/name binding. B6 provides the
kind in the index; the capture is read from the original source
frame. Native structural endpoint validity remains separate. -/
abbrev NamedSlot401 (slots : Nat → Option Capture) (_ : Kind) (n : Nat) :=
  {cap : Capture // slots n = some cap}

abbrev NamedMixedTree401 (s : State) (slots : Nat → Option Capture) :=
  MixedRhs401 s (NamedSlot401 slots)

def instantiateName401 (slots : Nat → Option Capture) (k : Kind) (n : Nat)
    (_ : Unit) : Option (NamedSlot401 slots k n) :=
  match h : slots n with
  | none => none
  | some cap => some ⟨cap,h⟩

theorem instantiateName401_of_some {slots : Nat → Option Capture}
    {k : Kind} {n : Nat} {cap : Capture} (got : slots n = some cap) :
    instantiateName401 slots k n () = some ⟨cap,got⟩ := by
  unfold instantiateName401
  split
  next missing => rw [got] at missing; cases missing
  next actual found =>
    have eq := Option.some.inj (found.symm.trans got)
    subst actual
    rfl

def actualNamedMixedRead401 (m : Model) {slots : Nat → Option Capture} (k : Kind) (n : Nat)
    (slot : NamedSlot401 slots k n) : Option (CommonNominalFullCarrier.Ty × CommonNominalFullCarrier.Row) :=
  some (m.assignment slot.val.center)

private def CoveredNames401 (slots : Nat → Option Capture) (xs : List (Nat × Kind)) : Prop :=
  ∀ n k, (n,k) ∈ xs → ∃ cap, slots n = some cap

private theorem coveredLeft401 {slots a b} (h : CoveredNames401 slots (a ++ b)) :
    CoveredNames401 slots a := fun n k seen => h n k (List.mem_append_left _ seen)

private theorem coveredRight401 {slots a b} (h : CoveredNames401 slots (a ++ b)) :
    CoveredNames401 slots b := fun n k seen => h n k (List.mem_append_right _ seen)

theorem exact_mixed_names_are_substitutable401 {s c p}
    (slots : Nat → Option Capture) (plan : B6MixedRhs401 s c p)
    (whole : ∀ n ∈ p.variables, (slots n).isSome = true) :
    ∃ tree : NamedMixedTree401 s slots c p,
      substituteMixedRhs401 (instantiateName401 slots) plan = some tree := by
  have covered : CoveredNames401 slots (mixedRhsNeeds401 plan) := by
    intro n k actual
    have named : n ∈ p.variables := by
      rw [← mixed_reads_are_exact_original_variables401 plan]
      exact List.mem_map_of_mem actual
    have present := whole n named
    cases h : slots n with
    | none => simp [h] at present
    | some cap => exact ⟨cap,rfl⟩
  revert covered
  refine MixedRhs401.rec
    (motive_1 := fun _ _ t => CoveredNames401 slots (mixedRhsNeeds401 t) → ∃ tree,
      substituteMixedRhs401 (instantiateName401 slots) t = some tree)
    (motive_2 := fun _ _ _ t => CoveredNames401 slots (mixedArgNeeds401 t) → ∃ tree,
      substituteMixedArg401 (instantiateName401 slots) t = some tree)
    (motive_3 := fun _ _ _ t => CoveredNames401 slots (mixedArgsNeeds401 t) → ∃ tree,
      substituteMixedArgs401 (instantiateName401 slots) t = some tree)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ plan
  · intro c n tok h
    obtain ⟨cap,got⟩ := h n .value List.mem_cons_self
    cases tok
    exact ⟨.binder n ⟨cap,got⟩, by simp only [substituteMixedRhs401,
      instantiateName401_of_some got,Option.map_some]⟩
  · intro c p q label a b ha hb h
    obtain ⟨x,hx⟩ := ha (coveredLeft401 h)
    obtain ⟨y,hy⟩ := hb (coveredRight401 h)
    exact ⟨.record label x y, by simp [substituteMixedRhs401,hx,hy]⟩
  · intro c p tag a ha h
    obtain ⟨x,hx⟩ := ha h
    exact ⟨.variant tag x, by simp [substituteMixedRhs401,hx]⟩
  · intro c p q a b ha hb h
    obtain ⟨x,hx⟩ := ha (coveredLeft401 h)
    obtain ⟨y,hy⟩ := hb (coveredRight401 h)
    exact ⟨.join x y, by simp [substituteMixedRhs401,hx,hy]⟩
  · intro ps c params n use kinds exacts a ha h
    obtain ⟨x,hx⟩ := ha h
    exact ⟨.declaredApp n use kinds exacts x, by simp [substituteMixedRhs401,hx]⟩
  · intros; exact ⟨_,rfl⟩
  · intros; exact ⟨_,rfl⟩
  · intros; exact ⟨_,rfl⟩
  · intro c a b n use prim x y hx hy h
    obtain ⟨vx,ex⟩ := hx (coveredLeft401 h)
    obtain ⟨vy,ey⟩ := hy (coveredRight401 h)
    exact ⟨.pair n use prim vx vy,by simp [substituteMixedRhs401,ex,ey]⟩
  · intro c p n kind mode tok h
    obtain ⟨cap,got⟩ := h n .value List.mem_cons_self
    cases tok
    exact ⟨.valuePoint n kind mode ⟨cap,got⟩, by simp only [substituteMixedArg401,
      instantiateName401_of_some got,Option.map_some]⟩
  · intro c p n kind mode tok h
    obtain ⟨cap,got⟩ := h n .value List.mem_cons_self
    cases tok
    exact ⟨.valueInterval n kind mode ⟨cap,got⟩, by simp only [substituteMixedArg401,
      instantiateName401_of_some got,Option.map_some]⟩
  · intro c p n kind mode tok h
    obtain ⟨cap,got⟩ := h n .row List.mem_cons_self
    cases tok
    exact ⟨.rowPoint n kind mode ⟨cap,got⟩, by simp only [substituteMixedArg401,
      instantiateName401_of_some got,Option.map_some]⟩
  · intro c p n kind mode tok h
    obtain ⟨cap,got⟩ := h n .row List.mem_cons_self
    cases tok
    exact ⟨.rowInterval n kind mode ⟨cap,got⟩, by simp only [substituteMixedArg401,
      instantiateName401_of_some got,Option.map_some]⟩
  · intro p pat c kind compound a ha h
    obtain ⟨x,hx⟩ := ha h
    exact ⟨.valueTree kind compound x, by simp [substituteMixedArg401,hx]⟩
  · intros; exact ⟨.nil,rfl⟩
  · intro c ap aps p ps a b ha hb h
    obtain ⟨x,hx⟩ := ha (coveredLeft401 h)
    obtain ⟨y,hy⟩ := hb (coveredRight401 h)
    exact ⟨.cons x y,by simp [substituteMixedArgs401,hx,hy]⟩

theorem source_and_lexically_instantiated_tree_read_same_model401 {s c p slots}
    (plan : B6MixedRhs401 s c p) (target : NamedMixedTree401 s slots c p)
    (instantiated : substituteMixedRhs401 (instantiateName401 slots) plan = some target) (m : Model) :
    ∃ ty, evaluateMixedRhs401 (actualNamedMixedRead401 m) target = some ty ∧
      evaluateMixedRhs401 (sourceRead401 m slots) plan = some ty := by
  have read := mixed_substitution_value_fusion401 (instantiateName401 slots) (actualNamedMixedRead401 m) plan
  rw [instantiated] at read
  change evaluateMixedRhs401 (actualNamedMixedRead401 m) target = _ at read
  have same : (fun k n x => (instantiateName401 slots k n x).bind (actualNamedMixedRead401 m k n)) =
      sourceRead401 m slots := by
    funext k n x
    cases x
    cases hit : slots n with
    | none => simp [instantiateName401,sourceRead401,hit]
    | some cap => simp [instantiateName401_of_some hit,actualNamedMixedRead401,sourceRead401,hit]
  rw [same] at read
  obtain ⟨ty,ok⟩ := mixed_value_total_on_bound_leaves401 (actualNamedMixedRead401 m)
    (fun _ _ cap => ⟨m.assignment cap.val.center,rfl⟩) target
  exact ⟨ty,ok,read.symm.trans ok⟩

/-- C395/399's actual selected declaration and positive head supply
all lexical names for the exact B6 supplier, including defaults at
original argument positions. This conclusion doesn't require the
old vector or a second native kind/endpoint witness merely to name
the slot. It is *not* a bound validity or classifier-totality claim. -/
theorem original_stored_head_supplies_all_named_mixed_slots401 {s q row}
    {t : CandidateTape s q (visible s q)} (origin : SelectedHeadOrigin395 (row := row) t)
    (place : Placement) (outside : Nat → Capture)
    (checked : Checked (authoredRegistry s.current))
    {name body} (supply : Supplies (authoredRegistry s.current).roles row name body)
    (plan : B6MixedRhs401 s false (normalize (bodyPattern body))) :
    let f := preoutputFrameOfOrigin399 origin place outside
    ∃ rhs : NamedMixedTree401 s (f.slots body) false (normalize (bodyPattern body)),
      substituteMixedRhs401 (instantiateName401 (f.slots body)) plan = some rhs ∧
      ∀ m : Model, ∃ ty, evaluateMixedRhs401 (actualNamedMixedRead401 m) rhs = some ty ∧
        evaluateMixedRhs401 (sourceRead401 m (f.slots body)) plan = some ty := by
  let f := preoutputFrameOfOrigin399 origin place outside
  have arity : q.demand.arguments.length = f.decl.head.length :=
    observed_preoutput_demand_head_lengths399 origin.pick.head
  have covered := original_frame_slot_coverage399 f checked arity (default_positions_from_authored_role_decl399 s) supply
  obtain ⟨rhs,made⟩ := exact_mixed_names_are_substitutable401 (f.slots body) plan covered
  exact ⟨rhs,made,fun m => source_and_lexically_instantiated_tree_read_same_model401 plan rhs made m⟩


open GeneralDictionaryAssociatedProvenance (lookup lookup_exact)
open CommonNominalFullCarrier (Ty)

structure NamedMixedOutput401 {s q} (atlas : B6OccurrenceAtlas401 s)
    (f : AuthoredBodyFrame393 s q) (i : Fin q.demand.outputs.length) where
  body : Body
  supplied : Supplies (authoredRegistry s.current).roles f.decl q.demand.outputs[i].name body
  plan : B6MixedRhs401 s false (normalize (bodyPattern body))
  originalTyped : atlas.read q f.ordinal i body = some plan
  rhs : NamedMixedTree401 s (f.slots body) false (normalize (bodyPattern body))
  formed : substituteMixedRhs401 (instantiateName401 (f.slots body)) plan = some rhs

structure NamedMixedReceipt401 (s : State) where
  occurrence : List Nat
  outputOrdinal : Nat
  original : GeneralSourceState.Output
  body : Body
  slots : Nat → Option Capture
  rhs : NamedMixedTree401 s slots false (normalize (bodyPattern body))

def NamedMixedOutput401.receipt {s q atlas f i}
    (out : NamedMixedOutput401 (s := s) (q := q) atlas f i) : NamedMixedReceipt401 s :=
  ⟨q.occurrence,i,q.demand.outputs[i],out.body,f.slots out.body,out.rhs⟩

def NamedMixedReceipt401.actualEquation {s} (r : NamedMixedReceipt401 s) (m : Model) :
    Option (Nat × Ty) :=
  (evaluateMixedRhs401 (actualNamedMixedRead401 m) r.rhs).map fun value => (r.original.target,value)

theorem named_mixed_output_is_fixed_equation401 {s q atlas f i}
    (out : NamedMixedOutput401 (s := s) (q := q) atlas f i) (m : Model) :
    ∃ ty, out.receipt.actualEquation m = some (q.demand.outputs[i].target,ty) ∧
      evaluateMixedRhs401 (sourceRead401 m (f.slots out.body)) out.plan = some ty := by
  obtain ⟨ty,read,proved⟩ := source_and_lexically_instantiated_tree_read_same_model401
    out.plan out.rhs out.formed m
  exact ⟨ty,by simp [NamedMixedOutput401.receipt,NamedMixedReceipt401.actualEquation,read],proved⟩

def NamedInputAtStoredHead401 {s q} (atlas : B6OccurrenceAtlas401 s)
    (f : AuthoredBodyFrame393 s q) : Prop :=
  ∀ (i : Fin q.demand.outputs.length) (body : Body),
    Supplies (authoredRegistry s.current).roles f.decl q.demand.outputs[i].name body →
    ∃ plan, atlas.read q f.ordinal i body = some plan

/-- For any genuine stored positive head of the original choice,
instantiate the B6 annotation on every requested associated output.
The names are derived from source scoping and actual head arity,
not assumed to be provided as another whole capture table. This only
uses the known original frame placement; an all-state Classifies
constructor and its independent authorization are still separate. -/
theorem stored_head_emits_exact_ordered_mixed_values401 {s q row}
    {t : CandidateTape s q (visible s q)} (origin : SelectedHeadOrigin395 (row := row) t)
    (place : Placement) (outside : Nat → Capture) (checked : Checked (authoredRegistry s.current))
    (declared : DeclaredOriginalOutputs400 s q) (atlas : B6OccurrenceAtlas401 s)
    (typed : NamedInputAtStoredHead401 atlas (preoutputFrameOfOrigin399 origin place outside)) :
    let f := preoutputFrameOfOrigin399 origin place outside
    ∃ each : ∀ i : Fin q.demand.outputs.length, NamedMixedOutput401 atlas f i,
      ∃ outputs : List (NamedMixedReceipt401 s),
        outputs.length = q.demand.outputs.length ∧
        ∀ i : Fin q.demand.outputs.length,
          outputs[i.val]? = some (each i).receipt ∧
          lookup (authoredRegistry s.current).roles f.decl q.demand.outputs[i].name = some (each i).body ∧
          (each i).receipt.occurrence = q.occurrence ∧ (each i).receipt.outputOrdinal = i.val ∧
          (each i).receipt.original = q.demand.outputs[i] ∧
          ∀ m : Model, ∃ ty,
            (each i).receipt.actualEquation m = some (q.demand.outputs[i].target,ty) ∧
            evaluateMixedRhs401 (sourceRead401 m (f.slots (each i).body)) (each i).plan = some ty := by
  classical
  let f := preoutputFrameOfOrigin399 origin place outside
  have rule := checked.2 f.decl (List.mem_of_getElem? f.authored)
  have role := (visible_exact s q f.decl).mp f.inScope |>.2
  have output (i : Fin q.demand.outputs.length) : Nonempty (NamedMixedOutput401 atlas f i) := by
    obtain ⟨body,source⟩ := GeneralDictionaryAssociatedProvenance.declared_covered
      (authoredRegistry s.current).roles f.decl rule.signature q.demand.outputs[i].name
      (role ▸ declared i)
    obtain ⟨plan,original⟩ := typed i body source
    obtain ⟨tree,made,_⟩ :=
      original_stored_head_supplies_all_named_mixed_slots401 origin place outside checked source plan
    exact ⟨⟨body,source,plan,original,tree,made⟩⟩
  let each (i : Fin q.demand.outputs.length) := Classical.choice (output i)
  refine ⟨each,List.ofFn (fun i => (each i).receipt),by simp,?_⟩
  intro i
  have supplier := (lookup_exact _ _ rule.identified.2.2.1 _ _).mpr (each i).supplied
  exact ⟨by simp,supplier,rfl,rfl,rfl,fun m => named_mixed_output_is_fixed_equation401 (each i) m⟩

end Yulang.GeneralDeclarativeI65
