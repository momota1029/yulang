import Yulang.GeneralDeclarativeI65OriginalBodyEvent393
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDictionaryAssociatedProvenance (Body Supplies lookup lookup_exact)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarations (Equation)
section
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeOutputs320 (bodyCapture)

-- Old ordinary lane only. This attestation is an input from B6,
-- not an evaluation attempt made while B4 selects an impl.
structure B6OrdinarySource398 (s : State) (body : Body) where
  term : Expr
  authored :
    translate (authoredRegistry s.current).constructors
      (interpretation s.current.environment.source.snapshot)
      (normalize (bodyPattern body)) = some term

structure B6OrdinaryAtlas398 (s : State) where
  explicit : (sourceOrdinal : Nat) → (eq : Equation) →
    Option (B6OrdinarySource398 s (.explicit eq))
  roleDefault : (role name : Nat) → (rhs : Roles.Term) →
    Option (B6OrdinarySource398 s (.default role name rhs))

def B6OrdinaryAtlas398.read {s} (atlas : B6OrdinaryAtlas398 s) (ordinal : Nat)
    (body : Body) : Option (B6OrdinarySource398 s body) :=
  match body with
  | .explicit written => atlas.explicit ordinal written
  | .default role name rhs => atlas.roleDefault role name rhs

def ordinary_role_output_from_B6398 {s q}
    (frame : AuthoredBodyFrame393 s q)
    (atlas : B6OrdinaryAtlas398 s)
    (i : Fin q.demand.outputs.length)
    (wf : (frame.decl.associated.map Equation.name).Nodup) :
    Option (AuthoredOutput393 frame i) :=
  let roles := (authoredRegistry s.current).roles
  let requested := q.demand.outputs[i]
  match found : lookup roles frame.decl requested.name with
  | none => none
  | some body => do
    let typed ← atlas.read frame.ordinal body
    if slotsRead : (normalize (bodyPattern body)).variables.all
        (fun n => (frame.slots body n).isSome) = true then
      let equation : GeneralDeclarativeHead320.Equation :=
        ⟨requested.target,logical (bodyCapture q.demand frame.names.input body) .actual typed.term⟩
      some ⟨body,(lookup_exact roles frame.decl wf requested.name body).mp found,
        .ordinary equation,.ordinary (List.all_eq_true.mp slotsRead) typed.authored⟩
    else none

theorem old_ordinary_payload_agrees_B6398 {s q}
    (f : AuthoredBodyFrame393 s q) {b : Body} (input : B6OrdinarySource398 s b)
    {target} {eq : GeneralDeclarativeHead320.Equation}
    (old : BodyWrite393 f b target (.ordinary eq)) :
    eq = ⟨target,logical (bodyCapture q.demand f.names.input b) .actual input.term⟩ := by
  cases old with
  | ordinary _ compiled =>
    have same := Option.some.inj (compiled.symm.trans input.authored)
    rw [same]

theorem B6_ordinary_receipt_keeps_target398 {s q} (f : AuthoredBodyFrame393 s q)
    {atlas : B6OrdinaryAtlas398 s} {i : Fin q.demand.outputs.length}
    {wf : (f.decl.associated.map Equation.name).Nodup}
    {out : AuthoredOutput393 f i}
    (_made : ordinary_role_output_from_B6398 f atlas i wf = some out) :
    out.receipt.occurrence = q.occurrence ∧ out.receipt.ordinal = i.val ∧
      q.demand.outputs[i.val]? = some out.receipt.requested ∧ out.receipt.writesTarget :=
  ⟨rfl,rfl,List.getElem?_eq_getElem i.isLt,out.fixed⟩
end


private theorem lookup_named_value_exact398 (names : List Nat) (values : Nat → Capture)
    (key : Nat) {result : Capture}
    (hit : (names.map fun n => (n,values n)).lookup key = some result) :
    values key = result := by
  induction names with
  | nil => simp at hit
  | cons head rest ih =>
    by_cases same : key = head
    · subst head
      simpa using hit
    · have different : (key == head) = false := beq_eq_false_iff_ne.mpr same
      exact ih (by simpa only [List.map_cons,List.lookup,different] using hit)

/-- A successful new explicit/positional read uses the same lexical
capture as the old ordinary substitution. The legacy totalizing
fallback is unused at these real source reads. -/
theorem checked_slot_is_exact_body_capture398 {s q} (f : AuthoredBodyFrame393 s q)
    (body : Body) (n : Nat) {cap : Capture}
    (read : f.slots body n = some cap) :
    GeneralDeclarativeOutputs320.bodyCapture q.demand f.names.input body n = cap := by
  cases body with
  | explicit equation =>
    exact lookup_named_value_exact398 _ _ n read
  | default role name term =>
    cases seen : q.demand.arguments[n]? with
    | none => simp [AuthoredBodyFrame393.slots,seen] at read
    | some actual =>
      have same : (⟨actual.center,actual.center,actual.center⟩ : Capture) = cap := by
        simpa only [AuthoredBodyFrame393.slots,seen,Option.map_some,Option.some.injEq] using read
      exact (GeneralDeclarativeOutputs320.positional_exact q.demand seen).trans same


private theorem lookup_member_present398 (names : List Nat) (get : Nat → Capture)
    (n : Nat) (member : n ∈ names) :
    (names.map fun m => (m,get m)).lookup n = some (get n) := by
  induction names with
  | nil => cases member
  | cons first rest ih =>
    by_cases equal : first = n
    · subst first
      simp
    · have unequal : (n == first) = false := beq_eq_false_iff_ne.mpr (Ne.symm equal)
      have later := (List.mem_cons.mp member).resolve_left (Ne.symm equal)
      simp only [List.map_cons,List.lookup,unequal,ih later]

/-- A real explicit body's used lexical references are all provided by
the actual source table, by the declaration-scope proof, not by B6
typing or an additional readback premise of dictionary_sound. -/
theorem explicit_B4_slots_total398 {s q} (f : AuthoredBodyFrame393 s q)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current))
    {eq : Equation} (written : eq ∈ f.decl.associated) :
    ∀ n ∈ (normalize (bodyPattern (.explicit eq))).variables,
      (f.slots (.explicit eq) n).isSome = true := by
  have actual := checked.2 f.decl ((visible_exact s q f.decl).mp f.inScope).1
  intro n occurs
  have inScope := actual.scope.2.1 eq written n occurs
  have member : n ∈ f.decl.inputNames ++ f.decl.outputNames := List.mem_append.mpr inScope
  have exactRead := lookup_member_present398 _ f.names.input n member
  simp only [AuthoredBodyFrame393.slots,AuthoredBodyFrame393.captures,exactRead,Option.isSome]

end Yulang.GeneralDeclarativeI65
