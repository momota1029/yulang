import Yulang.GeneralSourceRoleCstCatalogControl296

/-! Recover only the name decisions encoded by a supported old default.
A positional binder is a check, not a name-map entry. -/
namespace Yulang.GeneralSourceRoleCstReifyBody296
open GeneralSourceRoleSpelling292 (Body Environment Output ResolvedBody position position_exact)
open GeneralSourceRoleCstNamingRequests295 (Query bodyQueries outputQueries reply)
open GeneralSourceRoleCstNamingTrace295 (Trace values)
open GeneralSourceRoleExport292 (OutputWitness)

def bodyEvidence (xs : List String) : Body → Option Roles.Term → Option Trace
  | .required,none => some []
  | .binder s,some (.var i) => if position s xs = some i then some [] else none
  | .nullary s,some (.app j []) => some [(.constructor s,some j)]
  | _,_ => none

theorem from_resolved {e : Environment} {xs : List String} {b : Body} {v : Option Roles.Term}
    (ok : ResolvedBody e xs b v) :
    bodyEvidence xs b v = some (values e (bodyQueries b)) := by
  cases ok with
  | required => rfl
  | binder located => simp [bodyEvidence,bodyQueries,values,(position_exact ..).mpr located]
  | nullary h => simp [bodyEvidence,bodyQueries,values,reply,h]

def fieldEvidence (r : Nat) (xs : List String) (o : Output) (row : Nat × Option Roles.Term) :
    Option Trace :=
  (bodyEvidence xs o.body row.2).map (((.output r o.spelling),some row.1)::·)

theorem from_output {e : Environment} {r : Nat} {xs : List String} {o : Output}
    {field : Nat × Option Roles.Term} (h : OutputWitness e r xs o field) :
    fieldEvidence r xs o field = some (values e (outputQueries e r o)) := by
  unfold fieldEvidence
  rw [from_resolved h.2]
  simp [values,outputQueries,h.1,reply]

def Matches (e : Environment) (t : Trace) : Prop :=
  ∀ pair ∈ t, reply e pair.1 = pair.2

theorem values_match (e : Environment) (qs : List Query) : Matches e (values e qs) := by
  intro row mem
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp mem
  rfl

theorem matches_cons (e : Environment) (q : Query) (v : Option Nat) (t : Trace) :
    Matches e ((q,v)::t) ↔ reply e q = v ∧ Matches e t := by
  simp [Matches]

theorem body_replay {e : Environment} {xs : List String} {b : Body} {v : Option Roles.Term}
    {t : Trace} (decoded : bodyEvidence xs b v = some t) (known : Matches e t) :
    ResolvedBody e xs b v := by
  cases b with
  | required =>
    cases v with
    | none => exact .required
    | some value => cases decoded
  | binder s =>
    cases v with
    | none => cases decoded
    | some x =>
      cases x with
      | app _ _ => cases decoded
      | var i =>
        by_cases h : position s xs = some i
        · exact .binder ((position_exact ..).mp h)
        · simp [bodyEvidence,h] at decoded
  | nullary s =>
    cases v with
    | none => cases decoded
    | some x =>
      cases x with
      | var i => cases decoded
      | app j args =>
        cases args with
        | cons h tail => cases decoded
        | nil =>
          have eq : [(.constructor s,some j)] = t := Option.some.inj decoded
          rw [←eq] at known
          exact .nullary (known _ List.mem_cons_self)

theorem field_replay {e : Environment} {r : Nat} {xs : List String} {o : Output}
    {field : Nat × Option Roles.Term} {t : Trace}
    (decoded : fieldEvidence r xs o field = some t) (known : Matches e t) :
    OutputWitness e r xs o field := by
  cases h : bodyEvidence xs o.body field.2 with
  | none => simp [fieldEvidence,h] at decoded
  | some tail =>
    have eq : (.output r o.spelling,some field.1)::tail = t := by
      simpa [fieldEvidence,h] using decoded
    rw [←eq,matches_cons] at known
    exact ⟨known.1,body_replay h known.2⟩

end Yulang.GeneralSourceRoleCstReifyBody296
