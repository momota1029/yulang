import Yulang.GeneralSourceRoleCstReifyBody296

/-! Extract naming observations from a symbolic role and its ordered old row.
The row carrier alone contains no source spellings. -/
namespace Yulang.GeneralSourceRoleCstReifyRow296
open GeneralSourceRoleSpelling292 (Output Role Environment)
open GeneralSourceRoleExport292 (Aligned OutputWitness RowWitness role_exact resolveRole)
open GeneralSourceMetadataBareRole291 (BareRow)
open GeneralSourceRoleCstNamingRequests295 (outputQueries queryList reply)
open GeneralSourceRoleCstNamingTrace295 (Trace values capture)
open GeneralSourceRoleCstReifyBody296 (fieldEvidence from_output Matches matches_cons field_replay)

def fields (r : Nat) (xs : List String) : List Output → List (Nat × Option Roles.Term) → Option Trace
  | [],[] => some []
  | o::os,f::fs => (fieldEvidence r xs o f).bind fun a =>
    (fields r xs os fs).map (a ++ ·)
  | _,_ => none

theorem fields_from_aligned {e : Environment} {r : Nat} {xs : List String}
    {os : List Output} {fs : List (Nat × Option Roles.Term)}
    (ok : Aligned (OutputWitness e r xs) os fs) :
    fields r xs os fs = some (values e (os.flatMap (outputQueries e r))) := by
  induction ok with
  | nil => rfl
  | cons h tail ih => simp [fields,from_output h,ih,values]

theorem fields_replay {e : Environment} {r : Nat} {xs : List String}
    {os : List Output} {fs : List (Nat × Option Roles.Term)} {t : Trace}
    (got : fields r xs os fs = some t) (fits : Matches e t) :
    Aligned (OutputWitness e r xs) os fs := by
  induction os generalizing fs t with
  | nil =>
    cases fs with
    | nil => exact .nil
    | cons => cases got
  | cons o os ih =>
    cases fs with
    | nil => cases got
    | cons f fs =>
      cases front : fieldEvidence r xs o f with
      | none => simp [fields,front] at got
      | some head =>
        cases rest : fields r xs os fs with
        | none => simp [fields,front,rest] at got
        | some tail =>
          have eq : head ++ tail = t := by simpa [fields,front,rest] using got
          subst t
          exact .cons (field_replay front (fun p m => fits p (List.mem_append_left _ m)))
            (ih rest (fun p m => fits p (List.mem_append_right _ m)))

def recover (r : Role) (row : BareRow) : Option Trace :=
  if r.binders.Nodup ∧ r.binders.length = row.arity then
    (fields row.role r.binders r.outputs row.outputs).map (((.role r.spelling),some row.role)::·)
  else none

theorem recover_from_witness {e : Environment} {r : Role} {row : BareRow} (ok : RowWitness e r row) :
    recover r row = some (capture e r) := by
  obtain ⟨noDup,gets,arity,h⟩ := ok
  simp [recover,noDup,arity,fields_from_aligned h,capture,values,queryList,gets,reply]

theorem recover_from_existing_lowerer {e : Environment} {r : Role} {row : BareRow}
    (ok : resolveRole e r = some row) :
    recover r row = some (capture e r) :=
  recover_from_witness ((role_exact ..).mp ok)

theorem recover_replays {e : Environment} {r : Role} {row : BareRow} {t : Trace}
    (found : recover r row = some t) (fits : Matches e t) : resolveRole e r = some row := by
  by_cases shaped : r.binders.Nodup ∧ r.binders.length = row.arity
  · cases h : fields row.role r.binders r.outputs row.outputs with
    | none => simp [recover,shaped,h] at found
    | some tail =>
      have same : (.role r.spelling,some row.role)::tail = t := by
        simpa [recover,shaped,h] using found
      rw [←same,matches_cons] at fits
      exact (role_exact ..).mpr ⟨shaped.1,fits.1,shaped.2,fields_replay h fits.2⟩
  · simp [recover,shaped] at found

end Yulang.GeneralSourceRoleCstReifyRow296
