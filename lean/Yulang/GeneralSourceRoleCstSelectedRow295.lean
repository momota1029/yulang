import Yulang.GeneralSourceRoleCstSelectedControl295

/-! Success produces exactly one row, with no implicit aggregation of sibling
declarations. The name and arity are from the selected unresolved head
and its designated lookup environment, not from an occurrence integer. -/
namespace Yulang.GeneralSourceRoleCstSelectedRow295
open GeneralSourceRoleExport292 (Aligned)
open GeneralSourceRoleTrack292 (Tracked forget runTracked)
open GeneralSourceRoleHeadShape292 (HeadShape)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceMetadataRoles291 (RoleSource RoleRow Valid)
open GeneralSourceMetadataBareRole291 (forgetRow)
open GeneralSourceRoleCstSelectedCompile295 (Boundary compile compile_origin)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstWire293 (Wire)

theorem aligned_singleton {A B : Type} {rel : A → B → Prop} {item : A} {items : List B}
    (ok : Aligned rel [item] items) : ∃ other, items = [other] ∧ rel item other := by
  cases ok with
  | cons first tail =>
    cases tail
    exact ⟨_,rfl,first⟩

theorem map_singleton {A B : Type} {f : A → B} {xs : List A} {y : B}
    (h : xs.map f = [y]) : ∃ x, xs = [x] ∧ f x = y := by
  cases xs with
  | nil => cases h
  | cons x xs =>
    cases xs with
    | nil => exact ⟨x,rfl,List.cons.inj h |>.1⟩
    | cons z zs => cases h

theorem tracked_single_row {S H : Type} (env : S → Environment) (fallback : Nat)
    (p : Tracked S H) (table : RoleSource) (ok : runTracked env fallback [p] = some table) :
    table.fallbackArity = fallback ∧ Valid table ∧
      ∃ (r : RoleRow) (n : String) (params : List String), table.rows = [r] ∧
        HeadShape p.head n params ∧ (env p.scope).role n = some r.role ∧ r.arity = params.length := by
  obtain ⟨packets,prepared,built⟩ :=
    (GeneralSourceRoleHeadPacketRun292.run_exact env fallback [forget p] table).mp ok
  obtain ⟨packet,rfl,ready⟩ := aligned_singleton prepared
  obtain ⟨entries,projected,result⟩ := (GeneralSourceRoleScopedShell292.run_exact ..).mp built
  obtain ⟨entry,rfl,clear⟩ := aligned_singleton projected
  obtain ⟨stored,rows,validated⟩ := (GeneralSourceRoleScopedExport292.lower_exact ..).mp result
  obtain ⟨bare,one,rowWitness⟩ := aligned_singleton rows
  obtain ⟨r,single,rfl⟩ := map_singleton one
  obtain ⟨scopeEq,_,headWitness⟩ := ready
  obtain ⟨scopeLink,s,⟨srcName,srcArgs,_⟩,symbol,params,_⟩ := clear
  obtain ⟨_,key,arity,_⟩ := rowWitness
  change entry.role.binders.length = r.arity at arity
  change (env entry.scope).role entry.role.spelling = some r.role at key
  rw [←scopeLink,scopeEq,←symbol,←srcName] at key
  rw [←params,←srcArgs] at arity
  exact ⟨stored,validated,r,_,_,single,headWitness,key,arity.symm⟩

theorem compile_single_row {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (packet : Boundary S B) (env : S → Environment) (fallback : Nat)
    (out : RoleSource) (h : compile policy scope w brand a packet env fallback = some out) :
    out.fallbackArity = fallback ∧ Valid out ∧
    ∃ (p : Tracked S (Address B)) (row : RoleRow) (name : String) (args : List String), p.atRole = packet.selected.address ∧ out.rows = [row] ∧
      HeadShape p.head name args ∧ (env p.scope).role name = some row.role ∧
      row.arity = args.length := by
  obtain ⟨_,site,p,selected,_,ready⟩ := compile_origin policy scope w brand a packet env fallback out h
  obtain ⟨fb,valid,r,n,args,row,shape,key,arity⟩ := tracked_single_row env fallback p out ready
  exact ⟨fb,valid,p,r,n,args,selected.trans site,row,shape,key,arity⟩

end Yulang.GeneralSourceRoleCstSelectedRow295
