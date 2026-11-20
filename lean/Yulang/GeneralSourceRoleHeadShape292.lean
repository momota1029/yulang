import Yulang.GeneralSourceRoleArityRead292

/-! A conservative check for a symbolic head which has already been walked
by the parser owner. The real TypeExpression admits strictly more syntax.
Unrecognized application arguments are not removed to infer an arity. -/
namespace Yulang.GeneralSourceRoleHeadShape292
open GeneralSourceRoleChildCoverage292 (Child)
open GeneralSourceRoleCoveredShell292 (Inventory)
open GeneralSourceRoleScopedShell292 (Packet)
open GeneralSourceRoleExport292 (Aligned collect collect_exact)

inductive Primary where
  | simple (spelling : String)
  | other
  | recovered
  deriving DecidableEq, Repr

inductive Argument where
  | binder (spelling : String)
  | other
  | recovered
  deriving DecidableEq, Repr

structure Head where
  primary : Primary
  arguments : List Argument
  clean : Bool
  deriving DecidableEq, Repr

def readArgument : Argument → Option String
  | .binder s => some s
  | _ => none

theorem arg_exact (a : Argument) (s : String) : readArgument a = some s ↔ a = .binder s := by
  cases a <;> simp [readArgument]

def readHead (h : Head) : Option (String × List String) :=
  match h with
  | ⟨.simple name,arguments,true⟩ => (collect readArgument arguments).map (name, ·)
  | _ => none

def HeadShape (h : Head) (name : String) (parameters : List String) : Prop :=
  h.primary = .simple name ∧ h.clean = true ∧
    Aligned (fun a s => a = .binder s) h.arguments parameters

theorem head_exact (h : Head) (name : String) (params : List String) :
    readHead h = some (name,params) ↔ HeadShape h name params := by
  rcases h with ⟨tok,args,clean⟩
  change readHead ⟨tok,args,clean⟩ = some (name,params) ↔
    tok = .simple name ∧ clean = true ∧ Aligned (fun a s => a = .binder s) args params
  rw [←collect_exact _ _ arg_exact]
  cases tok <;> cases clean <;> cases h : collect readArgument args <;>
    simp [readHead,h]

theorem args_length (head : Head) (name : String) (params : List String)
    (h : readHead head = some (name,params)) : params.length = head.arguments.length := by
  have checked := ((head_exact ..).mp h).2.2
  clear h
  generalize head.arguments = args at checked ⊢
  induction checked with
  | nil => rfl
  | cons _ _ ih => simp [ih]

def packet {Scope : Type} (scope : Scope) (head : Head) (children : List Child) :
    Option (Packet Scope) :=
  (readHead head).map fun parsed => ⟨scope,⟨parsed.1,parsed.2,children⟩⟩

theorem packet_exact {Scope : Type} (scope : Scope) (head : Head) (children : List Child)
    (p : Packet Scope) :
    packet scope head children = some p ↔ p.scope = scope ∧ p.source.directChildren = children ∧
      HeadShape head p.source.name p.source.parameters := by
  rcases p with ⟨pScope,⟨name,params,body⟩⟩
  unfold packet
  change Option.map _ (readHead head) = some (⟨pScope,⟨name,params,body⟩⟩ : Packet Scope) ↔
    pScope = scope ∧ body = children ∧ HeadShape head name params
  rw [←head_exact]
  cases found : readHead head with
  | none => simp
  | some v =>
    rcases v with ⟨n,xs⟩
    simp [Packet.mk.injEq,Inventory.mk.injEq, and_assoc, and_comm, eq_comm]

theorem structural_head_control :
    readHead ⟨.simple "Index",[.binder "'container",.binder "'key"],true⟩ =
      some ("Index",["'container","'key"]) ∧
    readHead ⟨.simple "F",[.other,.binder "'t"],true⟩ = none ∧
    readHead ⟨.simple "F",[.recovered,.binder "'t"],false⟩ = none := by decide

#guard (readHead ⟨.simple "Index",[.binder "'container",.binder "'key"],true⟩).isSome
#guard (readHead ⟨.simple "F",[.other,.binder "'t"],true⟩).isNone

end Yulang.GeneralSourceRoleHeadShape292
