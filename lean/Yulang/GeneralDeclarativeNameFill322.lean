import Yulang.GeneralDeclarativeNameLookup322
import Yulang.GeneralDeclarativeExistingClause322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNameFill322
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeNameLookup322 (find exact_found found_if)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeExistingClause322 (Refers NamedRefers)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalMaterialization (Mode)
open GeneralSourceState (Output)
open CommonRoleOutermostResolver (All₂)

structure Pool where
  lower : List Nat
  actual : List Nat
  upper : List Nat

def Pool.atMode (p : Pool) : Mode → List Nat
  | .lower => p.lower
  | .actual => p.actual
  | .upper => p.upper

def Covered (s : State) (names : List Nat) (code : Expr) : Prop :=
  ∃ name ∈ names, Derives s (.variable name) code

def CoversArg (s : State) (capture : Nat → Capture) (code : Expr) (pool : Pool) : Prop :=
  ∀ m : Mode, Covered s (pool.atMode m) (logical capture m code)

noncomputable def input (s : State) (capture : Nat → Capture) (code : Expr) (pool : Pool) : Option Capture := do
  let low ← find s pool.lower (logical capture .lower code)
  let actual ← find s pool.actual (logical capture .actual code)
  let high ← find s pool.upper (logical capture .upper code)
  pure ⟨low,actual,high⟩

noncomputable def associated (s : State) (capture : Nat → Capture) (code : Nat × Expr)
    (pool : List Nat) : Option Output := do
  let target ← find s pool (logical capture .actual code.2)
  pure ⟨code.1,target⟩

theorem input_build {s : State} {capture : Nat → Capture} {code : Expr} {pool : Pool}
    (witness : CoversArg s capture code pool) :
    ∃ arg, input s capture code pool = some arg ∧ Refers s capture code arg ∧
      arg.lower ∈ pool.lower ∧ arg.center ∈ pool.actual ∧ arg.upper ∈ pool.upper := by
  obtain ⟨lo,hlo⟩ := found_if (witness .lower)
  obtain ⟨c,hc⟩ := found_if (witness .actual)
  obtain ⟨hi,hhi⟩ := found_if (witness .upper)
  simp only [Pool.atMode] at hlo hc hhi
  exact ⟨⟨lo,c,hi⟩,by simp [input,hlo,hc,hhi],
    ⟨(exact_found hlo).2,(exact_found hc).2,(exact_found hhi).2⟩,
    (exact_found hlo).1,(exact_found hc).1,(exact_found hhi).1⟩

theorem output_build {s : State} {capture : Nat → Capture} {code : Nat × Expr} {pool : List Nat}
    (witness : Covered s pool (logical capture .actual code.2)) :
    ∃ out, associated s capture code pool = some out ∧ NamedRefers s capture code out ∧
      out.target ∈ pool := by
  obtain ⟨target,found⟩ := found_if witness
  exact ⟨⟨code.1,target⟩,by simp [associated,found],⟨rfl,(exact_found found).2⟩,(exact_found found).1⟩

noncomputable def zipNames (f : α → β → Option γ) : List α → List β → Option (List γ)
  | [],[] => some []
  | a::as,b::bs => do
    let first ← f a b
    let rest ← zipNames f as bs
    pure (first::rest)
  | _,_ => none

theorem zip_build {f : α → β → Option γ} {witness : α → β → Prop} {facts : α → β → γ → Prop}
    (row : ∀ a b, witness a b → ∃ c, f a b = some c ∧ facts a b c)
    (covers : All₂ witness aa bb) :
    ∃ cs, zipNames f aa bb = some cs ∧ All₂ (fun a c => ∃ b, facts a b c) aa cs := by
  induction covers with
  | nil => exact ⟨[],rfl,.nil⟩
  | cons first rest ih =>
    obtain ⟨v,r,ok⟩ := row _ _ first
    obtain ⟨vs,rs,all⟩ := ih
    exact ⟨v::vs,by simp [zipNames,r,rs],.cons ⟨_,ok⟩ all⟩

end Yulang.GeneralDeclarativeNameFill322
