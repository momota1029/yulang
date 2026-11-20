import Yulang.GeneralSourceRoleSpelling292

/-! Source-spelling lowering into the existing, independently validated
finite role table. This is not a parser interface implementation. -/
namespace Yulang.GeneralSourceRoleExport292
open GeneralSourceRoleSpelling292
open GeneralSourceMetadataBareRole291 (BareRow)
open GeneralSourceMetadataBuildRoles291 (Input build)
open GeneralSourceMetadataRoles291 (RoleSource)
open GeneralSourceMetadataExprDomain291 (bind_success two_success)

def resolveOutput (env : Environment) (r : Nat) (binders : List String) (entry : Output) :
    Option (Nat × Option Roles.Term) :=
  (env.output r entry.spelling).bind fun id =>
    (body env binders entry.body).map fun term => (id,term)

def OutputWitness (env : Environment) (r : Nat) (binders : List String) (entry : Output)
    (resolved : Nat × Option Roles.Term) : Prop :=
  env.output r entry.spelling = some resolved.1 ∧ ResolvedBody env binders entry.body resolved.2

theorem output_exact (env : Environment) (r : Nat) (xs : List String) (entry : Output)
    (out : Nat × Option Roles.Term) :
    resolveOutput env r xs entry = some out ↔ OutputWitness env r xs entry out := by
  rcases out with ⟨id,term⟩
  simp only [resolveOutput,OutputWitness]
  cases found : env.output r entry.spelling with
  | none => simp
  | some j =>
    cases lowered : body env xs entry.body with
    | none =>
      constructor
      · simp
      · rintro ⟨_,h⟩
        have e := (body_exact env xs entry.body term).mpr h
        rw [lowered] at e
        cases e
    | some v =>
      simp only [Option.bind_some,Option.map_some,Option.some.injEq,Prod.mk.injEq]
      rw [←body_exact,lowered,Option.some.injEq]

inductive Aligned {A B : Type} (p : A → B → Prop) : List A → List B → Prop
  | nil : Aligned p [] []
  | cons {a b xs ys} : p a b → Aligned p xs ys → Aligned p (a :: xs) (b :: ys)

def collect {A B : Type} (f : A → Option B) : List A → Option (List B)
  | [] => some []
  | x :: xs => (f x).bind fun y => (collect f xs).map (List.cons y)

theorem collect_exact {A B : Type} (f : A → Option B) (p : A → B → Prop)
    (law : ∀ a b, f a = some b ↔ p a b) (xs : List A) (ys : List B) :
    collect f xs = some ys ↔ Aligned p xs ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys
    · exact ⟨fun _ => .nil,fun _ => rfl⟩
    · constructor <;> intro h <;> cases h
  | cons a xs ih =>
    cases ys with
    | nil =>
      constructor
      · intro h
        cases af : f a <;> cases tf : collect f xs <;> simp [collect,af,tf] at h
      · intro h; cases h
    | cons b ys =>
      constructor
      · intro h
        cases af : f a with
        | none => simp [collect,af] at h
        | some x =>
          cases tf : collect f xs with
          | none => simp [collect,af,tf] at h
          | some tail =>
            have eq : x = b ∧ tail = ys := by simpa [collect,af,tf] using h
            rcases eq with ⟨rfl,rfl⟩
            exact .cons ((law ..).mp af) ((ih ..).mp tf)
      · intro h
        cases h with
        | cons front tail => simp [collect,(law ..).mpr front,(ih ..).mpr tail]

def resolveRole (env : Environment) (input : Role) : Option BareRow :=
  if decide input.binders.Nodup then
    (env.role input.spelling).bind fun r =>
      (collect (resolveOutput env r input.binders) input.outputs).map fun outs =>
        ⟨r,input.binders.length,outs⟩
  else none

def RowWitness (env : Environment) (input : Role) (out : BareRow) : Prop :=
  input.binders.Nodup ∧ env.role input.spelling = some out.role ∧
  input.binders.length = out.arity ∧
  Aligned (OutputWitness env out.role input.binders) input.outputs out.outputs

theorem role_exact (env : Environment) (input : Role) (out : BareRow) :
    resolveRole env input = some out ↔ RowWitness env input out := by
  rcases out with ⟨r,arity,outs⟩
  change resolveRole env input = some ⟨r,arity,outs⟩ ↔
    input.binders.Nodup ∧ env.role input.spelling = some r ∧
    input.binders.length = arity ∧
    Aligned (OutputWitness env r input.binders) input.outputs outs
  by_cases d : input.binders.Nodup
  · rw [resolveRole,ite_eq_left (decide_eq_true_eq.mpr d)]
    cases key : env.role input.spelling with
    | none => simp
    | some j =>
      cases e : collect (resolveOutput env j input.binders) input.outputs with
      | none =>
        simp only [Option.bind_some,e,Option.map_none,reduceCtorEq,d,true_and,Option.some.injEq]
        constructor
        · intro h; cases h
        · rintro ⟨rfl,_,related⟩
          have impossible := (collect_exact _ _ (output_exact env j input.binders) _ _).mpr related
          rw [e] at impossible
          cases impossible
      | some got =>
        simp only [Option.bind_some,e,Option.map_some,Option.some.injEq,BareRow.mk.injEq,d,true_and]
        constructor
        · rintro ⟨rfl,h,rfl⟩
          exact ⟨rfl,h,(collect_exact _ _ (output_exact env j input.binders) _ _).mp e⟩
        · rintro ⟨rfl,h,related⟩
          exact ⟨rfl,h,Option.some.inj (e.symm.trans
            ((collect_exact _ _ (output_exact env j input.binders) _ _).mpr related))⟩
  · simp [resolveRole,d]

def lower (env : Environment) (fallback : Nat) (input : List Role) : Option RoleSource :=
  (collect (resolveRole env) input).bind fun rows => build (⟨fallback,rows⟩ : Input)

theorem lower_exact (env : Environment) (fallback : Nat) (input : List Role) (out : RoleSource) :
    lower env fallback input = some out ↔
      out.fallbackArity = fallback ∧
      Aligned (RowWitness env) input (out.rows.map GeneralSourceMetadataBareRole291.forgetRow) ∧
      GeneralSourceMetadataRoles291.Valid out := by
  constructor
  · intro h
    obtain ⟨rows,run,built⟩ := bind_success h
    obtain ⟨equal,valid⟩ := (GeneralSourceMetadataBuildRoles291.build_exact ..).mp built
    cases out
    simp only [GeneralSourceMetadataBuildRoles291.forget,Input.mk.injEq] at equal
    rcases equal with ⟨ha,hr⟩
    exact ⟨ha,hr ▸ (collect_exact _ _ (role_exact env) _ _).mp run,valid⟩
  · rintro ⟨ha,related,valid⟩
    unfold lower
    rw [(collect_exact _ _ (role_exact env) _ _).mpr related]
    exact (GeneralSourceMetadataBuildRoles291.build_exact ..).mpr
      ⟨by cases out; cases ha; rfl,valid⟩

end Yulang.GeneralSourceRoleExport292
