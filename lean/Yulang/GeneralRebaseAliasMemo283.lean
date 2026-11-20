import Yulang.GeneralRebaseOneSource283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseAliasMemo283
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralPresenceOrderedBlock247 (solve put SafeOrder)
open GeneralRebaseOneSource283 (One one reflects accepts meaning)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (model Equivalent subtype_refl)
open GeneralPresenceModelCongruence245 (Compatible tyEq_refl)
open GeneralRebaseLoopBase282 (equiv_trans)

abbrev Aliases := List (Nat × Nat)

def root (cache : Aliases) (n : Nat) : Nat :=
  ((cache.find? (fun x => x.1 == n)).map Prod.snd).getD n

def cache : List (Entry Nat) → Aliases → Option Aliases
  | [], prior => some prior
  | row :: rest, prior => do
    let read ← one row.2
    cache rest ((row.1,root prior read) :: prior)

def assignment (base : Assignment) (memo : Aliases) (n : Nat) := ((base (root memo n)).1,(base n).2)

theorem lookup_cons (memo : Aliases) (target value n : Nat) :
    root ((target,value)::memo) n = if target = n then value else root memo n := by
  by_cases hit : target = n
  · simp [root,hit]
  · simp [root,hit]

theorem exists_cache (entries : List (Entry Nat)) (prior : Aliases)
    (unary : ∀ row ∈ entries, ∃ n, One row.2 n) : ∃ memo, cache entries prior = some memo := by
  induction entries generalizing prior with
  | nil => exact ⟨prior,rfl⟩
  | cons row rest ih =>
    obtain ⟨read,shape⟩ := unary row List.mem_cons_self
    obtain ⟨memo,found⟩ := ih ((row.1,root prior read) :: prior)
      (fun e m => unary e (List.mem_cons_of_mem _ m))
    exact ⟨memo,by simp [cache,accepts shape,found]⟩

theorem update_agrees (base work : Assignment) (prior : Aliases)
    (compatible : Compatible model (assignment base prior) work)
    (row : Entry Nat) (n : Nat) (form : One row.2 n) :
    Compatible model (assignment base ((row.1,root prior n)::prior))
      (put model work row.1 (row.2.eval model work)) := by
  intro i
  refine ⟨?_,(compatible i).2.trans (GeneralPresenceOrderedBlock247.put_rows model _ _ _ _).symm⟩
  have map := lookup_cons prior row.1 (root prior n) i
  by_cases hit : row.1 = i
  · subst i
    have h : Equivalent (work n).1 (row.2.eval model work) :=
      ⟨(meaning form work).2,(meaning form work).1⟩
    have eq := equiv_trans (compatible n).1 h
    change Equivalent (base (root ((row.1,root prior n)::prior) row.1)).1
      (put model work row.1 (row.2.eval model work) row.1).1
    rw [map]
    simpa [put,assignment] using eq
  · change Equivalent (base (root ((row.1,root prior n)::prior) i)).1
      (put model work row.1 (row.2.eval model work) i).1
    rw [map,ite_eq_right hit,GeneralPresenceOrderedBlock247.put_outside model _ _ _ _ hit]
    exact (compatible i).1

theorem application (defs : List (Entry Nat)) (base work : Assignment) (start done : Aliases)
    (same : Compatible model (assignment base start) work) (made : cache defs start = some done) :
    Compatible model (assignment base done) (solve model defs work) := by
  induction defs generalizing work start with
  | nil =>
    have eq : start = done := Option.some.inj made
    subst done; exact same
  | cons row rest ih =>
    cases read : one row.2 with
    | none => simp [cache,read] at made
    | some n =>
      have next := update_agrees base work start same row n (reflects _ n read)
      apply ih _ _ next
      simpa [cache,read] using made

theorem exact (defs : List (Entry Nat)) (base : Assignment) (memo : Aliases)
    (made : cache defs [] = some memo) :
    Compatible model (assignment base memo) (solve model defs base) :=
  application defs base base [] memo (fun _ => ⟨tyEq_refl GeneralPresenceCommonLaws245.common_laws _,rfl⟩) made

theorem no_write (defs : List (Entry Nat)) (memo solved : Aliases) (n : Nat)
    (absent : ∀ row ∈ defs, row.1 ≠ n) (made : cache defs memo = some solved) :
    root solved n = root memo n := by
  induction defs generalizing memo with
  | nil =>
    have eq : memo = solved := Option.some.inj made
    subst solved; rfl
  | cons row rest ih =>
    cases found : one row.2 with
    | none => simp [cache,found] at made
    | some read =>
      have run : cache rest ((row.1,root memo read)::memo) = some solved := by simpa [cache,found] using made
      rw [ih _ (fun e m => absent e (List.mem_cons_of_mem _ m)) run,lookup_cons,
        ite_eq_right (absent row List.mem_cons_self)]

theorem equation (defs : List (Entry Nat)) (memo solved : Aliases) (order : SafeOrder defs)
    (made : cache defs memo = some solved) (row : Entry Nat) (member : row ∈ defs)
    (read : Nat) (valid : One row.2 read) :
    root solved row.1 = root solved read := by
  induction defs generalizing memo with
  | nil => cases member
  | cons head rest ih =>
    cases evidence : one head.2 with
    | none => simp [cache,evidence] at made
    | some source =>
      have run : cache rest ((head.1,root memo source)::memo) = some solved := by
        simpa [cache,evidence] using made
      obtain ⟨self,unique,clean,safeTail⟩ := order
      rcases List.mem_cons.mp member with rfl|inside
      · have eq := Option.some.inj ((accepts valid).symm.trans evidence)
        subst source
        have diff : row.1 ≠ read := by
          intro hit
          exact self ((GeneralRebaseOneSource283.reads_exact valid).mpr hit)
        have noRead : ∀ entry ∈ rest, entry.1 ≠ read := by
          intro entry present eq
          exact clean entry present ((GeneralRebaseOneSource283.reads_exact valid).mpr eq)
        rw [no_write _ _ _ _ unique run,no_write _ _ _ _ noRead run,lookup_cons,lookup_cons,
          ite_eq_left rfl,ite_eq_right diff]
      · exact ih _ safeTail run inside

theorem define_or_free (defs : List (Entry Nat)) (memo : Aliases) (n : Nat)
    (made : cache defs [] = some memo)
    (notDefined : ∀ row ∈ defs, row.1 ≠ n) : root memo n = n :=
  no_write defs [] memo n notDefined made

end Yulang.GeneralRebaseAliasMemo283
