import Yulang.GeneralGeneratedDictionaryRun299

namespace Yulang.GeneralOrderedDictionaryCheck309
open CommonRoleOutermostResolver (All₂ Dictionary)
open GeneralGeneratedDictionaryRun299 (Read run run_exact)

inductive Error where
  | fuel (cursor : Nat)
  | missing (cursor : Nat)
  | wrongKey (cursor wanted got : Nat)
  | wrongArity (cursor wanted got : Nat)
  | child (cursor ordinal : Nat) (error : Error)
  deriving Repr, DecidableEq

def ordered (check : Nat → Dictionary → Except Error Unit) (parent : Nat) :
    Nat → List Nat → List Dictionary → Except Error Unit
  | _,[],[] => .ok ()
  | pos,i::is,d::ds =>
    match check i d with
    | .error fault => .error (.child parent pos fault)
    | .ok _ => ordered check parent (pos+1) is ds
  | _,is,ds => .error (.wrongArity parent is.length ds.length)

def validate (read : Read) : Nat → Nat → Dictionary → Except Error Unit
  | 0,i,_ => .error (.fuel i)
  | n+1,i,.node key sub =>
    match read i with
    | none => .error (.missing i)
    | some r =>
      if key ≠ r.key then .error (.wrongKey i r.key key)
      else if sub.length ≠ r.children.length then .error (.wrongArity i r.children.length sub.length)
      else ordered (validate read n) i 0 r.children sub

theorem ordered_exact (check : Nat → Dictionary → Except Error Unit) (parent pos : Nat)
    (is : List Nat) (ds : List Dictionary) :
    ordered check parent pos is ds = .ok () ↔
    All₂ (fun i d => check i d = .ok ()) is ds := by
  induction is generalizing pos ds with
  | nil =>
    cases ds with
    | nil => exact ⟨fun _ => .nil,fun _ => rfl⟩
    | cons =>
      constructor <;> intro h <;> cases h
  | cons i is ih =>
    cases ds with
    | nil => constructor <;> intro h <;> cases h
    | cons d ds =>
      constructor
      · intro h
        cases took : check i d with
        | error fault => simp [ordered,took] at h
        | ok yes =>
          cases yes
          exact .cons took ((ih _ _).mp (by simpa only [ordered,took] using h))
      · intro h
        cases h with
        | cons head tail =>
          simpa only [ordered,head] using (ih (pos+1) ds).mpr tail

theorem map_relation {A B : Type} {P Q : A → B → Prop}
    (agree : ∀ a b, P a b ↔ Q a b) {is : List A} {ds : List B} :
    All₂ P is ds ↔ All₂ Q is ds := by
  have move {R S : A → B → Prop} (reach : ∀ a b, R a b → S a b) :
      ∀ {as : List A} {bs : List B}, All₂ R as bs → All₂ S as bs := by
    intro _ _ derivation
    induction derivation with
    | nil => exact .nil
    | cons h _ ih => exact .cons (reach _ _ h) ih
  exact ⟨move (fun a b => (agree a b).mp),move (fun a b => (agree a b).mpr)⟩

theorem length_equal {A B : Type} {P : A → B → Prop} {is ds}
    (link : @All₂ A B P is ds) : is.length = ds.length := by
  induction link with
  | nil => rfl
  | cons _ _ ih => exact congrArg (·+1) ih

/-- A separately supplied ordered payload is accepted precisely when the
reference reader produces that same payload. No guessed leaf is accepted. -/
theorem exact (read : Read) (fuel i : Nat) (d : Dictionary) :
    validate read fuel i d = .ok () ↔ run read fuel i = some d := by
  induction fuel generalizing i d with
  | zero => simp [validate,run]
  | succ n ih =>
    cases d with
    | node k ds =>
      constructor
      · intro h
        cases hit : read i with
        | none => simp [validate,hit] at h
        | some r =>
          by_cases key : k = r.key
          · by_cases len : ds.length = r.children.length
            · have orderedOk : ordered (validate read n) i 0 r.children ds = .ok () := by
                simpa [validate,hit,key,len] using h
              apply (run_exact ..).mpr
              exact ⟨r,ds,hit,
                (map_relation ih).mp ((ordered_exact ..).mp orderedOk),congrArg (fun x => Dictionary.node x ds) key⟩
            · simp [validate,hit,key,len] at h
          · simp [validate,hit,key] at h
      · intro h
        obtain ⟨r,sub,recorded,below,equal⟩ := (run_exact ..).mp h
        cases equal
        have size := length_equal below
        have checks := (map_relation ih).mpr below
        simpa [validate,recorded,size] using (ordered_exact (validate read n) i 0 r.children ds).mpr checks

end Yulang.GeneralOrderedDictionaryCheck309
