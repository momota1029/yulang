import Yulang.GeneralDeclarativeNormalized320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 13000
set_option maxHeartbeats 3300000
namespace Yulang.GeneralDeclarativeLinear320
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Constructors Pattern)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarativeHead320 (State Read)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds HeadArg)
open GeneralDeclarativeBounds319 (Bound)
open CommonRoleOutermostResolver (All₂)

def table (names : List Nat) (args : List Capture) : List (Nat × Capture) :=
  names.zip args

def captures : List (Nat × Capture) → Nat → Capture
  | [],_ => ⟨0,0,0⟩
  | (key,entry)::rest,name => if key = name then entry else captures rest name

theorem lookup {entries : List (Nat × Capture)} {n : Nat} {arg : Capture}
    (unique : (entries.map Prod.fst).Nodup) (used : (n,arg) ∈ entries) :
    captures entries n = arg := by
  induction entries with
  | nil => cases used
  | cons first rest ih =>
    obtain ⟨key,entry⟩ := first
    rcases List.mem_cons.mp used with eq|tail
    · cases eq
      simp [captures]
    · have unequal : key ≠ n := by
        intro same
        exact (List.nodup_cons.mp unique).1 (same.symm ▸ List.mem_map.mpr ⟨(n,arg),tail,rfl⟩)
      simp only [captures,unequal,ite_false]
      exact ih (List.nodup_cons.mp unique).2 tail

theorem keys {names : List Nat} {args : List Capture} (length : names.length = args.length) :
    (table names args).map Prod.fst = names :=
  List.map_fst_zip (Nat.le_of_eq length)

theorem argument_mem {names : List Nat} {args : List Capture} {n : Nat} {arg : Capture}
    (present : (n,arg) ∈ table names args) : arg ∈ args := by
  obtain ⟨i,bounds,atI⟩ := List.mem_iff_getElem.mp present
  change (names.zip args)[i] = (n,arg) at atI
  have iArgs : i < args.length := by
    rw [table,List.length_zip] at bounds
    omega
  have iNames : i < names.length := by rw [table,List.length_zip] at bounds; omega
  rw [List.getElem_zip] at atI
  have eq : args[i] = arg := congrArg Prod.snd atI
  exact eq ▸ List.getElem_mem iArgs

theorem table_order {names : List Nat} {args : List Capture} (length : names.length = args.length) :
    All₂ (fun (arg : Capture) (n : Nat) => (n,arg) ∈ table names args) args names := by
  induction names generalizing args with
  | nil =>
    have none : args = [] := List.length_eq_zero_iff.mp length.symm
    cases none
    exact .nil
  | cons name more ih =>
    cases args with
    | nil => cases length
    | cons arg args =>
      have tail : more.length = args.length := Nat.succ.inj length
      have aligned := ih tail
      refine All₂.cons (relation := fun a n => (n,a) ∈ table (name :: more) (arg :: args)) List.mem_cons_self ?_
      exact GeneralDeclarativeNormalized320.ordered_map aligned
        (fun _ _ _ _ there => List.mem_cons_of_mem _ there)

theorem map_right {p : α → γ → Prop} {f : β → γ} {xs : List α} {ys : List β}
    (h : All₂ (fun a b => p a (f b)) xs ys) : All₂ p xs (ys.map f) := by
  induction h with
  | nil => exact .nil
  | cons first _ ih => exact .cons first ih

/-- A linear variable head actually produces its all-model read certificate
from the ordered centers. There is no match witness or substitution premise. -/
theorem produce {s : State} {c : Constructors} {interp : Interpretation}
    {names : List Nat} {args : List Capture}
    (unique : names.Nodup) (length : names.length = args.length)
    (bounded : ∀ arg ∈ args, Bounds s arg) :
    (∀ name ∈ names, Bounds s (captures (table names args) name)) ∧
    All₂ (HeadArg s c interp (captures (table names args))) args (names.map Pattern.var) := by
  have tableUnique : ((table names args).map Prod.fst).Nodup := (keys length).symm ▸ unique
  constructor
  · intro name known
    rw [← keys length] at known
    obtain ⟨entry,present,equal⟩ := List.mem_map.mp known
    rcases entry with ⟨n,arg⟩
    change n = name at equal
    subst n
    rw [lookup tableUnique present]
    exact bounded arg (argument_mem present)
  · have aligned := table_order length
    have h : All₂ (fun arg name =>
        HeadArg s c interp (captures (table names args)) arg (.var name)) args names :=
      GeneralDeclarativeNormalized320.ordered_map aligned (fun arg listed name _ atEntry => by
        refine ⟨bounded arg listed,.variable name,rfl,.capture ?_ ?_⟩ <;>
          rw [GeneralDeclarativeHead320.byMode,lookup tableUnique atEntry] <;> exact .refl _)
    exact map_right h

end Yulang.GeneralDeclarativeLinear320
