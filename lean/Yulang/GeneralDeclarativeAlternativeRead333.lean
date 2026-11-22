import Yulang.GeneralDeclarativeAlternativeSpine333
import Yulang.GeneralDeclarativeNestedDecode332

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAlternativeRead333
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeAlternativeView333 (Offer Index)
open GeneralDeclarativeAlternativeSpine333 (literals)
open GeneralDeclarativeNestedTail332 (peel exact_peel)
open GeneralDeclarativeNestedRun332 (tagId tagId_exact)
open GeneralDeclarativeInlineTrace331 (Read Args Fields TailCode)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeOrderedRecord326 (order)
open GeneralDeclarativeRecordMaterial330 (tailExpr)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralNominalMaterialization (Mode)
open CommonRoleCanonicalRows (Row normalize)

abbrev Result (s : State) (mode : Mode) (raw target : Expr) :=
  { sites : List Occurrence // Read s mode raw target sites }
abbrev ArgResult (s : State) (mode : Mode) (raw target : List Expr) :=
  { sites : List Occurrence // Args s mode raw target sites }
abbrev FieldResult (s : State) (mode : Mode) (raw target : Row Expr) :=
  { sites : List Occurrence // Fields s mode raw target sites }

abbrev Reader (s : State) := ∀ mode raw target, List (Result s mode raw target)
abbrev ArgReader (s : State) := ∀ mode raw target, List (ArgResult s mode raw target)
abbrev FieldReader (s : State) := ∀ mode raw target, List (FieldResult s mode raw target)

def tailOK (e : Expr) : Option (PLift (TailCode e)) :=
  match e with
  | .variable _ => some ⟨.binder⟩
  | .primitive .emptyRecord [] => some ⟨.width⟩
  | .primitive .exactEmpty [] => some ⟨.exactEnd⟩
  | _ => none

def structured (src : Index s) (fuel : Nat) (next : Reader s) (args : ArgReader s)
    (fields : FieldReader s) (mode : Mode) : (raw target : Expr) → List (Result s mode raw target)
  | raw,.variable b => [⟨[⟨b,mode,raw⟩],.capture⟩]
  | .primitive observed raw,.primitive expected target =>
    if eq : tagId observed = tagId expected then
      (args mode raw target).map fun found =>
        ⟨found.val,by cases tagId_exact eq; exact .primitive found.property⟩
    else []
  | .nominal observed raw,.nominal expected target =>
    if eq : observed = expected then
      (args .actual raw target).map fun found =>
        ⟨found.val,by cases eq; exact .nominal found.property⟩
    else []
  | .variant observed raw,.variant expected target =>
    if eq : observed = expected then
      (next mode raw target).map fun found =>
        ⟨found.val,by cases eq; exact .variant found.property⟩
    else []
  | .join r x,.join t y =>
    (next mode r t).flatMap fun a =>
      (next mode x y).map fun b => ⟨a.val++b.val,.join a.property b.property⟩
  | raw,.record k f rest =>
    let target := Expr.record k f rest
    let planned := peel target
    let keys := planned.1.map Prod.fst
    if good : keys.Nodup ∧ keys ≠ [] then
      match tailOK planned.2 with
      | none => []
      | some tail =>
        (literals src fuel raw).flatMap fun literal =>
          match showOrder : order (normalize literal.val.1) keys with
          | none => []
          | some picked =>
            (fields mode picked planned.1).flatMap fun xs =>
              (next mode (tailExpr literal.val.1 keys literal.val.2) planned.2).map fun ys =>
                ⟨xs.val++ys.val,by
                  change Read s mode raw target _
                  rw [← exact_peel target]
                  exact .record literal.property good.1 good.2 showOrder
                    xs.property tail.down ys.property⟩
    else []
  | _,_ => []

def nonBinder : Expr → Bool
  | .variable _ => false
  | _ => true

theorem nonBinder_valid (seen : nonBinder expr = true) : ∀ n, expr ≠ .variable n := by
  intro n h
  cases h
  cases seen

theorem nonBinder_complete (different : ∀ n, expr ≠ .variable n) : nonBinder expr = true := by
  cases expr with
  | «variable» n => exact (different n rfl).elim
  | primitive | nominal | variant | record | join => rfl

def expansions (src : Index s) (next : Reader s) (mode : Mode) :
    (raw target : Expr) → List (Result s mode raw target)
  | .variable n,target =>
    if good : nonBinder target = true then
      (src n).flatMap fun offer =>
        (next mode offer.rhs target).map fun hit =>
          ⟨hit.val,.expose (nonBinder_valid good) offer.linked offer.stored hit.property⟩
    else []
  | _,_ => []

/- Finite search of positive evidence, not an election, stopping
claim or an ordering on candidates. Each syntax occurrence can use a
different available source row. A binder always captures its original
name or term instead of exposing a guessed representative. -/
mutual
def read (src : Index s) : Nat → Reader s
  | 0 => fun _ _ _ => []
  | fuel+1 => fun mode raw target =>
    structured src fuel (read src fuel) (readArgs src fuel) (readFields src fuel) mode raw target ++
      expansions src (read src fuel) mode raw target
def readArgs (src : Index s) : Nat → ArgReader s
  | 0 => fun _ _ _ => []
  | fuel+1 => fun mode raw target =>
    match raw,target with
    | [],[] => [⟨[],.nil⟩]
    | a::as,b::bs =>
      (read src fuel mode a b).flatMap fun first =>
        (readArgs src fuel mode as bs).map fun rest =>
          ⟨first.val++rest.val,.cons first.property rest.property⟩
    | _,_ => []
def readFields (src : Index s) : Nat → FieldReader s
  | 0 => fun _ _ _ => []
  | fuel+1 => fun mode raw target =>
    match raw,target with
    | [],[] => [⟨[],.nil⟩]
    | (k,a)::as,(l,b)::bs =>
      if eq : k = l then
        (read src fuel mode a b).flatMap fun first =>
          (readFields src fuel mode as bs).map fun rest =>
            ⟨first.val++rest.val,by cases eq; exact .cons first.property rest.property⟩
      else []
    | _,_ => []
end

def normalized (src : Index s) (fuel : Nat) (c : GeneralDeclarationPatterns.Constructors)
    (i : GeneralNominalInspection.Interpretation) (mode : Mode) (raw : Expr)
    (pat : GeneralDeclarationPatterns.Pattern) : List (List Occurrence) :=
  match translate c i (GeneralDeclarationPatterns.normalize pat) with
  | none => []
  | some code => (read src fuel mode raw code).map Subtype.val

theorem normalized_sound {s : State} {src : Index s}
    (found : used ∈ normalized src fuel c i mode raw pat) :
    ∃ code, translate c i (GeneralDeclarationPatterns.normalize pat) = some code ∧
      Read s mode raw code used := by
  cases printed : translate c i (GeneralDeclarationPatterns.normalize pat) with
  | none => simp [normalized,printed] at found
  | some code =>
    rw [normalized,printed] at found
    obtain ⟨hit,_,rfl⟩ := List.mem_map.mp found
    exact ⟨code,rfl,hit.property⟩

end Yulang.GeneralDeclarativeAlternativeRead333
