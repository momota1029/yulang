import Yulang.GeneralDeclarativeI65I74EquivalentObservations473
import Yulang.GeneralDeclarativeI65I74RecordTraversal455
import Yulang.GeneralDeclarativeI65I74RecordEntry412
import Yulang.GeneralDeclarativeWitnessLiteral349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473
open ObservationSyntax471 (Slot Label ReadsDescription readDescription description_exact FieldOrigin)
open GeneralDeclarativeI65 (State)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open WrittenPattern460.PhysicalOrigin (Pose Origin children exact_original_occurrences)
open AuthoredInspectQuery456 (AuthoredQuery compileQuery compile_query_exact)
open RecordTraversal455 (termInspects term_inspects_exact455)
open GeneralDeclarativeInspect321 (Inspects)

/-- Written child selector and its original literal subtree location.
Physical raw keys are separate; a binder does not license a constructor
opening, and this local reader never unfolds a name. -/
structure StepWire where
  action : WrittenPattern460.Address
  written : List Pose

def childSlot : WrittenPattern460.Address → Slot
  | .field label => .field label
  | .tag _ => .variant
  | .arg i => .argument i

def eligible (action : WrittenPattern460.Address) (left right : Label) : Bool :=
  match action,left,right with
  | .field _,.structural (.record _),.structural (.record _) => true
  | .tag k,.structural (.variant a),.structural (.variant b) => (k == a) && (k == b)
  | .arg _,.structural .pair,.structural .pair => true
  | .arg _,.nominal a,.nominal b => a == b
  | _,_,_ => false

def select (b : List (Slot × Expr)) (pick : Slot) : Option (Slot × Expr) :=
  b.find? fun e => e.1 == pick

theorem selected_is_exact {branches : List (Slot × Expr)} {pick : Slot} {slot e}
    (hit : select branches pick = some (slot,e)) :
    (pick,e) ∈ branches := by
  have named : slot = pick := beq_iff_eq.mp
    (List.find?_some (p := fun (p : Slot × Expr) => p.1 == pick) hit)
  exact named ▸ List.mem_of_find?_eq_some hit

structure ReadStep (s : GeneralDeclarativeI65.State) (w : StepWire) (p : Pattern) (query raw : Expr) where
  writtenChild : Pattern
  writtenFrom : WrittenPattern460.PhysicalOrigin.Origin p w.action w.written writtenChild
  childQuery : Expr
  exactCompile : AuthoredQuery s (normalize writtenChild) childQuery
  queryLabel : Label
  queryChildren : List (Slot × Expr)
  exactQuery : ReadsDescription s query queryLabel queryChildren
  actualQueryChild : (childSlot w.action,childQuery) ∈ queryChildren
  rawLabel : Label
  rawChildren : List (Slot × Expr)
  exactRaw : ReadsDescription s raw rawLabel rawChildren
  actualRawChild : Expr
  exactRawChild : (childSlot w.action,actualRawChild) ∈ rawChildren
  pathAllowed : eligible w.action queryLabel rawLabel = true
  childInspected : Inspects childQuery

def readLiteralVisitStep (s : GeneralDeclarativeI65.State) (p : Pattern) (query raw : Expr) (w : StepWire) :
    Option (ReadStep s w p query raw) :=
  let written := WrittenPattern460.PhysicalOrigin.children p w.action
  match move : written.find? (fun x => x.1 == w.written) with
  | none => none
  | some (pos,pattern) =>
    match printed : readDescription s query, actual : readDescription s raw with
    | some (queryLabel,queryChildren),some (rawLabel,rawChildren) =>
      match q : select queryChildren (childSlot w.action), r : select rawChildren (childSlot w.action) with
      | some (_qs,cq),some (_rs,cr) =>
        match compiled : compileQuery s (normalize pattern) with
        | none => none
        | some e =>
          if checked : eqExpr e cq = true ∧ eligible w.action queryLabel rawLabel = true ∧ termInspects cq = true then
            have right : pos = w.written := beq_iff_eq.mp
              (List.find?_some (p := fun p : List Pose × Pattern => p.1 == w.written) move)
            have confirmed := (exact_original_occurrences p w.action pos pattern).mp
              (List.mem_of_find?_eq_some move)
            some ⟨pattern,right ▸ confirmed,cq,(eq_expr ..).mp checked.1 ▸ (compile_query_exact ..).mp compiled,
              queryLabel,queryChildren,description_exact.mp printed,selected_is_exact q,
              rawLabel,rawChildren,description_exact.mp actual,cr,selected_is_exact r,checked.2.1,
              (term_inspects_exact455 _).mp checked.2.2⟩
          else none
      | _,_ => none
    | _,_ => none

inductive Visit (s : GeneralDeclarativeI65.State) : Pattern → Expr → Expr → List StepWire → Pattern → Expr → Expr → Prop where
  | stop : Visit s p query raw [] p query raw
  | walk (a : ReadStep s w p query raw) :
    Visit s a.writtenChild a.childQuery a.actualRawChild tail final finalCode finalRaw →
    Visit s p query raw (w::tail) final finalCode finalRaw

structure ReadVisit (s : GeneralDeclarativeI65.State) (p : Pattern) (q raw : Expr) (path : List StepWire) where
  pattern : Pattern
  query : Expr
  term : Expr
  exact : Visit s p q raw path pattern query term

def readLiteralVisit (s : GeneralDeclarativeI65.State) (p : Pattern) (q raw : Expr) (path : List StepWire) :
    Option (ReadVisit s p q raw path) :=
  match path with
  | [] => some ⟨p,q,raw,.stop⟩
  | first::rest => do
    let a ← readLiteralVisitStep s p q raw first
    let b ← readLiteralVisit s a.writtenChild a.childQuery a.actualRawChild rest
    pure ⟨b.pattern,b.query,b.term,.walk a b.exact⟩

open WrittenPattern460.PhysicalOrigin (atSource literal_occurrence sourceStep)
open ObservationSyntax471 (descend)

theorem written_pose_append_is_exact (p : Pattern) (a b : List Pose) :
    atSource p (a ++ b) = (atSource p a).bind fun target => atSource target b := by
  induction a generalizing p with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.cons_append,atSource]
    cases hit : sourceStep p first with
    | none => simp [Option.bind]
    | some target => simpa [bind,Option.bind] using ih target

theorem exact_original_ast_of_finite_literal_path {s p q raw path last lastQuery lastRaw}
    (arrived : Visit s p q raw path last lastQuery lastRaw) :
    atSource p (path.flatMap StepWire.written) = some last := by
  induction arrived with
  | stop => rfl
  | walk step _ ih =>
    rw [List.flatMap_cons,written_pose_append_is_exact,literal_occurrence step.writtenFrom]
    exact ih

theorem exact_compiler_code_at_nonempty_end_of_finite_original_literal_path
    {s p q raw path out code finish} (entered : Visit s p q raw path out code finish)
    (initial : AuthoredQuery s (normalize p) q) :
    AuthoredQuery s (normalize out) code := by
  induction entered with
  | stop => exact initial
  | walk step _ ih => exact ih step.exactCompile

theorem nonempty_literal_path_ends_at_a_nonvariable_compiler_query
    {s p q raw path out code finish} (entered : Visit s p q raw path out code finish)
    (nonempty : path ≠ []) : Inspects code := by
  induction entered with
  | stop => exact (nonempty rfl).elim
  | @walk w p q raw rest result final term step walked ih =>
    cases rest with
    | nil => cases walked; exact step.childInspected
    | cons one later => exact ih (by simp)

end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473

namespace Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarationPatterns (Pattern)
open WrittenPattern460.PhysicalOrigin (Pose atSource literal_occurrence exact_original_occurrences)

theorem selected_child_at_exact_unique_slot {cs : List (Slot × Expr)} {key e}
    (unique : (cs.map Prod.fst).Nodup) (hit : (key,e) ∈ cs) :
    cs.find? (fun c => c.1 == key) = some (key,e) := by
  induction cs with
  | nil => cases hit
  | cons first rest ih =>
    obtain ⟨orig,value⟩ := first
    rcases List.mem_cons.mp hit with eq|tail
    · cases eq
      simp
    · have no : orig ≠ key := by
        intro same
        subst orig
        exact (List.nodup_cons.mp unique).1 (List.mem_map.mpr ⟨_,tail,rfl⟩)
      simp [no]
      exact ih (List.nodup_cons.mp unique).2 tail

theorem raw_lexical_descent_preserves_the_exact_prefix
    (s : GeneralDeclarativeI65.State) (e : Expr) (left right : List Slot) :
    descend s e (left ++ right) = (descend s e left).bind fun x => descend s x right := by
  induction left generalizing e with
  | nil => rfl
  | cons step rest ih =>
    simp only [List.cons_append,descend]
    cases eq : readDescription s e with
    | none => simp [bind,Option.bind]
    | some hit =>
      obtain ⟨sig,cs⟩ := hit
      cases sub : cs.find? (fun c => c.1 == step) with
      | none => simp [sub,bind,Option.bind]
      | some out => simpa [sub,bind,Option.bind] using ih out.2

theorem one_step_raw_lexical_position_is_the_actual_selected_operand
    {s : GeneralDeclarativeI65.State} {e label branches path q key child}
    (arrived : descend s e path = some q)
    (described : ReadsDescription s q label branches) (selected : (key,child) ∈ branches) :
    descend s e (path ++ [key]) = some child := by
  rw [raw_lexical_descent_preserves_the_exact_prefix,arrived]
  have found := selected_child_at_exact_unique_slot (no_duplicate_slots_in_a_description described) selected
  simp [descend,description_exact.mpr described,found,bind,Option.bind]

end Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471

namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473
open ObservationSyntax471 (descend description_exact)
theorem exact_raw_lexical_path_after_finite_correspondence
    {s p query raw path out code term} (trace : Visit s p query raw path out code term) :
    descend s raw (path.map (childSlot ∘ StepWire.action)) = some term := by
  induction trace with
  | stop => rfl
  | walk step rest ih =>
    have slot := ObservationSyntax471.selected_child_at_exact_unique_slot
      (ObservationSyntax471.no_duplicate_slots_in_a_description step.exactRaw) step.exactRawChild
    simpa [descend,description_exact.mpr step.exactRaw,slot,bind,Option.bind] using ih
end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473

namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWitnessLiteral349 (eq_expr)
open AuthoredInspectQuery456 (compile_query_exact)
open ObservationSyntax471 (description_exact no_duplicate_slots_in_a_description selected_child_at_exact_unique_slot)
open RecordTraversal455 (term_inspects_exact455)
open WrittenPattern460.PhysicalOrigin (Pose literal_occurrence exact_original_occurrences)

theorem actual_literal_child_index_replays
    {p : Pattern} {action : WrittenPattern460.Address} {poses : List Pose} {t : Pattern}
    (auth : WrittenPattern460.PhysicalOrigin.Origin p action poses t) :
    ((WrittenPattern460.PhysicalOrigin.children p action).find? fun o => o.1 == poses) =
      some (poses,t) := by
  cases got : (WrittenPattern460.PhysicalOrigin.children p action).find? (fun o => o.1 == poses) with
  | none =>
    have found := (exact_original_occurrences ..).mpr auth
    exact ((List.find?_eq_none.mp got) (poses,t) found (by simp)).elim
  | some hit =>
    obtain ⟨path,out⟩ := hit
    have same : path = poses := by simpa using List.find?_some got
    subst path
    have aux : WrittenPattern460.PhysicalOrigin.Origin p action poses out :=
      (exact_original_occurrences ..).mp (List.mem_of_find?_eq_some got)
    have tied : out = t := Option.some.inj ((literal_occurrence aux).symm.trans (literal_occurrence auth))
    subst out
    rfl

theorem independent_step_derivation_replays_its_original_addresses {s w p q raw}
    (a : ReadStep s w p q raw) : readLiteralVisitStep s p q raw w = some a := by
  have written := actual_literal_child_index_replays a.writtenFrom
  have printed := description_exact.mpr a.exactQuery
  have rawShape := description_exact.mpr a.exactRaw
  have gotQ := selected_child_at_exact_unique_slot
    (no_duplicate_slots_in_a_description a.exactQuery) a.actualQueryChild
  have gotR := selected_child_at_exact_unique_slot
    (no_duplicate_slots_in_a_description a.exactRaw) a.exactRawChild
  have compiled := (compile_query_exact ..).mpr a.exactCompile
  unfold readLiteralVisitStep
  dsimp only
  split
  · rename_i missing
    rw [written] at missing
    cases missing
  · rename_i poses child got
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (got.symm.trans written))
    split
    · rename_i ql qs rl rs lhs rhs
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (lhs.symm.trans printed))
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (rhs.symm.trans rawShape))
      split
      · rename_i aq cq ar cr lhs rhs
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (lhs.symm.trans gotQ))
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (rhs.symm.trans gotR))
        split
        · rename_i missing
          rw [compiled] at missing
          cases missing
        · rename_i value found
          have eq : value = a.childQuery := Option.some.inj (found.symm.trans compiled)
          subst value
          rw [dite_eq_left ⟨(eq_expr ..).mpr rfl,a.pathAllowed,(term_inspects_exact455 _).mpr a.childInspected⟩]
      · rename_i failed
        exact (failed _ _ _ _ gotQ gotR).elim
    · rename_i failed
      exact (failed _ _ _ _ printed rawShape).elim

theorem finite_literal_visit_readback_is_independent {s p q raw path out code term}
    (entered : Visit s p q raw path out code term) :
    readLiteralVisit s p q raw path = some ⟨out,code,term,entered⟩ := by
  induction entered with
  | stop => rfl
  | walk first rest ih =>
    simp [readLiteralVisit,independent_step_derivation_replays_its_original_addresses first,ih,bind,Option.bind]

end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473
