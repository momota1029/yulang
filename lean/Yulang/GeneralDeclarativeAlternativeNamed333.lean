import Yulang.GeneralDeclarativeAlternativeReadComplete333
import Yulang.GeneralDeclarativeTrace321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAlternativeNamed333
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeAlternativeView333 (Index Offer)
open GeneralDeclarativeTrace321 (Trace TraceArgs Occurrence)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalMaterialization (Mode)
open GeneralCandidateInspection (Primitive)
open GeneralDeclarativeNestedRun332 (tagId tagId_exact)

def names : (raw : List Expr) → Option { names : List Nat // names.map Expr.variable = raw }
  | [] => some ⟨[],rfl⟩
  | .variable n::rest =>
    (names rest).map fun later => ⟨n::later.val,by simp only [List.map_cons]; rw [later.property]⟩
  | _ => none

theorem names_render (ns : List Nat) :
    names (ns.map Expr.variable) = some ⟨ns,rfl⟩ := by
  induction ns with
  | nil => rfl
  | cons a as ih =>
    change (names (as.map Expr.variable)).map (fun later => _) = _
    rw [ih]
    rfl

/-- These are the actual saved named RHSs read by the old observer.
Do not canonically subtract labels or force a captured unknown tail
to be an empty/closed record. This is a distinct existing source rule. -/
inductive Shape where
  | primitive (tag : Primitive) (ns : List Nat)
  | nominal (tag : Nat) (ns : List Nat)
  | record (tag first rest : Nat)
  | variant (tag data : Nat)
  | join (one two : Nat)

def Shape.raw : Shape → Expr
  | .primitive tag ns => .primitive tag (ns.map Expr.variable)
  | .nominal tag ns => .nominal tag (ns.map Expr.variable)
  | .record tag first rest => .record tag (.variable first) (.variable rest)
  | .variant tag data => .variant tag (.variable data)
  | .join a b => .join (.variable a) (.variable b)

def classifyRhs : (raw : Expr) → Option { s : Shape // s.raw = raw }
  | .primitive tag raw =>
    (names raw).map fun ns => ⟨.primitive tag ns.val,congrArg (Expr.primitive tag) ns.property⟩
  | .nominal tag raw =>
    (names raw).map fun ns => ⟨.nominal tag ns.val,congrArg (Expr.nominal tag) ns.property⟩
  | .record tag (.variable payload) (.variable rest) => some ⟨.record tag payload rest,rfl⟩
  | .variant tag (.variable data) => some ⟨.variant tag data,rfl⟩
  | .join (.variable a) (.variable b) => some ⟨.join a b,rfl⟩
  | _ => none

theorem source_shape (shape : Shape) : classifyRhs shape.raw = some ⟨shape,rfl⟩ := by
  cases shape with
  | primitive | nominal => simp [Shape.raw,classifyRhs,names_render]
  | variant | record | join => rfl

abbrev Result (s : State) (mode : Mode) (n : Nat) (target : Expr) :=
  { uses : List Occurrence // Trace s mode n target uses }
abbrev Arguments (s : State) (mode : Mode) (ns : List Nat) (target : List Expr) :=
  { uses : List Occurrence // TraceArgs s mode ns target uses }

abbrev Read (s : State) := ∀ mode n target, List (Result s mode n target)
abbrev ReadArgs (s : State) := ∀ mode ns target, List (Arguments s mode ns target)

theorem stored_as (offer : Offer s n) (exact : raw = offer.rhs) :
    (⟨offer.owner,raw⟩ : Equation) ∈ s.equations :=
  exact.symm ▸ offer.stored

def branch (offer : Offer s n) (next : Read s) (args : ReadArgs s) (mode : Mode)
    (shape : Shape) (known : shape.raw = offer.rhs) : (target : Expr) → List (Result s mode n target) :=
  match shape with
  | .primitive observed ns =>
    fun target => match target with
      | .primitive expected patterns =>
        if agree : tagId observed = tagId expected then
          (args mode ns patterns).map fun alt =>
            ⟨alt.val,by
              cases tagId_exact agree
              exact .primitive offer.linked (stored_as offer known) alt.property⟩
        else []
      | _ => []
  | .nominal observed ns =>
    fun target => match target with
      | .nominal expected patterns =>
        if agree : observed = expected then
          (args .actual ns patterns).map fun alt =>
            ⟨alt.val,by cases agree; exact .nominal offer.linked (stored_as offer known) alt.property⟩
        else []
      | _ => []
  | .record observed a b =>
    fun target => match target with
      | .record expected one two =>
        if same : observed = expected then
          (next mode a one).flatMap fun x =>
            (next mode b two).map fun y => ⟨x.val++y.val,by
              cases same
              exact .record offer.linked (stored_as offer known) x.property y.property⟩
        else []
      | _ => []
  | .variant observed a =>
    fun target => match target with
      | .variant expected data =>
        if same : observed = expected then
          (next mode a data).map fun x => ⟨x.val,by
            cases same
            exact .variant offer.linked (stored_as offer known) x.property⟩
        else []
      | _ => []
  | .join a b =>
    fun target => match target with
      | .join one two =>
        (next mode a one).flatMap fun x =>
          (next mode b two).map fun y => ⟨x.val++y.val,.join offer.linked
            (stored_as offer known) x.property y.property⟩
      | _ => []

def alternate (next : Read s) (args : ReadArgs s) (mode : Mode) (target : Expr) (offer : Offer s n) :
    List (Result s mode n target) :=
  match classifyRhs offer.rhs with
  | none => []
  | some shape => branch offer next args mode shape.val shape.property target

mutual
def named (src : Index s) : Nat → Read s
  | 0 => fun _ _ _ => []
  | fuel+1 => fun mode n target =>
    match target with
    | .variable b => [⟨[⟨b,mode,n⟩],.capture⟩]
    | target => (src n).flatMap (alternate (named src fuel) (namedArgs src fuel) mode target)
def namedArgs (src : Index s) : Nat → ReadArgs s
  | 0 => fun _ _ _ => []
  | fuel+1 => fun mode raw target =>
    match raw,target with
    | [],[] => [⟨[],.nil⟩]
    | n::ns,t::ts =>
      (named src fuel mode n t).flatMap fun a =>
        (namedArgs src fuel mode ns ts).map fun b => ⟨a.val++b.val,.cons a.property b.property⟩
    | _,_ => []
end

end Yulang.GeneralDeclarativeAlternativeNamed333
