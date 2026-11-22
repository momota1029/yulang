import Yulang.GeneralDeclarativeEndpointBatch336

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEndpointProgram336
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWhere319 (Capture InInterval)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeEndpointRecord336 (Read interp field_interval labels)
open GeneralDeclarativeEndpointResidual336 (exact_residuals)
open GeneralDeclarativeEndpointNames336 (Triple)
open GeneralDeclarativeEndpointBatch336 (slots atSlots)
open GeneralDeclarativeRecordChannel330 (project)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleCanonicalRows (Row normalize residual)
open CommonNominalFullCarrier (Ty mask)
open GeneralDeclarationPatterns (Pattern)

inductive Projection where
  | field (arg : Capture) (label : Nat) (lo hi : Expr)
  | rest (arg : Capture) (keys : List Nat) (lo hi : Expr)

def Projection.eval : Projection → Assignment → Option Triple
  | .field a label low high,m =>
    (project label false [] (m a.center).1).map fun mid =>
      (interp m low,mid,interp m high)
  | .rest a keys low high,m =>
    some (mask keys (interp m low),mask keys (m a.center).1,mask keys (interp m high))

abbrev Jobs := List (Nat × Projection)

def template : List (Nat × Nat) → Nat → Pattern
  | [],r => .var r
  | (label,binder)::rest,r => .record label (.var binder) (template rest r)

theorem hide_away {key : Nat} {fields : List (Nat × Nat)} (notListed : key ∉ fields.map Prod.fst)
    (r : Nat) : GeneralDeclarationPatterns.hide key (template fields r) = template fields r := by
  induction fields with
  | nil => rfl
  | cons first tail ih =>
    obtain ⟨k,n⟩ := first
    have diff : key ≠ k := fun same => notListed (same ▸ List.mem_cons_self)
    have away : key ∉ tail.map Prod.fst := fun seen => notListed (List.mem_cons_of_mem _ seen)
    simp [template,GeneralDeclarationPatterns.hide,diff,ih away]

theorem normal {fields : List (Nat × Nat)} (distinct : (fields.map Prod.fst).Nodup) (r : Nat) :
    GeneralDeclarationPatterns.normalize (template fields r) = template fields r := by
  induction fields with
  | nil => rfl
  | cons first tail ih =>
    obtain ⟨k,n⟩ := first
    obtain ⟨before,after⟩ := List.nodup_cons.mp distinct
    simp [template,GeneralDeclarationPatterns.normalize,ih after,hide_away before r]

theorem binders (fields : List (Nat × Nat)) (r : Nat) :
    (template fields r).variables = fields.map Prod.snd ++ [r] := by
  induction fields with
  | nil => rfl
  | cons first tail ih =>
    obtain ⟨k,n⟩ := first
    simp [template,Pattern.variables,ih]

/-- Consume the two ordered source lists in precisely the pattern's
field order. A repeated binder remains a separate occurrence; it is
not deduplicated by the endpoint observer. -/
def fields (arg : Capture) : List (Nat × Nat) → Row Expr → Row Expr → Option Jobs
  | [],[],[] => some []
  | (label,binder)::rest,(lk,a)::ls,(hk,b)::hs =>
    if lk = label ∧ hk = label then
      (fields arg rest ls hs).map ((binder,.field arg label a b)::·)
    else none
  | _,_,_ => none

def ready (arg : Capture) (templateFields : List (Nat × Nat)) (tailBinder : Nat)
    (ls us first last : Row Expr) (le ue : Expr) : Option Jobs := do
  let keys := templateFields.map Prod.fst
  let uses ← fields arg templateFields first last
  pure (uses ++ [(tailBinder,.rest arg keys (withTail (residual keys (normalize ls)) le)
    (withTail (residual keys (normalize us)) ue))])

theorem fields_complete (lo : first.map Prod.fst = shape.map Prod.fst)
    (hi : last.map Prod.fst = shape.map Prod.fst) :
    ∃ jobs, fields arg shape first last = some jobs := by
  induction shape generalizing first last with
  | nil => cases first <;> cases last <;> simp_all [fields]
  | cons firstShape rest ih =>
    obtain ⟨key,binder⟩ := firstShape
    cases first with
    | nil => simp at lo
    | cons one ls =>
      cases last with
      | nil => simp at hi
      | cons two us =>
        obtain ⟨lk,a⟩ := one
        obtain ⟨hk,b⟩ := two
        simp only [List.map_cons,List.cons.injEq] at lo hi
        obtain ⟨jobs,computed⟩ := ih lo.2 hi.2
        exact ⟨(binder,.field arg key a b)::jobs,by simp [fields,lo.1,hi.1,computed]⟩

theorem from_supported {s : State} {p : Supported s done}
    (r : Read p arg (shape.map Prod.fst) ls us first last le ue) (tail : Nat) :
    ∃ jobs, ready arg shape tail ls us first last le ue = some jobs := by
  obtain ⟨jobs,computed⟩ := fields_complete (arg := arg) (labels r).1 (labels r).2
  exact ⟨jobs ++ [(tail,.rest arg (shape.map Prod.fst)
    (withTail (residual (shape.map Prod.fst) (normalize ls)) le)
    (withTail (residual (shape.map Prod.fst) (normalize us)) ue))],by simp [ready,computed]⟩

theorem fields_exact (built : fields arg shape first last = some jobs) :
    jobs.map Prod.fst = shape.map Prod.snd ∧
    ∀ j ∈ jobs, ∃ key a b, j.2 = .field arg key a b ∧ (key,a) ∈ first ∧ (key,b) ∈ last := by
  induction shape generalizing first last jobs with
  | nil => cases first <;> cases last <;> simp_all [fields]
  | cons one rest ih =>
    obtain ⟨key,binder⟩ := one
    cases first with
    | nil => simp [fields] at built
    | cons left ls =>
      cases last with
      | nil => simp [fields] at built
      | cons right us =>
        obtain ⟨lk,a⟩ := left
        obtain ⟨hk,b⟩ := right
        by_cases same : lk = key ∧ hk = key
        · obtain ⟨seq,req⟩ := same
          subst lk; subst hk
          cases computed : fields arg rest ls us with
          | none => simp [fields,computed] at built
          | some collected =>
            have eq : (binder,.field arg key a b)::collected = jobs :=
              Option.some.inj (by simpa [fields,computed] using built)
            subst jobs
            obtain ⟨names,origins⟩ := ih computed
            refine ⟨by simp [names],?_⟩
            intro j used
            rcases List.mem_cons.mp used with rfl|earlier
            · exact ⟨_,_,_,rfl,List.mem_cons_self,List.mem_cons_self⟩
            · obtain ⟨k,v,w,eq,l,h⟩ := origins j earlier
              exact ⟨k,v,w,eq,List.mem_cons_of_mem _ l,List.mem_cons_of_mem _ h⟩
        · simp [fields,same] at built

theorem list_sound {s : State} {p : Supported s done}
    (r : Read p arg (shape.map Prod.fst) ls us first last le ue)
    (built : ready arg shape tail ls us first last le ue = some jobs) :
    jobs.map Prod.fst = (template shape tail).variables ∧
    ∀ m, Models s m → ∀ j ∈ jobs, ∃ v, j.2.eval m = some v ∧ InInterval v.1 v.2.2 v.2.1 := by
  cases computed : fields arg shape first last with
  | none => simp [ready,computed] at built
  | some collected =>
    have eq := Option.some.inj (by simpa [ready,computed] using built)
    change collected ++ [_] = jobs at eq
    subst jobs
    have exactJobs := fields_exact computed
    refine ⟨by simp [binders,exactJobs.1],?_⟩
    intro m valid j used
    rcases List.mem_append.mp used with existing|rest
    · obtain ⟨key,a,b,tied,one,two⟩ := exactJobs.2 j existing
      obtain ⟨payload,seen,bounds⟩ := field_interval r one two m valid
      exact ⟨(interp m a,payload,interp m b),by simp [Projection.eval,tied,seen],bounds⟩
    · cases List.mem_singleton.mp rest
      exact ⟨_,rfl,exact_residuals r m valid⟩

end Yulang.GeneralDeclarativeEndpointProgram336
