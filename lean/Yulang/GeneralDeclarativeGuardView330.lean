import Yulang.GeneralDeclarativeCurrentReceipt330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeGuardView330
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeLowerKnown321 (Alias Knows Ready)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeTrace321 (Trace TraceArgs)
open GeneralDeclarativeEndpointProbe321 (HeadMatches Matches)
open CommonRoleOutermostResolver (All₂)

/-- The exact finite information consumed by the name-only positive
probes. Bounds may be supplied by proof (not literal interval entries),
but source rows must still be authorized in the target view.
This says nothing about the full ordinary K2 graph. -/
structure View (s t : State) : Prop where
  bound : ∀ {a b}, Bound s.normal a b → Bound t.normal a b
  rows : s.equations ⊆ t.equations

theorem alias {s t : State} (v : View s t) (seen : Alias s a b) : Alias t a b := by
  induction seen with
  | bounds one two => exact .bounds (v.bound one) (v.bound two)
  | forward row => exact .forward (v.rows row)
  | backward row => exact .backward (v.rows row)
  | trans _ _ x y => exact .trans x y

theorem known {s t : State} (v : View s t) (old : Knows s n tag) : Knows t n tag := by
  obtain ⟨row,present,link,shape⟩ := old
  exact ⟨row,v.rows present,alias v link,shape⟩

theorem trace {s t : State} (v : View s t) (seen : Trace s mode n code uses) :
    Trace t mode n code uses :=
  Trace.rec
    (motive_1 := fun mode n code links _ => Trace t mode n code links)
    (motive_2 := fun mode ns codes links _ => TraceArgs t mode ns codes links)
    (by intro _ _ _; exact .capture)
    (by intro _ _ _ _ _ _ _ equal stored _ ih; exact .primitive (alias v equal) (v.rows stored) ih)
    (by intro _ _ _ _ _ _ _ equal stored _ ih; exact .nominal (alias v equal) (v.rows stored) ih)
    (by intro _ _ _ _ _ _ _ _ _ _ equal stored _ _ ih jh
        exact .record (alias v equal) (v.rows stored) ih jh)
    (by intro _ _ _ _ _ _ _ equal stored _ ih; exact .variant (alias v equal) (v.rows stored) ih)
    (by intro _ _ _ _ _ _ _ _ _ equal stored _ _ ih jh
        exact .join (alias v equal) (v.rows stored) ih jh)
    (by intro _; exact .nil)
    (by intro _ _ _ _ _ _ _ _ _ ih jh; exact .cons ih jh)
    seen

theorem endpoint {s t : State} (view : View s t) (has : Matches s c i arg pat) :
    Matches t c i arg pat := by
  obtain ⟨⟨first,last⟩,code,lo,hi,printed,lower,upper⟩ := has
  exact ⟨⟨view.bound first,view.bound last⟩,code,lo,hi,printed,trace view lower,trace view upper⟩

theorem args {s t : State} (v : View s t) (seen : All₂ (Matches s c i) arguments patterns) :
    All₂ (Matches t c i) arguments patterns := by
  induction seen with
  | nil => exact .nil
  | cons here _ rest => exact .cons (endpoint v here) rest

theorem ready {s t : State} {p : Supported s done} {q : Supported t later}
    (v : View (restriction p) (restriction q)) (old : Ready p d) : Ready q d := by
  intro a used
  obtain ⟨tag,has⟩ := old a used
  exact ⟨tag,known v has⟩

theorem positive_exact {s t : State} {p : Supported s done} {q : Supported t later}
    (toCurrent : View (restriction p) (restriction q)) (fromCurrent : View (restriction q) (restriction p)) :
    (Ready p d ↔ Ready q d) ∧
    (∀ impl, HeadMatches (restriction p) c i d impl ↔ HeadMatches (restriction q) c i d impl) :=
  ⟨⟨ready toCurrent,ready fromCurrent⟩,fun _ => ⟨args toCurrent,args fromCurrent⟩⟩

open GeneralDeclarativeCurrentReceipt330 (Receipt)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativePriority321 (Candidates Survives Blocked Recurs)

theorem ordinary_bound {s t : State} (receipt : Receipt s t) (known : Bound s.normal a b) :
    Bound t.normal a b := by
  induction known with
  | interval old => exact receipt.intervals _ old
  | constraint atom => exact .constraint (receipt.constraints atom)
  | refl a => exact .refl a
  | trans _ _ x y => exact .trans x y

theorem using_receipt {s t : State} {p : Supported s done} {q : Supported t later}
    (receipt : Receipt s t) (sourceRows : (restriction p).equations ⊆ (restriction q).equations) :
    View (restriction p) (restriction q) :=
  ⟨fun h => ordinary_bound (s := s) (t := t) receipt h,sourceRows⟩

theorem elected {s t : State} {p : Supported s done} {q : Supported t later}
    {prior current : Candidates}
    (v : View (restriction p) (restriction q))
    (agrees : ∀ decl, prior.viable d decl ↔ current.viable d decl)
    (unresolved : ∀ decl, prior.unresolved d decl ↔ current.unresolved d decl)
    (actualK2 : ¬Recurs t r i current d)
    (before : Elected s r i p prior d impl) : Elected t r i q current d impl := by
  refine ⟨ready v before.ready,actualK2,?_,⟨before.viable.1,(agrees _).mp before.viable.2⟩,?_⟩
  · rintro ⟨other,visible,waiting⟩
    exact before.clear ⟨other,visible,(unresolved _).mpr waiting⟩
  · intro other still
    exact before.unique other ⟨still.1,(agrees _).mpr still.2⟩

end Yulang.GeneralDeclarativeGuardView330
