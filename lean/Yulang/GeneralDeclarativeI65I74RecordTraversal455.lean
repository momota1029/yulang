import Yulang.GeneralDeclarativeI65I74RecordEntry412
import Yulang.GeneralDeclarativeI65I74WhereCohortFullFit451

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordTraversal455
open GeneralDeclarativeHead320 (Equation)
abbrev RawSnapshot := GeneralDeclarativeHead320.State
open GeneralDeclarativeGraphRows321 (shapeOf observed structural)
open GeneralDeclarativeK2Graph321 (Shape)
open GeneralDeclarativeK2Alias321 (AliasCycle)

open GeneralDeclarativeInspect321 (Inspects Visit fieldPatterns)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWitnessCycle350 (Link checksLink link)
open WhereSites450 (alias_wire_from_actual_derivation450)
open List410 (ExactEscapeWire)
open SplitEscape446 (splitCheck446 checked_split_escape_excludes_exact_raw_K2446)
open SplitEscape446.SplitCompact447 (raw_safe_iff_small_witness447)
open RecordK2412 (FieldCycleWire checkCycleAt412 cycle_at_sound412)

/-- A checked-open ledger is separate from the raw graph used only for K2.
The caller supplies the genuine source-ledger implementation. -/
structure OpenOps where
  Token : Type
  allowed : Nat → Equation → Prop
  check : Nat → Equation → Token → Bool
  exactCheck : ∀ root row, (∃ w, check root row w = true) ↔ allowed root row

structure StepWire (o : OpenOps) where
  rawRow : Nat
  owner : Link
  fieldOrdinal : Nat
  patternOrdinal : Nat
  token : o.Token

def Step (s : RawSnapshot) (o : OpenOps) (root : Nat) (code : Expr)
    (label child : Nat) (query : Expr) : Prop :=
  ∃ row ∈ s.equations, ∃ fs,
    GeneralDeclarativeLowerKnown321.Alias s root row.left ∧ shapeOf row.right = some (.record fs) ∧
    o.allowed root row ∧ (label,child) ∈ fs ∧ (label,query) ∈ fieldPatterns code

def readStep (s : RawSnapshot) (o : OpenOps) (root : Nat) (code : Expr) (w : StepWire o) :
    Option (Nat × Nat × Expr) := do
  let row ← s.equations[w.rawRow]?
  if checksLink s root row.left w.owner && o.check root row w.token then
    match shapeOf row.right with
    | some (.record fields) =>
      match fields[w.fieldOrdinal]?, (fieldPatterns code)[w.patternOrdinal]? with
      | some (label,child), some (name,query) =>
        if label = name then some (label,child,query) else none
      | _,_ => none
    | _ => none
  else none

theorem step_projects_original_visit455 {s o root code label child query site}
    (step : Step s o root code label child query)
    (tail : Visit (structural s) child query site) : Visit (structural s) root code site := by
  obtain ⟨row,member,fs,alias,decoded,_,actual,written⟩ := step
  have raw : structural s root (.record fs) := by
    cases row
    exact ⟨_,alias,_,member,decoded⟩
  cases code
  case record => exact .field raw actual written tail
  all_goals simp [fieldPatterns] at written

theorem read_step_sound455 {s o root code label child query} {w : StepWire o}
    (ok : readStep s o root code w = some (label,child,query)) :
    Step s o root code label child query := by
  cases r : s.equations[w.rawRow]? with
  | none => simp [readStep,r,Option.bind] at ok
  | some row =>
    by_cases check : checksLink s root row.left w.owner && o.check root row w.token
    · have checked := Bool.and_eq_true_iff.mp check
      cases sh : shapeOf row.right with
      | none => simp [readStep,r,sh,Option.bind,checked.1,checked.2] at ok
      | some shape =>
        cases shape <;> simp [readStep,r,sh,Option.bind,checked.1,checked.2] at ok
        rename_i fs
        cases f : fs[w.fieldOrdinal]? with
        | none => simp [f] at ok
        | some pair =>
          rcases pair with ⟨actual,site⟩
          cases pat : (fieldPatterns code)[w.patternOrdinal]? with
          | none => simp [f,pat] at ok
          | some qp =>
            rcases qp with ⟨written,a⟩
            by_cases keys : actual = written
            · subst written
              simp [f,pat] at ok
              rcases ok with ⟨rfl,rfl,rfl⟩
              exact ⟨row,List.mem_of_getElem? r,fs,link checked.1,sh,
                (o.exactCheck _ _).mp ⟨w.token,checked.2⟩,
                List.mem_of_getElem? f,List.mem_of_getElem? pat⟩
            · simp [f,pat,keys] at ok
    · have no : ¬ (checksLink s root row.left w.owner = true ∧ o.check root row w.token = true) :=
        fun h => check (Bool.and_eq_true_iff.mpr h)
      simp [readStep,r,Option.bind,no] at ok

theorem step_has_finite_wire455 {s o root code label child query}
    (step : Step s o root code label child query) :
    ∃ w : StepWire o, readStep s o root code w = some (label,child,query) := by
  obtain ⟨row,member,fs,alias,decoded,source,actual,written⟩ := step
  obtain ⟨ri,byRow⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨a,byActual⟩ := List.mem_iff_getElem?.mp actual
  obtain ⟨q,byQuery⟩ := List.mem_iff_getElem?.mp written
  obtain ⟨l,byAlias⟩ := alias_wire_from_actual_derivation450 alias
  obtain ⟨auth,bySource⟩ := (o.exactCheck _ _).mpr source
  exact ⟨⟨ri,l,a,q,auth⟩,by simp [readStep,byRow,Option.bind,byAlias,bySource,decoded,byActual,byQuery]⟩

def termInspects : Expr → Bool
  | .primitive .. | .nominal .. | .record .. | .variant .. => true
  | _ => false

theorem term_inspects_exact455 (code : Expr) : termInspects code = true ↔ Inspects code := by
  cases code <;> constructor <;> intro h <;>
    first | exact Inspects.primitive | exact Inspects.nominal |
      exact Inspects.record | exact Inspects.variant | rfl | cases h

abbrev TrailPath := List (Nat × Nat)

/-- The raw cycle test stops at the first bad entered position; every
proper prefix is source-authorized and raw-safe. A variable is not a
position, even when its captured value happens to be recursive. -/
inductive Trail (s : RawSnapshot) (o : OpenOps) : Nat → Expr → TrailPath → Nat → Prop
  | stop : Inspects code → Trail s o root code [] root
  | down : ¬AliasCycle s (observed s) root → Step s o root code label child query →
      Trail s o child query rest site → Trail s o root code ((label,child)::rest) site

inductive TrailWire (o : OpenOps) where
  | stop
  | down (step : StepWire o) (escape : ExactEscapeWire) (rest : TrailWire o)

def readTrail (s : RawSnapshot) (o : OpenOps) (root : Nat) (code : Expr) :
    TrailWire o → Option (TrailPath × Nat)
  | .stop => if termInspects code then some ([],root) else none
  | .down w e ws => do
    let (label,child,query) ← readStep s o root code w
    if splitCheck446 s root e then
      let (ts,site) ← readTrail s o child query ws
      some ((label,child)::ts,site)
    else none

theorem trail_projects_exact_inspection455 {s o root code path site}
    (t : Trail s o root code path site) : Visit (structural s) root code site := by
  induction t with
  | stop inspect => exact .here inspect
  | down _ step _ ih => exact step_projects_original_visit455 step ih

theorem read_trail_sound455 {s o root code path site} {w : TrailWire o}
    (ok : readTrail s o root code w = some (path,site)) : Trail s o root code path site := by
  induction w generalizing root code path site with
  | stop =>
    by_cases h : termInspects code
    · simp [readTrail,h] at ok
      rcases ok with ⟨rfl,rfl⟩
      exact .stop ((term_inspects_exact455 code).mp h)
    · simp [readTrail,h] at ok
  | down w e ws ih =>
    cases a : readStep s o root code w with
    | none => simp [readTrail,a,Option.bind] at ok
    | some q =>
      rcases q with ⟨label,child,query⟩
      by_cases safe : splitCheck446 s root e
      · cases rest : readTrail s o child query ws with
        | none => simp [readTrail,a,safe,rest,Option.bind] at ok
        | some p =>
          rcases p with ⟨tail,last⟩
          simp [readTrail,a,safe,rest,Option.bind] at ok
          rcases ok with ⟨rfl,rfl⟩
          exact .down (checked_split_escape_excludes_exact_raw_K2446 safe) (read_step_sound455 a) (ih rest)
      · simp [readTrail,a,safe,Option.bind] at ok

theorem trail_has_finite_data_witness455 {s o root code path site}
    (h : Trail s o root code path site) :
    ∃ w : TrailWire o, readTrail s o root code w = some (path,site) := by
  induction h with
  | stop inspects => exact ⟨.stop,by simp [readTrail,(term_inspects_exact455 _).mpr inspects]⟩
  | @down root code label child query tail site safe step _ ih =>
    obtain ⟨w,read⟩ := step_has_finite_wire455 step
    obtain ⟨escape,ok,_,_⟩ := (raw_safe_iff_small_witness447 s root).mp safe
    obtain ⟨ws,rest⟩ := ih
    exact ⟨.down w escape ws,by simp [readTrail,read,Option.bind,ok,rest]⟩

theorem read_trail_exact455 (s : RawSnapshot) (o : OpenOps) (root : Nat) (code : Expr)
    (path : TrailPath) (site : Nat) :
    (∃ w : TrailWire o, readTrail s o root code w = some (path,site)) ↔ Trail s o root code path site :=
  ⟨fun ⟨_,ok⟩ => read_trail_sound455 ok,trail_has_finite_data_witness455⟩

structure CycleVisitWire (o : OpenOps) where
  trail : TrailWire o
  cycle : FieldCycleWire

def readCycleVisit (s : RawSnapshot) (o : OpenOps) (root : Nat) (code : Expr) (w : CycleVisitWire o) :
    Option (TrailPath × Nat) := do
  let (path,site) ← readTrail s o root code w.trail
  if !path.isEmpty && checkCycleAt412 s site w.cycle then some (path,site) else none

def ExactCycleVisit (s : RawSnapshot) (o : OpenOps) (root : Nat) (code : Expr)
    (path : TrailPath) (site : Nat) : Prop :=
  Trail s o root code path site ∧ path ≠ [] ∧ AliasCycle s (observed s) site

theorem read_cycle_visit_sound455 {s o root code path site} {w : CycleVisitWire o}
    (ok : readCycleVisit s o root code w = some (path,site)) :
    ExactCycleVisit s o root code path site := by
  cases a : readTrail s o root code w.trail with
  | none => simp [readCycleVisit,a,Option.bind] at ok
  | some q =>
    rcases q with ⟨steps,last⟩
    change (readTrail s o root code w.trail).bind _ = _ at ok
    rw [a] at ok
    change ((if !steps.isEmpty && checkCycleAt412 s last w.cycle then some (steps,last) else none) = some (path,site)) at ok
    split at ok
    · rename_i checked
      have eq : steps = path ∧ last = site := by simpa using ok
      rcases eq with ⟨rfl,rfl⟩
      have pass := Bool.and_eq_true_iff.mp checked
      refine ⟨read_trail_sound455 a,?_,cycle_at_sound412 pass.2⟩
      intro empty
      simp [empty] at pass
    · cases ok


theorem naked_raw_cycle_has_finite_wire455 (s : RawSnapshot) (site : Nat) :
    AliasCycle s (observed s) site ↔ ∃ w : FieldCycleWire, checkCycleAt412 s site w = true := by
  constructor
  · rintro ⟨_,_,first,rest,returns⟩
    obtain ⟨head,atChild,ok⟩ := WhereSites450.structural_wire_from_actual_row450 first
    obtain ⟨tail,last,closed⟩ := WhereSites450.path_wire_from_actual_derivation450 rest returns
    exact ⟨⟨head,tail,last⟩,by simp [checkCycleAt412,atChild,ok,closed]⟩
  · rintro ⟨_,checked⟩
    exact cycle_at_sound412 checked

theorem exact_cycle_visit_has_finite_wire455 {s o root code path site}
    (actual : ExactCycleVisit s o root code path site) :
    ∃ w : CycleVisitWire o, readCycleVisit s o root code w = some (path,site) := by
  obtain ⟨trail,nonempty,cycle⟩ := actual
  obtain ⟨wt,ok⟩ := trail_has_finite_data_witness455 trail
  obtain ⟨wc,cy⟩ := (naked_raw_cycle_has_finite_wire455 s site).mp cycle
  exact ⟨⟨wt,wc⟩,by simp [readCycleVisit,ok,cy,nonempty,Option.bind]⟩

theorem exact_cycle_visit_iff_finite_wire455 (s : RawSnapshot) (o : OpenOps)
    (root : Nat) (code : Expr) (path : TrailPath) (site : Nat) :
    (∃ w : CycleVisitWire o, readCycleVisit s o root code w = some (path,site)) ↔
      ExactCycleVisit s o root code path site :=
  ⟨fun ⟨_,ok⟩ => read_cycle_visit_sound455 ok,exact_cycle_visit_has_finite_wire455⟩

theorem exact_cycle_visit_is_safe_at_root_and_real_at_site455 {s o root code path site}
    (exact : ExactCycleVisit s o root code path site) :
    ¬AliasCycle s (observed s) root ∧ Visit (structural s) root code site ∧
      AliasCycle s (observed s) site := by
  refine ⟨?_,trail_projects_exact_inspection455 exact.1,exact.2.2⟩
  have nz := exact.2.1
  cases exact.1 with
  | stop => exact (nz rfl).elim
  | down safe => exact safe

end Yulang.GeneralDeclarativeI65.I72.RecordTraversal455
