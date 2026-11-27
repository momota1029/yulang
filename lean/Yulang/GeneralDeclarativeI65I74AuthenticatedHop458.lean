import Yulang.GeneralDeclarativeI65I74InlineVariant458

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.AuthenticatedHop458
open RecordTraversal455 RecordTraversal455.MixedQA
open GeneralDeclarativeWitnessCycle350 (Link checksLink link)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (shapeOf observed structural)
open GeneralDeclarativeInspect321 (Inspects Visit)
open GeneralDeclarativeK2Graph321 (Shape)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeHead320 (Equation)
open List410 (ExactEscapeWire)
open SplitEscape446 (splitCheck446 checked_split_escape_excludes_exact_raw_K2446)
open SplitEscape446.SplitCompact447 (raw_safe_iff_small_witness447)
open RecordK2412 (FieldCycleWire checkCycleAt412 cycle_at_sound412)

structure Policy where
  Token : Type
  inline : Token → Bool
  opens : Nat → Equation → Address → Nat → Bool → Prop
  checks : Nat → Equation → Address → Nat → Token → Bool
  reflected : ∀ l r a c use,
    (∃ token, inline token = use ∧ checks l r a c token = true) ↔ opens l r a c use

structure HopWire (p : Policy) where
  row : Nat
  alias : Link
  child : ChildWire
  author : p.Token

def AtStep (s : RawSnapshot) (p : Policy) (root : Nat) (code : Expr)
    (addr : Address) (child : Nat) (next : Expr) (used : Bool) : Prop :=
  ∃ r ∈ s.equations, ∃ sh, GeneralDeclarativeLowerKnown321.Alias s root r.left ∧ shapeOf r.right = some sh ∧
    ChildAt sh code addr child next ∧ p.opens root r addr child used

def readStep (s : RawSnapshot) (p : Policy) (root : Nat) (code : Expr)
    (w : HopWire p) : Option (Address × Nat × Expr × Bool) := do
  let r ← s.equations[w.row]?
  let shape ← shapeOf r.right
  let pick ← readChild w.child shape code
  if checksLink s root r.left w.alias && p.checks root r pick.address pick.child w.author then
    some (pick.address,pick.child,pick.next,p.inline w.author)
  else none

theorem read_step_sound458 {s p root code a c nxt use} {w : HopWire p}
    (ok : readStep s p root code w = some (a,c,nxt,use)) :
    AtStep s p root code a c nxt use := by
  cases row : s.equations[w.row]? with
  | none => simp [readStep,row,Option.bind] at ok
  | some r =>
    cases seen : shapeOf r.right with
    | none => simp [readStep,row,seen,Option.bind] at ok
    | some sh =>
      cases child : readChild w.child sh code with
      | none => simp [readStep,row,seen,child,Option.bind] at ok
      | some pick =>
        by_cases pass : checksLink s root r.left w.alias = true ∧
            p.checks root r pick.address pick.child w.author = true
        · simp [readStep,row,seen,child,Option.bind,pass.1,pass.2] at ok
          obtain ⟨rfl,rfl,rfl,rfl⟩ := ok
          exact ⟨r,List.mem_of_getElem? row,sh,link pass.1,seen,pick.valid,
            (p.reflected ..).mp ⟨w.author,rfl,pass.2⟩⟩
        · simp [readStep,row,seen,child,Option.bind,Bool.and_eq_true,pass] at ok

theorem read_step_complete458 {s p root code a c nxt use}
    (atStep : AtStep s p root code a c nxt use) :
    ∃ w, readStep s p root code w = some (a,c,nxt,use) := by
  obtain ⟨r,seen,sh,alias,shape,child,made⟩ := atStep
  obtain ⟨i,readRow⟩ := List.mem_iff_getElem?.mp seen
  obtain ⟨link,readAlias⟩ := WhereSites450.alias_wire_from_actual_derivation450 alias
  obtain ⟨wire,atChild⟩ :=
    every_canonical_child_has_its_actual_field_or_ordinal_wire (⟨a,c,nxt,child⟩ : ReadChild sh code)
  obtain ⟨token,which,verify⟩ := (p.reflected ..).mpr made
  exact ⟨⟨i,link,wire,token⟩,by simp [readStep,readRow,shape,atChild,readAlias,verify,which,Option.bind]⟩

inductive Trail (s : RawSnapshot) (p : Policy) : Nat → Expr → MixedPath → Nat → Bool → Prop
  | stop : Inspects code → Trail s p root code [] root false
  | down : ¬AliasCycle s (observed s) root → AtStep s p root code a c next used →
      Trail s p c next tail terminal rest →
      Trail s p root code ((a,c)::tail) terminal (used || rest)

inductive Wire (p : Policy) where
  | stop
  | down (hop : HopWire p) (escape : ExactEscapeWire) (rest : Wire p)

def readTrail (s : RawSnapshot) (p : Policy) (root : Nat) (code : Expr) :
    Wire p → Option (MixedPath × Nat × Bool)
  | .stop => if termInspects code then some ([],root,false) else none
  | .down hop clear tail => do
    let (a,c,next,used) ← readStep s p root code hop
    if splitCheck446 s root clear then
      let (path,terminal,rest) ← readTrail s p c next tail
      some ((a,c)::path,terminal,used || rest)
    else none

theorem read_trail_sound458 {s p root code path terminal use} {w : Wire p}
    (ok : readTrail s p root code w = some (path,terminal,use)) :
    Trail s p root code path terminal use := by
  induction w generalizing root code path terminal use with
  | stop =>
    by_cases rigid : termInspects code
    · simp [readTrail,rigid] at ok
      obtain ⟨rfl,rfl,rfl⟩ := ok
      exact .stop ((term_inspects_exact455 _).mp rigid)
    · simp [readTrail,rigid] at ok
  | down hop cut rest ih =>
    cases entered : readStep s p root code hop with
    | none => simp [readTrail,entered,Option.bind] at ok
    | some raw =>
      obtain ⟨a,c,new,used⟩ := raw
      by_cases safe : splitCheck446 s root cut
      · cases deeper : readTrail s p c new rest with
        | none => simp [readTrail,entered,safe,deeper,Option.bind] at ok
        | some result =>
          obtain ⟨tail,last,restUses⟩ := result
          simp [readTrail,entered,safe,deeper,Option.bind] at ok
          obtain ⟨rfl,rfl,rfl⟩ := ok
          exact .down (checked_split_escape_excludes_exact_raw_K2446 safe)
            (read_step_sound458 entered) (ih deeper)
      · simp [readTrail,entered,safe,Option.bind] at ok

theorem read_trail_complete458 {s p root code path terminal use}
    (actual : Trail s p root code path terminal use) :
    ∃ w, readTrail s p root code w = some (path,terminal,use) := by
  induction actual with
  | stop rigid => exact ⟨.stop,by simp [readTrail,(term_inspects_exact455 _).mpr rigid]⟩
  | down safe atStep _ ih =>
    obtain ⟨hop,entry⟩ := read_step_complete458 atStep
    obtain ⟨hold,escape,_,_⟩ := (raw_safe_iff_small_witness447 s _).mp safe
    obtain ⟨w,deep⟩ := ih
    exact ⟨.down hop hold w,by simp [readTrail,entry,escape,deep,Option.bind]⟩

theorem genuine_used_hop_proves_exact_existing_raw_visit458 {s p root code path terminal use}
    (t : Trail s p root code path terminal use) : Visit (structural s) root code terminal := by
  induction t with
  | stop rigid => exact .here rigid
  | down _ atStep _ ih =>
    obtain ⟨row,seen,sh,alias,shape,actual,_⟩ := atStep
    cases row
    exact checked_child_is_exact_visit_step ⟨_,alias,_,seen,shape⟩ actual ih

theorem used_trace_is_root_safe_and_nonempty458 {s p root code path terminal use}
    (t : Trail s p root code path terminal use) (used : use = true) :
    ¬AliasCycle s (observed s) root ∧ path ≠ [] := by
  cases t with
  | stop => cases used
  | down safe _ _ => exact ⟨safe,by simp⟩

structure CycleWire (p : Policy) where
  trail : Wire p
  cycle : FieldCycleWire

def readCycle (s : RawSnapshot) (p : Policy) (root : Nat) (code : Expr)
    (w : CycleWire p) : Option (MixedPath × Nat) := do
  let (path,endAt,used) ← readTrail s p root code w.trail
  if used && checkCycleAt412 s endAt w.cycle then some (path,endAt) else none

theorem exact_used_cycle_has_finite_wire458 (s : RawSnapshot) (p : Policy) (root : Nat) (code : Expr)
    (path : MixedPath) (terminal : Nat) :
    (∃ w, readCycle s p root code w = some (path,terminal)) ↔
      Trail s p root code path terminal true ∧ AliasCycle s (observed s) terminal := by
  constructor
  · rintro ⟨w,h⟩
    cases actual : readTrail s p root code w.trail with
    | none => simp [readCycle,actual,Option.bind] at h
    | some result =>
      obtain ⟨xs,last,used⟩ := result
      cases used with
      | false => simp [readCycle,actual,Option.bind] at h
      | true =>
        by_cases cycle : checkCycleAt412 s last w.cycle
        · simp [readCycle,actual,cycle,Option.bind] at h
          obtain ⟨rfl,rfl⟩ := h
          exact ⟨read_trail_sound458 actual,cycle_at_sound412 cycle⟩
        · simp [readCycle,actual,cycle,Option.bind] at h
  · rintro ⟨trail,cycle⟩
    obtain ⟨w,read⟩ := read_trail_complete458 trail
    obtain ⟨closed,yes⟩ := (naked_raw_cycle_has_finite_wire455 s terminal).mp cycle
    exact ⟨⟨w,closed⟩,by simp [readCycle,read,yes,Option.bind]⟩

end Yulang.GeneralDeclarativeI65.I72.AuthenticatedHop458
