import Yulang.GeneralDeclarativeI65I74RecordTraversal455

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordTraversal455.MixedQA
open GeneralDeclarativeK2Graph321 (Shape View)
open GeneralDeclarativeInspect321 (Visit fieldPatterns)
open GeneralNominalCenteredHeadMatExpressions (Expr)

inductive Address where
  | primitive (tag : GeneralCandidateInspection.Primitive) (index : Nat)
  | nominal (tag index : Nat)
  | field (label : Nat)
  | variant (label : Nat)
  deriving DecidableEq

inductive ChildAt : Shape → Expr → Address → Nat → Expr → Prop
  | primitive :
    xs[i]? = some x → ps[i]? = some p →
    ChildAt (.primitive tag xs) (.primitive tag ps) (.primitive tag i) x p
  | nominal :
    xs[i]? = some x → ps[i]? = some p →
    ChildAt (.nominal tag xs) (.nominal tag ps) (.nominal tag i) x p
  | field :
    (l,x) ∈ fs → (l,p) ∈ fieldPatterns (.record r v t) →
    ChildAt (.record fs) (.record r v t) (.field l) x p
  | variant :
    ChildAt (.variant lbl x) (.variant lbl v) (.variant lbl) x v

theorem checked_child_is_exact_visit_step {sh c addr x p root site}
    {view : View} (origin : view root sh) (child : ChildAt sh c addr x p)
    (rest : Visit view x p site) : Visit view root c site := by
  cases child with
  | primitive ax aq => exact .primitive origin aq ax rest
  | nominal ax aq => exact .nominal origin aq ax rest
  | field f pat => exact .field origin f pat rest
  | variant => exact .variant origin rest

structure ReadChild (sh : Shape) (code : Expr) where
  address : Address
  child : Nat
  next : Expr
  valid : ChildAt sh code address child next

inductive ChildWire where
  | index (i : Nat)
  | field (observed original : Nat)
  | variant

def readChild : ChildWire → (sh : Shape) → (code : Expr) → Option (ReadChild sh code)
  | .index i,.primitive a xs,.primitive b ps =>
    if same : a = b then
      match raw : xs[i]?, written : ps[i]? with
      | some x, some p => some ⟨.primitive a i,x,p,
          by subst b; exact .primitive raw written⟩
      | _,_ => none
    else none
  | .index i,.nominal a xs,.nominal b ps =>
    if same : a = b then
      match raw : xs[i]?, written : ps[i]? with
      | some x, some p => some ⟨.nominal a i,x,p,
          by subst b; exact .nominal raw written⟩
      | _,_ => none
    else none
  | .field i j,.record fs,.record l v t =>
    match raw : fs[i]?, written : (fieldPatterns (.record l v t))[j]? with
    | some (a,x), some (b,q) =>
      if same : a = b then
        some ⟨.field a,x,q,by
          subst b
          exact .field (List.mem_of_getElem? raw) (List.mem_of_getElem? written)⟩
      else none
    | _,_ => none
  | .variant,.variant a x,.variant b p =>
    if same : a = b then some ⟨.variant a,x,p,by subst b; exact .variant⟩ else none
  | _,_,_ => none

theorem every_canonical_child_has_its_actual_field_or_ordinal_wire {sh code}
    (w : ReadChild sh code) : ∃ u, readChild u sh code = some w := by
  rcases w with ⟨a,x,p,c⟩
  cases c with
  | @primitive xs i x ps p tag first last =>
    refine ⟨.index i,?_⟩
    simp only [readChild]
    split <;> try simp_all
    all_goals (split <;> simp_all)
    all_goals (rename_i hx hp; exact ⟨Option.some.inj (hx.symm.trans first),Option.some.inj (hp.symm.trans last)⟩)
  | @nominal xs i x ps p tag first last =>
    refine ⟨.index i,?_⟩
    simp only [readChild]
    split <;> try simp_all
    all_goals (split <;> simp_all)
    all_goals (rename_i hx hp; exact ⟨Option.some.inj (hx.symm.trans first),Option.some.inj (hp.symm.trans last)⟩)
  | field lhs rhs =>
    obtain ⟨i,present⟩ := List.mem_iff_getElem?.mp lhs
    obtain ⟨j,found⟩ := List.mem_iff_getElem?.mp rhs
    refine ⟨.field i j,?_⟩
    simp only [readChild]
    split <;> first | rfl | solve | simp_all | (simp_all; rename_i contra; exact contra _ _ _ _ rfl rfl rfl rfl)
  | variant => exact ⟨.variant,by simp [readChild]⟩

theorem canonical_inspection_has_a_child_view_at_any_proper_step
    {view : View} {root : Nat} {code : Expr} {site : Nat}
    (actual : Visit view root code site) :
    (site = root ∧ GeneralDeclarativeInspect321.Inspects code) ∨
      ∃ (sh : Shape) (p : ReadChild sh code), view root sh ∧ Visit view p.child p.next site := by
  cases actual with
  | here inspect => exact .inl ⟨rfl,inspect⟩
  | primitive seen written raw rest =>
    exact .inr ⟨_,⟨_,_,_,.primitive raw written⟩,seen,rest⟩
  | nominal seen written raw rest =>
    exact .inr ⟨_,⟨_,_,_,.nominal raw written⟩,seen,rest⟩
  | field seen raw written rest =>
    exact .inr ⟨_,⟨_,_,_,.field raw written⟩,seen,rest⟩
  | variant seen rest =>
    exact .inr ⟨_,⟨_,_,_,.variant⟩,seen,rest⟩

#print axioms checked_child_is_exact_visit_step
#print axioms every_canonical_child_has_its_actual_field_or_ordinal_wire
#print axioms canonical_inspection_has_a_child_view_at_any_proper_step


open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeGraphRows321 (shapeOf observed structural)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeWitnessCycle350 (Link checksLink link)
open List410 (ExactEscapeWire)
open RecordK2412 (FieldCycleWire checkCycleAt412)
open SplitEscape446 (splitCheck446 checked_split_escape_excludes_exact_raw_K2446)
open SplitEscape446.SplitCompact447 (raw_safe_iff_small_witness447)

structure OpenWire (o : OpenOps) where
  ordinal : Nat
  rawAlias : Link
  token : o.Token

def AuthoredShape (s : RawSnapshot) (o : OpenOps) (root : Nat) (shape : Shape) : Prop :=
  ∃ r ∈ s.equations, GeneralDeclarativeLowerKnown321.Alias s root r.left ∧
    shapeOf r.right = some shape ∧ o.allowed root r

def readOwned (s : RawSnapshot) (o : OpenOps) (root : Nat) (w : OpenWire o) : Option Shape := do
  let row ← s.equations[w.ordinal]?
  if checksLink s root row.left w.rawAlias && o.check root row w.token then shapeOf row.right else none

theorem read_owned_sound {s o root sh} {w : OpenWire o} (ok : readOwned s o root w = some sh) :
    AuthoredShape s o root sh := by
  cases here : s.equations[w.ordinal]? with
  | none => simp [readOwned,here,Option.bind] at ok
  | some row =>
    have out : checksLink s root row.left w.rawAlias = true ∧
        o.check root row w.token = true ∧ shapeOf row.right = some sh := by
      simpa [readOwned,here,Option.bind,and_assoc] using ok
    exact ⟨row,List.mem_of_getElem? here,link out.1,out.2.2,
      (o.exactCheck _ _).mp ⟨w.token,out.2.1⟩⟩

theorem read_owned_complete {s o root sh} (real : AuthoredShape s o root sh) :
    ∃ w : OpenWire o, readOwned s o root w = some sh := by
  obtain ⟨row,member,alias,eq,auth⟩ := real
  obtain ⟨n,here⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨wl,chosen⟩ := WhereSites450.alias_wire_from_actual_derivation450 alias
  obtain ⟨wo,checked⟩ := (o.exactCheck _ _).mpr auth
  exact ⟨⟨n,wl,wo⟩,by simp [readOwned,here,Option.bind,chosen,checked,eq]⟩

abbrev MixedPath := List (Address × Nat)

inductive MixedTrail (s : RawSnapshot) (o : OpenOps) : Nat → Expr → MixedPath → Nat → Prop
  | stop : GeneralDeclarativeInspect321.Inspects code → MixedTrail s o root code [] root
  | down : ¬AliasCycle s (observed s) root → AuthoredShape s o root sh →
     ChildAt sh code a child next → MixedTrail s o child next tail site →
     MixedTrail s o root code ((a,child)::tail) site

inductive MixedWire (o : OpenOps) where
  | stop
  | down (owner : OpenWire o) (edge : ChildWire) (clear : ExactEscapeWire)
      (tail : MixedWire o)

def readMixed (s : RawSnapshot) (o : OpenOps) (root : Nat) (code : Expr) :
    MixedWire o → Option (MixedPath × Nat)
  | .stop => if termInspects code then some ([],root) else none
  | .down ow cw clear tail => do
    let shape ← readOwned s o root ow
    let atChild ← readChild cw shape code
    if splitCheck446 s root clear then
      let (rest,last) ← readMixed s o atChild.child atChild.next tail
      some ((atChild.address,atChild.child)::rest,last)
    else none

theorem mixed_trail_in_canonical_visit {s o root code path site}
    (proof : MixedTrail s o root code path site) : Visit (structural s) root code site := by
  induction proof with
  | stop yes => exact .here yes
  | down _ origin child _ ih =>
    obtain ⟨row,member,alias,shape,auth⟩ := origin
    exact checked_child_is_exact_visit_step ⟨row.left,alias,row.right,by cases row; exact member,shape⟩ child ih

theorem checked_mixed_trail_is_actual {s o root code path site} {w : MixedWire o}
    (ok : readMixed s o root code w = some (path,site)) : MixedTrail s o root code path site := by
  induction w generalizing root code path site with
  | stop =>
    by_cases good : termInspects code
    · simp [readMixed,good] at ok
      rcases ok with ⟨rfl,rfl⟩
      exact .stop ((term_inspects_exact455 _).mp good)
    · simp [readMixed,good] at ok
  | down ow cw c tail ih =>
    cases own : readOwned s o root ow with
    | none => simp [readMixed,own,Option.bind] at ok
    | some shape =>
      cases pick : readChild cw shape code with
      | none => simp [readMixed,own,pick,Option.bind] at ok
      | some actual =>
        by_cases clear : splitCheck446 s root c
        · cases next : readMixed s o actual.child actual.next tail with
          | none => simp [readMixed,own,pick,clear,next,Option.bind] at ok
          | some p =>
            rcases p with ⟨rest,last⟩
            simp [readMixed,own,pick,clear,next,Option.bind] at ok
            rcases ok with ⟨rfl,rfl⟩
            exact .down (checked_split_escape_excludes_exact_raw_K2446 clear)
              (read_owned_sound own) actual.valid (ih next)
        · simp [readMixed,own,pick,clear,Option.bind] at ok

theorem actual_mixed_trail_has_finite_wire {s o root code path site}
    (proof : MixedTrail s o root code path site) :
    ∃ w : MixedWire o, readMixed s o root code w = some (path,site) := by
  induction proof with
  | stop good => exact ⟨.stop,by simp [readMixed,(term_inspects_exact455 _).mpr good]⟩
  | @down root sh code a child next tail site safe auth step _ ih =>
    obtain ⟨ow,h⟩ := read_owned_complete auth
    obtain ⟨cw,read⟩ := every_canonical_child_has_its_actual_field_or_ordinal_wire
      (⟨a,child,next,step⟩ : ReadChild sh code)
    obtain ⟨cut,ok,_,_⟩ := (raw_safe_iff_small_witness447 s root).mp safe
    obtain ⟨w,pick⟩ := ih
    exact ⟨.down ow cw cut w,by simp [readMixed,h,read,ok,pick,Option.bind]⟩

structure MixedCycleWire (o : OpenOps) where
  start : MixedWire o
  finish : FieldCycleWire

def readMixedCycle (s : RawSnapshot) (o : OpenOps) (root : Nat) (code : Expr)
    (w : MixedCycleWire o) : Option (MixedPath × Nat) := do
  let q ← readMixed s o root code w.start
  if !(q.1.isEmpty) && checkCycleAt412 s q.2 w.finish then some q else none

theorem mixed_cycle_has_actual_finite_wire (s : RawSnapshot) (o : OpenOps) (root : Nat)
    (code : Expr) (path : MixedPath) (site : Nat) :
    (∃ w : MixedCycleWire o, readMixedCycle s o root code w = some (path,site)) ↔
      MixedTrail s o root code path site ∧ path ≠ [] ∧ AliasCycle s (observed s) site := by
  constructor
  · rintro ⟨w,ok⟩
    cases res : readMixed s o root code w.start with
    | none => simp [readMixedCycle,res,Option.bind] at ok
    | some q =>
      rcases q with ⟨xs,last⟩
      change (readMixed s o root code w.start).bind _ = _ at ok
      rw [res] at ok
      change ((if !xs.isEmpty && checkCycleAt412 s last w.finish then some (xs,last) else none) =
        some (path,site)) at ok
      split at ok
      · rename_i checked
        have eq : xs = path ∧ last = site := by simpa using ok
        rcases eq with ⟨rfl,rfl⟩
        have yes := Bool.and_eq_true_iff.mp checked
        have nz : xs ≠ [] := by simpa using yes.1
        exact ⟨checked_mixed_trail_is_actual res,nz,RecordK2412.cycle_at_sound412 yes.2⟩
      · cases ok
  · rintro ⟨trail,nz,cycle⟩
    obtain ⟨w,pre⟩ := actual_mixed_trail_has_finite_wire trail
    obtain ⟨c,closing⟩ := (naked_raw_cycle_has_finite_wire455 s site).mp cycle
    exact ⟨⟨w,c⟩,by simp [readMixedCycle,pre,nz,closing,Option.bind]⟩

end Yulang.GeneralDeclarativeI65.I72.RecordTraversal455.MixedQA
