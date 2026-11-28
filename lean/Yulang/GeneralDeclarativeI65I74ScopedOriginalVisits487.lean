import Yulang.GeneralDeclarativeI65I74AutomaticPaletteEntry486

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open ObservationAlternatives473 (Positions graphOf)
open Producer479 (Site Trail)
open LiteralVisits473 (StepWire)
open QuotientObservation471 (ReturnsUpToEquality)

structure OriginalVisitPrefix487 (n : Nat) where
  argument : Nat
  root : Fin n
  moves : List StepWire
  visited : List (Fin n)

def OriginalVisitPrefix487.withNext {n : Nat} (p : OriginalVisitPrefix487 n)
    (a : StepWire) (i : Fin n) : OriginalVisitPrefix487 n :=
  ⟨p.argument,p.root,p.moves++[a],p.visited++[i]⟩

def OriginalVisitPrefix487.key {n : Nat} (p : OriginalVisitPrefix487 n) : CandidateVisitKey485 n :=
  ⟨p.argument,p.moves.map (fun w => (w.action,w.written)),p.root::p.visited⟩

def originalSuffixPermitted487 {n : Nat} (allow : CandidateVisitKey485 n → Bool) :
    OriginalVisitPrefix487 n → List StepWire → List (Fin n) → Bool
  | _,[],[] => true
  | head,a::acts,i::steps =>
    let extended := head.withNext a i
    allow extended.key && originalSuffixPermitted487 allow extended acts steps
  | _,_,_ => false

/-- Only authorized proper prefixes are evaluated beyond the current
site. A missing checked sign on such a anchor is not a safe result. -/
def enumeratePermittedOldSuffixes487 {n : Nat} {s : GeneralDeclarativeI65.State}
    {pos : Positions n} (rel : List (Fin n × Fin n)) (palette : SignedPalette486 n)
    (allow : CandidateVisitKey485 n → Bool) : Nat → OriginalVisitPrefix487 n → Site s pos →
    Option (List (GeometricVisit486 s pos))
  | 0,_,here => (oldObservedSign486 s pos rel palette here.index).map fun b => [⟨[],[],here,b⟩]
  | fuel+1,anchor,here =>
    match oldObservedSign486 s pos rel palette here.index with
    | none => none
    | some true => some [⟨[],[],here,true⟩]
    | some false => do
      let levels ← (finiteExistingHops486 here).mapM fun pair =>
        let extended := anchor.withNext pair.1 pair.2.index
        if allow extended.key then
          (enumeratePermittedOldSuffixes487 rel palette allow fuel extended pair.2).map
            (List.map fun suffix => ⟨pair.1::suffix.moves,pair.2.index::suffix.points,suffix.last,suffix.bit⟩)
        else some []
      pure (⟨[],[],here,false⟩ :: levels.flatten)

private theorem every_value_of_a_successful_mapM_is_linked_to_some_input
    {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (formed : xs.mapM (m := Option) f = some ys) (y : β) (inside : y ∈ ys) :
    ∃ x ∈ xs, f x = some y := by
  induction xs generalizing ys with
  | nil =>
    have empty : [] = ys := Option.some.inj formed
    subst ys
    cases inside
  | cons a tail ih =>
    cases onHead : f a with
    | none => simp [List.mapM_cons,onHead] at formed
    | some head =>
      cases onTail : tail.mapM (m := Option) f with
      | none => simp [List.mapM_cons,onHead,onTail] at formed
      | some rest =>
        have all : head::rest = ys := Option.some.inj (by simpa [List.mapM_cons,onHead,onTail] using formed)
        subst ys
        rcases List.mem_cons.mp inside with same|past
        · exact ⟨a,List.mem_cons_self ..,same ▸ onHead⟩
        · obtain ⟨here,member,original⟩ := ih onTail past
          exact ⟨here,List.mem_cons_of_mem _ member,original⟩

theorem every_computed_suffix_stays_in_the_original_prior_authorized_domain487
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n} {allow : CandidateVisitKey485 n → Bool}
    (fuel : Nat) (p : OriginalVisitPrefix487 n) (here : Site s pos) (v : GeometricVisit486 s pos)
    {xs : List (GeometricVisit486 s pos)}
    (made : enumeratePermittedOldSuffixes487 rel palette allow fuel p here = some xs) (found : v ∈ xs) :
    Trail s pos rel here v.moves v.points v.last v.bit ∧
      originalSuffixPermitted487 allow p v.moves v.points = true := by
  induction fuel generalizing p here v xs with
  | zero =>
    cases signed : oldObservedSign486 s pos rel palette here.index with
    | none => rw [enumeratePermittedOldSuffixes487, signed] at made; contradiction
    | some bit =>
      have only : [⟨[],[],here,bit⟩] = xs := Option.some.inj (by simpa [enumeratePermittedOldSuffixes487,signed] using made)
      subst xs
      have eq := List.mem_singleton.mp found
      subst v
      have exact := old_palette_sign_is_about_its_own_existing_site486 signed
      exact ⟨.stop exact.1 exact.2,rfl⟩
  | succ k ih =>
    cases signed : oldObservedSign486 s pos rel palette here.index with
    | none => rw [enumeratePermittedOldSuffixes487, signed] at made; contradiction
    | some bit =>
      have facts := old_palette_sign_is_about_its_own_existing_site486 signed
      cases bit with
      | true =>
        have only : [⟨[],[],here,true⟩] = xs :=
          Option.some.inj (by simpa [enumeratePermittedOldSuffixes487,signed] using made)
        subst xs
        have eq := List.mem_singleton.mp found
        subst v
        exact ⟨.stop facts.1 facts.2,rfl⟩
      | false =>
        let fold := fun pair : StepWire × Site s pos =>
          let ext := p.withNext pair.1 pair.2.index
          if allow ext.key then
            (enumeratePermittedOldSuffixes487 rel palette allow k ext pair.2).map
              (List.map fun suffix => (⟨pair.1::suffix.moves,pair.2.index::suffix.points,suffix.last,suffix.bit⟩ :
                GeometricVisit486 s pos))
          else some []
        have selection : (do
          let rows ← (finiteExistingHops486 here).mapM fold
          some (⟨[],[],here,false⟩ :: rows.flatten)) = some xs := by
          rw [enumeratePermittedOldSuffixes487,signed] at made
          exact made
        cases h : (finiteExistingHops486 here).mapM fold with
        | none => simp [h] at selection
        | some rows =>
          have only : (⟨[],[],here,false⟩ :: rows.flatten) = xs := Option.some.inj (by simpa [h] using selection)
          subst xs
          rcases List.mem_cons.mp found with fixed|nested
          · subst v
            exact ⟨.stop facts.1 facts.2,rfl⟩
          · obtain ⟨childVisits,visitAt,foundIn⟩ := List.mem_flatten.mp nested
            obtain ⟨⟨a,next⟩,hopAt,use⟩ := every_value_of_a_successful_mapM_is_linked_to_some_input h _ visitAt
            let extended := p.withNext a next.index
            cases permitted : allow extended.key with
            | false =>
              have empty : [] = childVisits := Option.some.inj (by simpa [fold,extended,permitted] using use)
              subst childVisits
              cases foundIn
            | true =>
              cases checked : enumeratePermittedOldSuffixes487 rel palette allow k extended next with
              | none => simp [fold,extended,permitted,checked] at use
              | some suffixes =>
                have exact : suffixes.map (fun suffix =>
                    (⟨a::suffix.moves,next.index::suffix.points,suffix.last,suffix.bit⟩ :
                    GeometricVisit486 s pos)) = childVisits :=
                  Option.some.inj (by simpa [fold,extended,permitted,checked] using use)
                rw [←exact] at foundIn
                obtain ⟨suffix,good,finished⟩ := List.mem_map.mp foundIn
                subst v
                obtain ⟨old,tail⟩ := ih extended next suffix checked good
                obtain ⟨actualHop⟩ := finite_hops_are_exact_existing_written_visits486.mp hopAt
                exact ⟨.step actualHop facts.1 (fun cycle => Bool.false_ne_true (facts.2.mpr cycle)) old,
                  by
                    change (allow extended.key && originalSuffixPermitted487 allow extended suffix.moves suffix.points) = true
                    rw [permitted,tail]; rfl⟩

private theorem successful_mapM_has_each_exact_input
    {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (formed : xs.mapM (m := Option) f = some ys) (x : α) (inside : x ∈ xs) :
    ∃ y ∈ ys, f x = some y := by
  induction xs generalizing ys with
  | nil => cases inside
  | cons a tail ih =>
    cases onHead : f a with
    | none => simp [List.mapM_cons,onHead] at formed
    | some head =>
      cases onTail : tail.mapM (m := Option) f with
      | none => simp [List.mapM_cons,onHead,onTail] at formed
      | some rest =>
        have all : head::rest = ys := Option.some.inj (by simpa [List.mapM_cons,onHead,onTail] using formed)
        subst ys
        rcases List.mem_cons.mp inside with same|past
        · exact ⟨head,List.mem_cons_self ..,same ▸ onHead⟩
        · obtain ⟨here,member,original⟩ := ih onTail past
          exact ⟨here,List.mem_cons_of_mem _ member,original⟩

theorem successful_scoped_enumeration_covers_every_independently_permitted_old_suffix487
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n} {allow : CandidateVisitKey485 n → Bool}
    {first last : Site s pos} {moves points bit}
    (independent : Trail s pos rel first moves points last bit)
    (fuel : Nat) (p : OriginalVisitPrefix487 n) (budget : moves.length ≤ fuel)
    {xs : List (GeometricVisit486 s pos)}
    (made : enumeratePermittedOldSuffixes487 rel palette allow fuel p first = some xs)
    (authorized : originalSuffixPermitted487 allow p moves points = true) :
    (⟨moves,points,last,bit⟩ : GeometricVisit486 s pos) ∈ xs := by
  induction independent generalizing fuel p xs with
  | @stop here ownBit guard sign =>
    have checked : ∃ b, oldObservedSign486 s pos rel palette here.index = some b := by
      cases h : oldObservedSign486 s pos rel palette here.index with
      | none => cases fuel <;> rw [enumeratePermittedOldSuffixes487,h] at made <;> contradiction
      | some b => exact ⟨b,rfl⟩
    obtain ⟨b,h⟩ := checked
    have observed := (old_palette_sign_is_about_its_own_existing_site486 h).2
    have same : b = ownBit := by cases b <;> cases ownBit <;> simp_all
    subst b
    cases fuel with
    | zero =>
      have only : [⟨[],[],here,ownBit⟩] = xs :=
        Option.some.inj (by simpa [enumeratePermittedOldSuffixes487,h] using made)
      subst xs
      exact List.mem_cons_self ..
    | succ k =>
      cases ownBit with
      | true =>
        have only : [⟨[],[],here,true⟩] = xs :=
          Option.some.inj (by simpa [enumeratePermittedOldSuffixes487,h] using made)
        subst xs
        exact List.mem_cons_self ..
      | false =>
        let fold := fun pair : StepWire × Site s pos =>
          let ext := p.withNext pair.1 pair.2.index
          if allow ext.key then
            (enumeratePermittedOldSuffixes487 rel palette allow k ext pair.2).map
              (List.map fun suffix => (⟨pair.1::suffix.moves,pair.2.index::suffix.points,suffix.last,suffix.bit⟩ :
                GeometricVisit486 s pos))
          else some []
        have selection : (do
          let rows ← (finiteExistingHops486 here).mapM fold
          some (⟨[],[],here,false⟩ :: rows.flatten)) = some xs := by
          rw [enumeratePermittedOldSuffixes487,h] at made
          exact made
        cases formation : (finiteExistingHops486 here).mapM fold with
        | none => simp [formation] at selection
        | some rows =>
          have only : (⟨[],[],here,false⟩ :: rows.flatten) = xs :=
            Option.some.inj (by simpa [formation] using selection)
          subst xs
          exact List.mem_cons_self ..
  | @step here next finish w moves points bit hop guard safe tail ih =>
    cases fuel with
    | zero => simp at budget
    | succ k =>
      have h : oldObservedSign486 s pos rel palette here.index = some false := by
        cases ran : oldObservedSign486 s pos rel palette here.index with
        | none => rw [enumeratePermittedOldSuffixes487,ran] at made; contradiction
        | some sign =>
          cases sign with
          | false => rfl
          | true => exact False.elim (safe ((old_palette_sign_is_about_its_own_existing_site486 ran).2.mp rfl))
      let extended := p.withNext w next.index
      have parts : allow extended.key = true ∧
          originalSuffixPermitted487 allow extended moves points = true := by
        exact Bool.and_eq_true_iff.mp authorized
      let fold := fun pair : StepWire × Site s pos =>
        let ext := p.withNext pair.1 pair.2.index
        if allow ext.key then
          (enumeratePermittedOldSuffixes487 rel palette allow k ext pair.2).map
            (List.map fun suffix => (⟨pair.1::suffix.moves,pair.2.index::suffix.points,suffix.last,suffix.bit⟩ :
              GeometricVisit486 s pos))
        else some []
      have selection : (do
        let rows ← (finiteExistingHops486 here).mapM fold
        some (⟨[],[],here,false⟩ :: rows.flatten)) = some xs := by
        rw [enumeratePermittedOldSuffixes487,h] at made
        exact made
      cases formation : (finiteExistingHops486 here).mapM fold with
      | none => simp [formation] at selection
      | some rows =>
        have only : (⟨[],[],here,false⟩ :: rows.flatten) = xs :=
          Option.some.inj (by simpa [formation] using selection)
        subst xs
        obtain ⟨childList,childAt,childRead⟩ := successful_mapM_has_each_exact_input formation (w,next)
          (finite_hops_are_exact_existing_written_visits486.mpr ⟨hop⟩)
        cases ran : enumeratePermittedOldSuffixes487 rel palette allow k extended next with
        | none => simp [fold,extended,parts.1,ran] at childRead
        | some items =>
          have exact : items.map (fun suffix =>
              (⟨w::suffix.moves,next.index::suffix.points,suffix.last,suffix.bit⟩ : GeometricVisit486 s pos)) =
              childList := Option.some.inj (by simpa [fold,extended,parts.1,ran] using childRead)
          have inside := ih k extended (Nat.le_of_succ_le_succ budget) ran parts.2
          apply List.mem_cons_of_mem
          apply List.mem_flatten.mpr
          refine ⟨childList,childAt,?_⟩
          rw [←exact]
          exact List.mem_map.mpr ⟨⟨moves,points,finish,bit⟩,inside,rfl⟩

private theorem can_form_mapM_if_each_input_can_be_read
    {α β : Type} {f : α → Option β} {xs : List α}
    (each : ∀ x ∈ xs, ∃ y, f x = some y) :
    ∃ ys, xs.mapM (m := Option) f = some ys := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons a tail ih =>
    obtain ⟨head,h⟩ := each a (List.mem_cons_self ..)
    obtain ⟨rest,t⟩ := ih (fun x member => each x (List.mem_cons_of_mem _ member))
    exact ⟨head::rest,by simp [List.mapM_cons,h,t]⟩

theorem the_computed_original_palette_has_a_scoped_read_from_each_guarded_root487
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n} {allow : CandidateVisitKey485 n → Bool}
    (complete : CompletePalette486 s pos rel palette)
    (fuel : Nat) (p : OriginalVisitPrefix487 n) (here : Site s pos)
    (guard : LiteralVisits473.GuardedObservationInput s pos rel here.index) :
    ∃ visits, enumeratePermittedOldSuffixes487 rel palette allow fuel p here = some visits := by
  induction fuel generalizing p here with
  | zero =>
    obtain ⟨bit,h⟩ := complete here.index guard
    exact ⟨[⟨[],[],here,bit⟩],by simp [enumeratePermittedOldSuffixes487,h]⟩
  | succ k ih =>
    obtain ⟨bit,h⟩ := complete here.index guard
    cases bit with
    | true => exact ⟨[⟨[],[],here,true⟩],by simp [enumeratePermittedOldSuffixes487,h]⟩
    | false =>
      let fold := fun pair : StepWire × Site s pos =>
        let ext := p.withNext pair.1 pair.2.index
        if allow ext.key then
          (enumeratePermittedOldSuffixes487 rel palette allow k ext pair.2).map
            (List.map fun suffix => (⟨pair.1::suffix.moves,pair.2.index::suffix.points,suffix.last,suffix.bit⟩ :
              GeometricVisit486 s pos))
        else some []
      have all : ∀ pair ∈ finiteExistingHops486 here, ∃ ys, fold pair = some ys := by
        rintro ⟨a,next⟩ found
        let extended := p.withNext a next.index
        cases permission : allow extended.key with
        | false => exact ⟨[],by simp [fold,extended,permission]⟩
        | true =>
          obtain ⟨hop⟩ := finite_hops_are_exact_existing_written_visits486.mp found
          have nextGuard : LiteralVisits473.GuardedObservationInput s pos rel next.index :=
            ⟨guard.1,guard.2.1,guard.2.2.1,guard.2.2.2.1,
              (fun i tail => guard.2.2.2.2.1 i (.cons hop.edge tail)),
              (fun i tail => guard.2.2.2.2.2 i (.cons hop.edge tail))⟩
          obtain ⟨rows,ran⟩ := ih extended next nextGuard
          exact ⟨rows.map (fun suffix => ⟨a::suffix.moves,next.index::suffix.points,suffix.last,suffix.bit⟩),
            by simp [fold,extended,permission,ran]⟩
      obtain ⟨levels,computed⟩ := can_form_mapM_if_each_input_can_be_read all
      apply Exists.intro ((⟨[],[],here,false⟩ : GeometricVisit486 s pos) :: levels.flatten)
      rw [enumeratePermittedOldSuffixes487,h]
      change (do
        let rows ← (finiteExistingHops486 here).mapM fold
        some ((⟨[],[],here,false⟩ : GeometricVisit486 s pos) :: rows.flatten)) = _
      simp [computed]

private theorem if_all_successful_actions_are_exact_their_output_list_is_pure_map
    {α β : Type} {f : α → Option β} {g : α → β} {xs : List α} {ys : List β}
    (formed : xs.mapM (m := Option) f = some ys)
    (each : ∀ x ∈ xs, ∀ y, f x = some y → y = g x) :
    ys = xs.map g := by
  induction xs generalizing ys with
  | nil => exact (Option.some.inj formed).symm
  | cons a tail ih =>
    cases onHead : f a with
    | none => simp [List.mapM_cons,onHead] at formed
    | some head =>
      cases onTail : tail.mapM (m := Option) f with
      | none => simp [List.mapM_cons,onHead,onTail] at formed
      | some rest =>
        have all : head::rest = ys := Option.some.inj (by simpa [List.mapM_cons,onHead,onTail] using formed)
        subst ys
        have fixed := each a (List.mem_cons_self ..) head onHead
        have rem := ih onTail (fun x inTail y exact => each x (List.mem_cons_of_mem _ inTail) y exact)
        simp [fixed,rem]

theorem successful_scoped_suffixes_are_exactly_the_ordered_original_geometry_filter487
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n} {allow : CandidateVisitKey485 n → Bool}
    (fuel : Nat) (p : OriginalVisitPrefix487 n) (here : Site s pos)
    {xs : List (GeometricVisit486 s pos)}
    (made : enumeratePermittedOldSuffixes487 rel palette allow fuel p here = some xs) :
    xs = (enumerateGuardedGeometry486 rel palette fuel here).filter
      (fun v => originalSuffixPermitted487 allow p v.moves v.points) := by
  induction fuel generalizing p here xs with
  | zero =>
    cases h : oldObservedSign486 s pos rel palette here.index with
    | none => rw [enumeratePermittedOldSuffixes487,h] at made; contradiction
    | some b => simpa [enumeratePermittedOldSuffixes487,enumerateGuardedGeometry486,h,List.filter_cons,List.filter_nil,originalSuffixPermitted487] using made.symm
  | succ k ih =>
    cases h : oldObservedSign486 s pos rel palette here.index with
    | none => rw [enumeratePermittedOldSuffixes487,h] at made; contradiction
    | some b =>
      cases b with
      | true => simpa [enumeratePermittedOldSuffixes487,enumerateGuardedGeometry486,h,List.filter_cons,List.filter_nil,originalSuffixPermitted487] using made.symm
      | false =>
        let fold := fun pair : StepWire × Site s pos =>
          let ext := p.withNext pair.1 pair.2.index
          if allow ext.key then
            (enumeratePermittedOldSuffixes487 rel palette allow k ext pair.2).map
              (List.map fun suffix => (⟨pair.1::suffix.moves,pair.2.index::suffix.points,suffix.last,suffix.bit⟩ :
                GeometricVisit486 s pos))
          else some []
        let expected := fun pair : StepWire × Site s pos =>
          ((enumerateGuardedGeometry486 rel palette k pair.2).map
            (fun v => (⟨pair.1::v.moves,pair.2.index::v.points,v.last,v.bit⟩ : GeometricVisit486 s pos))).filter
            (fun v => originalSuffixPermitted487 allow p v.moves v.points)
        have selection : (do
          let rows ← (finiteExistingHops486 here).mapM fold
          some (⟨[],[],here,false⟩ :: rows.flatten)) = some xs := by
          rw [enumeratePermittedOldSuffixes487,h] at made
          exact made
        cases formation : (finiteExistingHops486 here).mapM fold with
        | none => simp [formation] at selection
        | some rows =>
          have only : (⟨[],[],here,false⟩ :: rows.flatten) = xs :=
            Option.some.inj (by simpa [formation] using selection)
          subst xs
          have one : ∀ pair ∈ finiteExistingHops486 here, ∀ z, fold pair = some z → z = expected pair := by
            rintro ⟨w,next⟩ _ z read
            let extended := p.withNext w next.index
            cases permitted : allow extended.key with
            | false =>
              have empty : [] = z := Option.some.inj (by simpa [fold,extended,permitted] using read)
              subst z
              simp only [expected,List.filter_map,Function.comp_def,originalSuffixPermitted487]
              change [] = (((enumerateGuardedGeometry486 rel palette k next).filter
                  (fun v => allow extended.key && originalSuffixPermitted487 allow extended v.moves v.points)).map _)
              simp [permitted]
            | true =>
              cases there : enumeratePermittedOldSuffixes487 rel palette allow k extended next with
              | none => simp [fold,extended,permitted,there] at read
              | some suffixes =>
                have fixed := ih extended next there
                have exact : suffixes.map (fun v =>
                    (⟨w::v.moves,next.index::v.points,v.last,v.bit⟩ : GeometricVisit486 s pos)) = z :=
                  Option.some.inj (by simpa [fold,extended,permitted,there] using read)
                rw [←exact,fixed]
                simp only [expected,List.filter_map,Function.comp_def,originalSuffixPermitted487]
                change _ = (((enumerateGuardedGeometry486 rel palette k next).filter
                  (fun v => allow extended.key && originalSuffixPermitted487 allow extended v.moves v.points)).map _)
                simp [permitted]
          have fixed := if_all_successful_actions_are_exact_their_output_list_is_pure_map formation one
          rw [fixed]
          rw [enumerateGuardedGeometry486,h]
          simp only [List.filter_cons,originalSuffixPermitted487,ite_true, List.filter_flatMap]
          rfl

def OriginalVisitPrefix487.withSuffix {n : Nat} (p : OriginalVisitPrefix487 n)
    (moves : List StepWire) (points : List (Fin n)) : OriginalVisitPrefix487 n :=
  ⟨p.argument,p.root,p.moves++moves,p.visited++points⟩

private theorem original_withNext_withSuffix_eq {n : Nat} (p : OriginalVisitPrefix487 n)
    (a : StepWire) (point : Fin n) (moves : List StepWire) (points : List (Fin n)) :
    (p.withNext a point).withSuffix moves points = p.withSuffix (a::moves) (point::points) := by
  simp [OriginalVisitPrefix487.withNext,OriginalVisitPrefix487.withSuffix,List.append_assoc]

theorem an_approved_suffix_has_its_exact_terminal_permission487
    {n : Nat} (allow : CandidateVisitKey485 n → Bool)
    (p : OriginalVisitPrefix487 n) (moves : List StepWire) (points : List (Fin n))
    (proper : moves ≠ []) (allowed : originalSuffixPermitted487 allow p moves points = true) :
    allow (p.withSuffix moves points).key = true := by
  induction moves generalizing p points with
  | nil => exact False.elim (proper rfl)
  | cons a tail ih =>
    cases points with
    | nil => contradiction
    | cons point remaining =>
      rw [←original_withNext_withSuffix_eq]
      let next := p.withNext a point
      have yes : allow next.key = true ∧ originalSuffixPermitted487 allow next tail remaining = true :=
        Bool.and_eq_true_iff.mp allowed
      cases tail with
      | nil =>
        cases remaining with
        | nil =>
          have fixed : next.withSuffix [] [] = next := by
            cases next
            simp [OriginalVisitPrefix487.withSuffix]
          rw [fixed]
          exact yes.1
        | cons _ _ => exact False.elim (Bool.false_ne_true yes.2)
      | cons b rest => exact ih next remaining (List.cons_ne_nil b rest) yes.2

def finitePermitFirstPlan487 {n : Nat} {s : GeneralDeclarativeI65.State}
    {pos : Positions n} (rel : List (Fin n × Fin n)) (palette : SignedPalette486 n)
    (argument : Nat) (first : Site s pos) (permit : CandidateVisitKey485 n → Bool) :
    Option (List (CandidateVisitKey485 n)) :=
  (enumeratePermittedOldSuffixes487 rel palette permit (originalNodeBudget486 first.pattern)
    ⟨argument,first.index,[],[]⟩ first).map fun visits =>
      visits.filterMap fun visit =>
        if visit.moves.isEmpty then none else some (exactGeometryKey486 argument first visit)

private theorem original_visit_prefix_starts_from_exact_geometry_key
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    (argument : Nat) (first : Site s pos) (v : GeometricVisit486 s pos) :
    ((⟨argument,first.index,[],[]⟩ : OriginalVisitPrefix487 n).withSuffix v.moves v.points).key =
      exactGeometryKey486 argument first v := rfl

private theorem filterMap_congr_original_geometry {α β : Type}
    (xs : List α) (f g : α → Option β) (eq : ∀ x ∈ xs, f x = g x) :
    xs.filterMap f = xs.filterMap g := by
  induction xs with
  | nil => rfl
  | cons a tail ih =>
    have head := eq a (List.mem_cons_self ..)
    have rest := ih (fun x h => eq x (List.mem_cons_of_mem _ h))
    simp only [List.filterMap_cons,head,rest]

theorem same_order_geometry_agrees_when_terminal_permission_implies_prefix_permission487
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n} {rel : List (Fin n × Fin n)}
    {palette : SignedPalette486 n} {argument : Nat} {first : Site s pos}
    {permit : CandidateVisitKey485 n → Bool} {keys : List (CandidateVisitKey485 n)}
    (ran : finitePermitFirstPlan487 rel palette argument first permit = some keys)
    (prefixClosed : ∀ v ∈ enumerateGuardedGeometry486 rel palette (originalNodeBudget486 first.pattern) first,
      v.moves ≠ [] → permit (exactGeometryKey486 argument first v) = true →
      originalSuffixPermitted487 permit ⟨argument,first.index,[],[]⟩ v.moves v.points = true) :
    keys = finiteAuthorizedVisitPlan486 rel palette argument first permit := by
  cases made : enumeratePermittedOldSuffixes487 rel palette permit (originalNodeBudget486 first.pattern)
    ⟨argument,first.index,[],[]⟩ first with
  | none => simp [finitePermitFirstPlan487,made] at ran
  | some visits =>
    have fixed : visits.filterMap (fun v =>
        if v.moves.isEmpty then none else some (exactGeometryKey486 argument first v)) = keys :=
      Option.some.inj (by simpa [finitePermitFirstPlan487,made] using ran)
    subst keys
    rw [successful_scoped_suffixes_are_exactly_the_ordered_original_geometry_filter487 _ _ _ made]
    unfold finiteAuthorizedVisitPlan486
    rw [List.filterMap_filter]
    apply filterMap_congr_original_geometry
    intro v found
    cases moves : v.moves with
    | nil => simp
    | cons a later =>
      have proper : v.moves ≠ [] := by simp [moves]
      have both : originalSuffixPermitted487 permit ⟨argument,first.index,[],[]⟩ v.moves v.points =
          permit (exactGeometryKey486 argument first v) := by
        apply Bool.eq_iff_iff.mpr
        constructor
        · intro bound
          have was := an_approved_suffix_has_its_exact_terminal_permission487 _ _ _ _ proper bound
          simp only [original_visit_prefix_starts_from_exact_geometry_key] at was
          exact was
        · exact prefixClosed v found proper
      rw [moves] at both
      cases flag : permit (exactGeometryKey486 argument first v) <;> simp [both,flag]

private theorem mapM_congr_on_exact_inputs487
    {α β : Type} {f g : α → Option β} {xs : List α}
    (same : ∀ x ∈ xs, f x = g x) :
    xs.mapM (m := Option) f = xs.mapM (m := Option) g := by
  induction xs with
  | nil => rfl
  | cons a tail ih =>
    rw [List.mapM_cons,List.mapM_cons,same a (List.mem_cons_self ..)]
    rw [ih (fun x h => same x (List.mem_cons_of_mem _ h))]

theorem successful_permitted_search_reads_only_its_produced_checkpoint_positions487
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {left right : SignedPalette486 n}
    {allow : CandidateVisitKey485 n → Bool}
    (fuel : Nat) (p : OriginalVisitPrefix487 n) (here : Site s pos)
    {xs : List (GeometricVisit486 s pos)}
    (made : enumeratePermittedOldSuffixes487 rel left allow fuel p here = some xs)
    (same : ∀ v ∈ xs, oldObservedSign486 s pos rel left v.last.index =
      oldObservedSign486 s pos rel right v.last.index) :
    enumeratePermittedOldSuffixes487 rel right allow fuel p here = some xs := by
  induction fuel generalizing p here xs with
  | zero =>
    cases h : oldObservedSign486 s pos rel left here.index with
    | none => rw [enumeratePermittedOldSuffixes487,h] at made; contradiction
    | some b =>
      rw [enumeratePermittedOldSuffixes487,h] at made
      have fixed : [⟨[],[],here,b⟩] = xs := Option.some.inj made
      subst xs
      have h' := same ⟨[],[],here,b⟩ (List.mem_cons_self ..)
      rw [enumeratePermittedOldSuffixes487,←h',h]
      rfl
  | succ k ih =>
    cases h : oldObservedSign486 s pos rel left here.index with
    | none => rw [enumeratePermittedOldSuffixes487,h] at made; contradiction
    | some b =>
      cases b with
      | true =>
        rw [enumeratePermittedOldSuffixes487,h] at made
        have fixed : [⟨[],[],here,true⟩] = xs := Option.some.inj made
        subst xs
        have h' := same ⟨[],[],here,true⟩ (List.mem_cons_self ..)
        rw [enumeratePermittedOldSuffixes487,←h',h]
      | false =>
        let fold := fun palette (pair : StepWire × Site s pos) =>
          let ext := p.withNext pair.1 pair.2.index
          if allow ext.key then
            (enumeratePermittedOldSuffixes487 rel palette allow k ext pair.2).map
              (List.map fun suffix => (⟨pair.1::suffix.moves,pair.2.index::suffix.points,suffix.last,suffix.bit⟩ :
                GeometricVisit486 s pos))
          else some []
        have selection : (do
          let rows ← (finiteExistingHops486 here).mapM (fold left)
          some (⟨[],[],here,false⟩ :: rows.flatten)) = some xs := by
          rw [enumeratePermittedOldSuffixes487,h] at made
          exact made
        cases formation : (finiteExistingHops486 here).mapM (fold left) with
        | none => simp [formation] at selection
        | some rows =>
          have only : (⟨[],[],here,false⟩ :: rows.flatten) = xs :=
            Option.some.inj (by simpa [formation] using selection)
          subst xs
          have h' := same ⟨[],[],here,false⟩ (List.mem_cons_self ..)
          have readBoth : ∀ pair ∈ finiteExistingHops486 here, fold left pair = fold right pair := by
            rintro ⟨w,next⟩ arrived
            let ext := p.withNext w next.index
            cases permit : allow ext.key with
            | false => simp [fold,ext,permit]
            | true =>
              obtain ⟨ys,found,cooked⟩ := successful_mapM_has_each_exact_input formation (w,next) arrived
              cases read : enumeratePermittedOldSuffixes487 rel left allow k ext next with
              | none => simp [fold,ext,permit,read] at cooked
              | some inner =>
                let lift := fun v : GeometricVisit486 s pos =>
                  (⟨w::v.moves,next.index::v.points,v.last,v.bit⟩ : GeometricVisit486 s pos)
                have shape : inner.map lift = ys :=
                  Option.some.inj (by simpa [fold,ext,permit,read,lift] using cooked)
                have perPosition : ∀ v ∈ inner,
                    oldObservedSign486 s pos rel left v.last.index =
                      oldObservedSign486 s pos rel right v.last.index := by
                  intro v atInner
                  have inY : lift v ∈ ys := shape ▸ List.mem_map.mpr ⟨v,atInner,rfl⟩
                  exact same (lift v) (List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨ys,found,inY⟩))
                have nextRead := ih ext next read perPosition
                simp [fold,ext,permit,read,nextRead]
          have other := (mapM_congr_on_exact_inputs487 readBoth).symm.trans formation
          rw [enumeratePermittedOldSuffixes487,←h',h]
          change (do
            let rest ← (finiteExistingHops486 here).mapM (fold right)
            some ((⟨[],[],here,false⟩ : GeometricVisit486 s pos) :: rest.flatten)) =
              some (⟨[],[],here,false⟩ :: rows.flatten)
          simp [other]

theorem narrowing_prior_permissions_cannot_make_a_successful_old_read_unknown487
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    {wide into : CandidateVisitKey485 n → Bool}
    (narrower : ∀ key, into key = true → wide key = true)
    (fuel : Nat) (p : OriginalVisitPrefix487 n) (here : Site s pos)
    {xs : List (GeometricVisit486 s pos)}
    (made : enumeratePermittedOldSuffixes487 rel palette wide fuel p here = some xs) :
    ∃ ys, enumeratePermittedOldSuffixes487 rel palette into fuel p here = some ys := by
  induction fuel generalizing p here xs with
  | zero => exact ⟨xs,made⟩
  | succ k ih =>
    cases signed : oldObservedSign486 s pos rel palette here.index with
    | none => rw [enumeratePermittedOldSuffixes487,signed] at made; contradiction
    | some bit =>
      cases bit with
      | true =>
        have both : enumeratePermittedOldSuffixes487 rel palette into (k+1) p here = some [⟨[],[],here,true⟩] := by
          rw [enumeratePermittedOldSuffixes487,signed]
        exact ⟨_,both⟩
      | false =>
        let fold := fun (allow : CandidateVisitKey485 n → Bool) (pair : StepWire × Site s pos) =>
          let ext := p.withNext pair.1 pair.2.index
          if allow ext.key then
            (enumeratePermittedOldSuffixes487 rel palette allow k ext pair.2).map
              (List.map fun suffix => (⟨pair.1::suffix.moves,pair.2.index::suffix.points,suffix.last,suffix.bit⟩ :
                GeometricVisit486 s pos))
          else some []
        have selection : (do
          let rows ← (finiteExistingHops486 here).mapM (fold wide)
          some (⟨[],[],here,false⟩ :: rows.flatten)) = some xs := by
          rw [enumeratePermittedOldSuffixes487,signed] at made
          exact made
        cases formation : (finiteExistingHops486 here).mapM (fold wide) with
        | none => simp [formation] at selection
        | some rows =>
          have all : ∀ pair ∈ finiteExistingHops486 here, ∃ out, fold into pair = some out := by
            rintro ⟨w,next⟩ arrived
            let ext := p.withNext w next.index
            cases permit : into ext.key with
            | false => exact ⟨[],by simp [fold,ext,permit]⟩
            | true =>
              have old := narrower ext.key permit
              obtain ⟨ys,_,cooked⟩ := successful_mapM_has_each_exact_input formation (w,next) arrived
              cases read : enumeratePermittedOldSuffixes487 rel palette wide k ext next with
              | none => simp [fold,ext,old,read] at cooked
              | some inner =>
                obtain ⟨other,checked⟩ := ih ext next read
                exact ⟨other.map (fun v => ⟨w::v.moves,next.index::v.points,v.last,v.bit⟩),
                  by simp [fold,ext,permit,checked]⟩
          obtain ⟨result,every⟩ := can_form_mapM_if_each_input_can_be_read all
          refine ⟨(⟨[],[],here,false⟩ : GeometricVisit486 s pos) :: result.flatten,?_⟩
          rw [enumeratePermittedOldSuffixes487,signed]
          change (do
            let rest ← (finiteExistingHops486 here).mapM (fold into)
            some ((⟨[],[],here,false⟩ : GeometricVisit486 s pos) :: rest.flatten)) = _
          simp [every]

private theorem expanding_single_permissions_preserves_suffix_permission487
    {n : Nat} {wide into : CandidateVisitKey485 n → Bool}
    (narrower : ∀ key, into key = true → wide key = true)
    (p : OriginalVisitPrefix487 n) (moves : List StepWire) (points : List (Fin n)) :
    originalSuffixPermitted487 into p moves points = true →
      originalSuffixPermitted487 wide p moves points = true := by
  induction moves generalizing p points with
  | nil => cases points <;> simp [originalSuffixPermitted487]
  | cons w rest ih =>
    cases points with
    | nil => simp [originalSuffixPermitted487]
    | cons t tail =>
      simp only [originalSuffixPermitted487,Bool.and_eq_true]
      exact fun h => ⟨narrower _ h.1,ih (p.withNext w t) tail h.2⟩

theorem a_narrower_permitted_read_is_the_exact_original_subsequence487
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    {wide into : CandidateVisitKey485 n → Bool}
    (narrower : ∀ key, into key = true → wide key = true)
    (fuel : Nat) (p : OriginalVisitPrefix487 n) (here : Site s pos)
    {xs : List (GeometricVisit486 s pos)}
    (made : enumeratePermittedOldSuffixes487 rel palette wide fuel p here = some xs) :
    enumeratePermittedOldSuffixes487 rel palette into fuel p here =
      some (xs.filter (fun v => originalSuffixPermitted487 into p v.moves v.points)) := by
  obtain ⟨ys,ran⟩ := narrowing_prior_permissions_cannot_make_a_successful_old_read_unknown487 narrower fuel p here made
  have left := successful_scoped_suffixes_are_exactly_the_ordered_original_geometry_filter487 fuel p here made
  have right := successful_scoped_suffixes_are_exactly_the_ordered_original_geometry_filter487 fuel p here ran
  rw [ran,left,Option.some.injEq,right,List.filter_filter]
  apply List.filter_congr
  intro v _
  cases h : originalSuffixPermitted487 into p v.moves v.points
  · simp
  · simp [expanding_single_permissions_preserves_suffix_permission487 narrower p v.moves v.points h]

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
