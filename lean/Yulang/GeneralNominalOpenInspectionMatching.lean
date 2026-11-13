import Yulang.GeneralNominalOpenInspectionPositions

/-! A successful real inspection either matches the explicit finite tree or
reaches an opaque leaf. The latter conclusion retains the actual subreport,
interval, origin and semantic value; it is not a hole elimination certificate. -/
namespace Yulang.GeneralNominalOpenInspectionMatching
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query Bounds)
open GeneralNominalOriginTerms GeneralNominalFiniteMeaning GeneralNominalReadbackFunctionality
open GeneralNominalHeadMatchMass GeneralNominalInspectionAlignment
open GeneralNominalOpenInspectionPositions GeneralNominalOpenInspectionValues
open GeneralNominalInspectionPositions (structural_matched nominal_matched zip_reindex)

def Subreport (first last : Report state) : Prop :=
  first.captures ⊆ last.captures ∧ first.tests ⊆ last.tests

def Captured (values : Nat → CommonNominalFullCarrier.Ty) (model : GeneralNominalCommonBridge.Assignment)
    (report : Report state) (name : Nat) (term : Expr Nat) : Prop :=
  ∃ bounds origin, (⟨name,bounds,origin⟩ : Capture state) ∈ report.captures ∧
    Input values model state bounds origin term

def Constructor : Query → Prop
  | .scalar _ | .node _ _ | .nominal _ _ => True
  | _ => False

def Exposed (values : Nat → CommonNominalFullCarrier.Ty) (model : GeneralNominalCommonBridge.Assignment)
    (report : Report state) (hole : Nat) : Prop :=
  ∃ query bounds origin, Constructor query ∧ Finished (inspect state query bounds origin) ∧
    Subreport (inspect state query bounds origin) report ∧ Input values model state bounds origin (.leaf hole)

theorem subreport_trans (first : Subreport a b) (last : Subreport b c) : Subreport a c :=
  ⟨fun _ member => last.1 (first.1 member), fun _ member => last.2 (first.2 member)⟩

theorem visit_subreport (bounds : Bounds state) (origin : Option Origin) (test : Test) (report : Report state) :
    Subreport report (report.visit bounds origin test) :=
  ⟨fun _ member => member, fun _ member => List.mem_append_right _ member⟩

theorem child_leaf (member : part ∈ List.ofFn (children : Fin (arity test) → Expr Nat))
    (present : hole ∈ part.leaves) : hole ∈ (Expr.node test children).leaves := by
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
  exact List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨index,rfl⟩,present⟩

theorem nominal_left_report (state : GeneralNominalState.State) (queries : List Query) (bounds : Bounds state)
    (origin : Option Origin) (finished : Finished (inspect state (.nominal name queries) bounds origin)) :
    ∃ descriptor intervals, state.nominals bounds.1 = some descriptor ∧ descriptor.declaration.name = name ∧
      typeArguments descriptor.arguments = some intervals ∧
      Finished (inspectMany state queries intervals
        (fun index => some (.nominal (origin.getD (.source (state.base.source bounds.1))) name index)) 0) ∧
      Subreport (inspectMany state queries intervals
        (fun index => some (.nominal (origin.getD (.source (state.base.source bounds.1))) name index)) 0) (inspect state (.nominal name queries) bounds origin) := by
  simp only [inspect,finished_visit] at finished
  split at finished
  · split at finished <;> simp only [Finished,block] at finished
    all_goals simp at finished
  · rename_i descriptor recorded
    split at finished
    · rename_i same
      split at finished
      · simp only [Finished,block] at finished; cases finished.1
      · rename_i intervals found
        refine ⟨descriptor,intervals,recorded,same,found,?_⟩
        split at finished
        · rename_i point
          refine ⟨finished,?_⟩
          rw [inspect.eq_def,recorded]
          simp only [same,found,ite_eq_left point,ite_true,Report.visit,Subreport]
          exact ⟨fun _ h => h, fun _ h => List.mem_append_right _ h⟩
        · rename_i strict
          split at finished
          · simp only [Finished,block] at finished; cases finished.1
          · rename_i upper upperAt
            split at finished
            · rename_i upperName
              split at finished
              · simp only [Finished,block] at finished; cases finished.1
              · rename_i targets upperArgs
                refine ⟨(finished_append ..).mp finished |>.1,?_⟩
                simp only [inspect,recorded,same,found,strict,ite_false,upperAt,upperName,upperArgs,ite_true,Report.visit,Report.append,Subreport]
                exact ⟨List.subset_append_left ..,fun _ h => List.mem_append_right _ (List.mem_append_left _ h)⟩
            · simp only [Finished] at finished; cases finished.2.1
    · simp only [Finished] at finished; cases finished.2.1

mutual
  theorem inspect_matched_or_exposed (state : GeneralNominalState.State)
      (model : GeneralNominalCommonBridge.Assignment) (values : Nat → CommonNominalFullCarrier.Ty)
      (report : Report state) (valid : GeneralNominalState.Models state model)
      (query : Query) (bounds : Bounds state) (origin : Option Origin) (term : Expr Nat)
      (single : Single query) (finished : Finished (inspect state query bounds origin))
      (known : Input values model state bounds origin term)
      (included : Subreport (inspect state query bounds origin) report) :
      Matches (Captured values model report) query term ∨ ∃ hole ∈ term.leaves, Exposed values model report hole := by
    cases query with
    | variables names =>
      simp only [Single] at single
      obtain ⟨name,rfl⟩ := single
      exact Or.inl (.capture ⟨bounds,origin,included.1 (by simp [inspect]),known⟩)
    | deferred => simp only [inspect,Finished,block] at finished; cases finished.1
    | scalar base =>
      by_cases leaf : ∃ hole, term = .leaf hole
      · obtain ⟨hole,rfl⟩ := leaf
        exact Or.inr ⟨hole,List.mem_singleton_self _,.scalar base,bounds,origin,True.intro,finished,included,known⟩
      · have explicit : ∀ name, term ≠ .leaf name := fun name equal => leaf ⟨name,equal⟩
        simp only [inspect,finished_visit] at finished
        split at finished
        · simp only [Finished] at finished; cases finished.2.1
        · split at finished
          · rename_i actual recorded
            split at finished
            · rename_i same
              have equal := GeneralNominalInspectionFiniteValues.scalar_slot state model valid bounds.1 recorded
              rw [← same] at equal
              obtain ⟨children,identical⟩ := scalar_open values term explicit
                (CommonNominalFullCarrier.subtype_trans equal.2 known.2.1.1)
              rw [identical]
              exact Or.inl (.scalar children)
            · simp only [Finished] at finished; cases finished.2.1
          · simp only [Finished] at finished; cases finished.2.1
          · simp only [Finished,block] at finished; cases finished.1
    | node shape queries =>
      by_cases leaf : ∃ hole, term = .leaf hole
      · obtain ⟨hole,rfl⟩ := leaf
        exact Or.inr ⟨hole,List.mem_singleton_self _,.node shape queries,bounds,origin,True.intro,finished,included,known⟩
      · have explicit : ∀ name, term ≠ .leaf name := fun name equal => leaf ⟨name,equal⟩
        simp only [Single] at single
        simp only [inspect,finished_visit] at finished
        split at finished
        · rename_i lowerKind lower upperKind upper lowerAt upperAt
          split at finished
          · rename_i same
            obtain ⟨children,equal,childInputs⟩ := structural_inputs state model valid bounds
              lowerKind upperKind lower upper lowerAt upperAt same.1 same.2 known explicit
            have childIncluded : Subreport (inspectMany state queries ((List.ofFn lower).zip (List.ofFn upper))
                (fun index => origin.map fun parent => .structural parent shape index) 0) report := by
              have parent := included
              simp only [inspect,lowerAt,upperAt,same,and_self,ite_true] at parent
              exact subreport_trans (visit_subreport bounds origin (.structural shape) _) parent
            have result := many_matched_or_exposed state model values report valid queries _ _ 0 _ single finished childInputs childIncluded
            rcases result with matched | ⟨part,member,hole,present,exposed⟩
            · have length := finished_length state queries _ _ 0 finished
              rw [zip_reindex same.1 same.2,List.length_ofFn] at length
              rw [equal]
              exact Or.inl (structural_matched matched length)
            · exact Or.inr ⟨hole,equal ▸ child_leaf member present,exposed⟩
          · simp only [Finished,block] at finished; cases finished.1
        · simp only [Finished] at finished; cases finished.2.1
        · simp only [Finished,block] at finished; cases finished.1
    | nominal name queries =>
      by_cases leaf : ∃ hole, term = .leaf hole
      · obtain ⟨hole,rfl⟩ := leaf
        exact Or.inr ⟨hole,List.mem_singleton_self _,.nominal name queries,bounds,origin,True.intro,finished,included,known⟩
      · have explicit : ∀ name, term ≠ .leaf name := fun name equal => leaf ⟨name,equal⟩
        simp only [Single] at single
        obtain ⟨descriptor,intervals,recorded,same,found,complete,subset⟩ := nominal_left_report state queries bounds origin finished
        obtain ⟨children,equal,childInputs⟩ := nominal_inputs state model valid bounds descriptor recorded found known explicit
        rw [same] at equal childInputs
        have result := many_matched_or_exposed state model values report valid queries intervals _ 0 _ single complete childInputs
          (subreport_trans subset included)
        rcases result with matched | ⟨part,member,hole,present,exposed⟩
        · rw [equal]
          exact Or.inl (nominal_matched matched (finished_length state queries intervals _ 0 complete))
        · exact Or.inr ⟨hole,equal ▸ child_leaf member present,exposed⟩
    termination_by sizeOf query

  theorem many_matched_or_exposed (state : GeneralNominalState.State)
      (model : GeneralNominalCommonBridge.Assignment) (values : Nat → CommonNominalFullCarrier.Ty)
      (report : Report state) (valid : GeneralNominalState.Models state model)
      (queries : List Query) (bounds : List (Bounds state)) (origins : Nat → Option Origin) (offset : Nat)
      (terms : List (Expr Nat)) (single : ∀ query ∈ queries, Single query)
      (finished : Finished (inspectMany state queries bounds origins offset))
      (known : InputsAt values model state origins offset bounds terms)
      (included : Subreport (inspectMany state queries bounds origins offset) report) :
      GeneralNominalMatchedAssembly.Aligned (Matches (Captured values model report)) queries terms ∨
        ∃ term ∈ terms, ∃ hole ∈ term.leaves, Exposed values model report hole := by
    cases queries with
    | nil =>
      cases bounds with
      | nil => cases terms with
        | nil => exact Or.inl .nil
        | cons => cases known
      | cons => simp only [inspectMany,Finished] at finished; cases finished.2.2
    | cons query rest =>
      cases bounds with
      | nil => simp only [inspectMany,Finished] at finished; cases finished.2.2
      | cons bounds tail =>
        cases terms with
        | nil => cases known
        | cons term terms =>
          simp only [inspectMany,finished_append] at finished
          simp only [inspectMany,Subreport,Report.append] at included
          have first := inspect_matched_or_exposed state model values report valid query bounds (origins offset) term
            (single query (List.mem_cons_self ..)) finished.1 known.1
            ⟨fun _ member => included.1 (List.mem_append_left _ member),fun _ member => included.2 (List.mem_append_left _ member)⟩
          rcases first with matched | ⟨hole,present,exposed⟩
          · have result := many_matched_or_exposed state model values report valid rest tail origins (offset+1) terms
              (fun q member => single q (List.mem_cons_of_mem _ member)) finished.2 known.2
              ⟨fun _ member => included.1 (List.mem_append_right _ member),fun _ member => included.2 (List.mem_append_right _ member)⟩
            rcases result with restMatched | ⟨part,member,hole,present,exposed⟩
            · exact Or.inl (.cons matched restMatched)
            · exact Or.inr ⟨part,List.mem_cons_of_mem _ member,hole,present,exposed⟩
          · exact Or.inr ⟨term,List.mem_cons_self ..,hole,present,exposed⟩
    termination_by sizeOf queries
end

end Yulang.GeneralNominalOpenInspectionMatching
