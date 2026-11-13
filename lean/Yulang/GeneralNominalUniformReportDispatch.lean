import Yulang.GeneralNominalUniformInspectionInputs

/-! Every capture in both endpoint reports has a uniform labelled subtree,
or an actual report fragment exposes a surviving hole. The fragment retains
inspected positions even when an optional root origin is absent. -/
namespace Yulang.GeneralNominalUniformReportDispatch
open GeneralDeclarationPatterns GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query Bounds)
open GeneralNominalOriginTerms GeneralNominalHoleElimination GeneralNominalOpenPatternLabels
open GeneralNominalSourcePatternParts GeneralNominalUniformInspectionInputs GeneralNominalInspectionAlignment
open GeneralNominalOpenInspectionMatching (Constructor)

variable {models : GeneralNominalCommonBridge.Assignment → Prop}
variable {values : GeneralNominalCommonBridge.Assignment → Nat → CommonNominalFullCarrier.Ty}
variable {allowed : Pattern → Prop} {queryScope : Query → Prop}

inductive Fragment : Report state → Report state → Prop
  | refl : Fragment report report
  | visit : Fragment report (report.visit bounds origin test)
  | left {first last : Report state} : Fragment first (first.append last)
  | right {first last : Report state} : Fragment last (first.append last)
  | trans : Fragment first middle → Fragment middle last → Fragment first last

theorem fragment_fields (fragment : Fragment first last) :
    first.captures ⊆ last.captures ∧ first.inspected ⊆ last.inspected ∧
      first.anchors ⊆ last.anchors ∧ first.tests ⊆ last.tests := by
  induction fragment with
  | refl => exact ⟨List.Subset.refl _,List.Subset.refl _,List.Subset.refl _,List.Subset.refl _⟩
  | visit => exact ⟨List.Subset.refl _,fun _ member => List.mem_cons_of_mem _ member,
      List.subset_append_right ..,List.subset_append_right ..⟩
  | left => exact ⟨List.subset_append_left ..,List.subset_append_left ..,List.subset_append_left ..,List.subset_append_left ..⟩
  | right => exact ⟨List.subset_append_right ..,List.subset_append_right ..,List.subset_append_right ..,List.subset_append_right ..⟩
  | trans _ _ one two => exact ⟨one.1.trans two.1,one.2.1.trans two.2.1,one.2.2.1.trans two.2.2.1,one.2.2.2.trans two.2.2.2⟩

def Sourced (context : GeneralNominalCandidates.Context) (remaining : List Nat) (allowed : Pattern → Prop)
    (pattern : Pattern) (term : Expr Nat) : Prop :=
  Label context pattern term ∧ Closed remaining term ∧ allowed pattern

def Captures (context : GeneralNominalCandidates.Context) (remaining : List Nat) (allowed : Pattern → Prop)
    (models : GeneralNominalCommonBridge.Assignment → Prop)
    (values : GeneralNominalCommonBridge.Assignment → Nat → CommonNominalFullCarrier.Ty) (report : Report state) : Prop :=
  ∀ captured ∈ report.captures, ∃ pattern term, Sourced context remaining allowed pattern term ∧
    Input models values state captured.bounds captured.origin term

def Exposed (models : GeneralNominalCommonBridge.Assignment → Prop)
    (values : GeneralNominalCommonBridge.Assignment → Nat → CommonNominalFullCarrier.Ty)
    (queryScope : Query → Prop) (report : Report state) (hole : Nat) : Prop :=
  ∃ query bounds origin, queryScope query ∧ Constructor query ∧ Finished (inspect state query bounds origin) ∧
    Fragment (inspect state query bounds origin) report ∧ Input models values state bounds origin (.leaf hole)

theorem exposed_lift (exposed : Exposed models values queryScope first hole) (fragment : Fragment first last) :
    Exposed models values queryScope last hole := by
  obtain ⟨query,bounds,origin,tracked,constructor,finished,inside,known⟩ := exposed
  exact ⟨query,bounds,origin,tracked,constructor,finished,.trans inside fragment,known⟩

theorem captures_visit (known : Captures context remaining allowed models values report) :
    Captures context remaining allowed models values (report.visit bounds origin test) := known

theorem captures_append (first : Captures context remaining allowed models values one)
    (last : Captures context remaining allowed models values two) :
    Captures context remaining allowed models values (one.append two) := by
  intro capture member
  rcases List.mem_append.mp member with member | member
  · exact first capture member
  · exact last capture member

theorem child_sources
    (hereditary : ∀ first last, Part first last → allowed first → allowed last)
    (source : Sourced context remaining allowed pattern (.node test children)) :
    ∀ term ∈ List.ofFn children, ∃ label, Sourced context remaining allowed label term := by
  intro term member
  obtain ⟨position,rfl⟩ := List.mem_ofFn.mp member
  obtain ⟨label,part,known⟩ := GeneralNominalOpenReification.child_source_label source.1 position
  exact ⟨label,known,GeneralNominalOpenCaptureLabels.child_closed source.2.1 position,hereditary _ _ part source.2.2⟩

mutual
  theorem inspect_dispatch (state : GeneralNominalState.State)
      (inhabited : ∃ model, models model)
      (valid : ∀ model, models model → GeneralNominalState.Models state model)
      (hereditary : ∀ first last, Part first last → allowed first → allowed last)
      (queryChildren : ∀ parent child, child ∈ GeneralNominalSourcePatternParts.queryChildren parent → queryScope parent → queryScope child)
      (query : Query) (bounds : Bounds state) (origin : Option Origin) (term : Expr Nat)
      (tracked : queryScope query) (finished : Finished (inspect state query bounds origin))
      (known : Input models values state bounds origin term)
      (source : Sourced context remaining allowed pattern term) :
      Captures context remaining allowed models values (inspect state query bounds origin) ∨
        ∃ hole ∈ remaining, Exposed models values queryScope (inspect state query bounds origin) hole := by
    cases query with
    | variables names =>
      left
      intro captured member
      simp only [inspect] at member
      obtain ⟨name,present,rfl⟩ := List.mem_map.mp member
      exact ⟨pattern,term,source,known⟩
    | deferred => simp only [inspect,Finished,block] at finished; cases finished.1
    | scalar base =>
      by_cases leaf : ∃ hole, term = .leaf hole
      · obtain ⟨hole,rfl⟩ := leaf
        exact Or.inr ⟨hole,source.2.1 hole (List.mem_singleton_self _),.scalar base,bounds,origin,tracked,trivial,finished,.refl,known⟩
      · left
        simp only [inspect]
        split
        · intro captured member; cases member
        · split
          · split <;> intro captured member <;> cases member
          · intro captured member; cases member
          · intro captured member; cases member
    | node shape queries =>
      by_cases leaf : ∃ hole, term = .leaf hole
      · obtain ⟨hole,rfl⟩ := leaf
        exact Or.inr ⟨hole,source.2.1 hole (List.mem_singleton_self _),.node shape queries,bounds,origin,tracked,trivial,finished,.refl,known⟩
      · have explicit : ∀ name, term ≠ .leaf name := fun name equal => leaf ⟨name,equal⟩
        simp only [inspect,finished_visit] at finished
        split at finished
        · rename_i lowerKind lower upperKind upper lowerAt upperAt
          split at finished
          · rename_i shapes
            obtain ⟨children,equal,inputs⟩ := structural_inputs state inhabited valid bounds lowerKind upperKind lower upper
              lowerAt upperAt shapes.1 shapes.2 known explicit
            have sources := child_sources hereditary (equal ▸ source)
            have result := many_dispatch state inhabited valid hereditary queryChildren queries _ _ 0 _
              (fun q mem => queryChildren (.node shape queries) q mem tracked) finished inputs sources
            have report : inspect state (.node shape queries) bounds origin =
                (inspectMany state queries ((List.ofFn lower).zip (List.ofFn upper))
                  (fun index => origin.map fun parent => .structural parent shape index) 0).visit bounds origin (.structural shape) := by
              simp only [inspect,lowerAt,upperAt,shapes,and_self,ite_true]
            rw [report]
            rcases result with captures | ⟨hole,present,exposed⟩
            · exact Or.inl (captures_visit captures)
            · exact Or.inr ⟨hole,present,exposed_lift exposed .visit⟩
          · simp only [Finished,block] at finished; cases finished.1
        · simp only [Finished] at finished; cases finished.2.1
        · simp only [Finished,block] at finished; cases finished.1
    | nominal name queries =>
      by_cases leaf : ∃ hole, term = .leaf hole
      · obtain ⟨hole,rfl⟩ := leaf
        exact Or.inr ⟨hole,source.2.1 hole (List.mem_singleton_self _),.nominal name queries,bounds,origin,tracked,trivial,finished,.refl,known⟩
      · have explicit : ∀ name, term ≠ .leaf name := fun name equal => leaf ⟨name,equal⟩
        simp only [inspect,finished_visit] at finished
        split at finished
        · split at finished <;> simp only [Finished,block] at finished
          all_goals simp at finished
        · rename_i lower lowerAt
          split at finished
          · rename_i lowerName
            split at finished
            · simp only [Finished,block] at finished; cases finished.1
            · rename_i intervals found
              obtain ⟨children,equal,inputs⟩ := nominal_inputs state inhabited valid bounds lower lowerAt found known explicit
              rw [lowerName] at equal inputs
              have sources := child_sources hereditary (equal ▸ source)
              split at finished
              · rename_i point
                have result := many_dispatch state inhabited valid hereditary queryChildren queries intervals _ 0 _
                  (fun q mem => queryChildren (.nominal name queries) q mem tracked) finished inputs sources
                have report : inspect state (.nominal name queries) bounds origin =
                    (inspectMany state queries intervals
                      (fun index => some (.nominal (origin.getD (.source (state.base.source bounds.1))) name index)) 0).visit bounds origin (.nominal name queries.length) := by
                  rw [inspect.eq_def,lowerAt]
                  simp only [lowerName,found,ite_eq_left point,ite_true]
                rw [report]
                rcases result with captures | ⟨hole,present,exposed⟩
                · exact Or.inl (captures_visit captures)
                · exact Or.inr ⟨hole,present,exposed_lift exposed .visit⟩
              · rename_i strict
                split at finished
                · simp only [Finished,block] at finished; cases finished.1
                · rename_i upper upperAt
                  split at finished
                  · rename_i upperName
                    split at finished
                    · simp only [Finished,block] at finished; cases finished.1
                    · rename_i targets located
                      have pieces := (finished_append ..).mp finished
                      obtain ⟨right,rightEq,rightInputs⟩ := nominal_inputs state inhabited valid (bounds.2,bounds.2) upper upperAt located
                        (upper_input state valid bounds lower upper lowerAt upperAt known) explicit
                      rw [upperName] at rightEq rightInputs
                      have rightSources := child_sources hereditary (rightEq ▸ source)
                      have report : inspect state (.nominal name queries) bounds origin =
                          ((inspectMany state queries intervals
                            (fun index => some (.nominal (origin.getD (.source (state.base.source bounds.1))) name index)) 0).append
                          (inspectMany state queries targets
                            (fun index => some (.nominal (origin.getD (.source (state.base.source bounds.2))) name index)) 0)).visit bounds origin (.nominal name queries.length) := by
                        simp only [inspect,lowerAt,lowerName,found,strict,ite_false,upperAt,upperName,located,ite_true]
                      rw [report]
                      rcases many_dispatch state inhabited valid hereditary queryChildren queries intervals _ 0 _
                        (fun q mem => queryChildren (.nominal name queries) q mem tracked) pieces.1 inputs sources with one | ⟨hole,present,exposed⟩
                      · rcases many_dispatch state inhabited valid hereditary queryChildren queries targets _ 0 _
                          (fun q mem => queryChildren (.nominal name queries) q mem tracked) pieces.2 rightInputs rightSources with two | ⟨hole,present,exposed⟩
                        · exact Or.inl (captures_visit (captures_append one two))
                        · exact Or.inr ⟨hole,present,exposed_lift exposed (.trans .right .visit)⟩
                      · exact Or.inr ⟨hole,present,exposed_lift exposed (.trans .left .visit)⟩
                  · simp only [Finished] at finished; cases finished.2.1
          · simp only [Finished] at finished; cases finished.2.1
    termination_by sizeOf query

  theorem many_dispatch (state : GeneralNominalState.State)
      (inhabited : ∃ model, models model)
      (valid : ∀ model, models model → GeneralNominalState.Models state model)
      (hereditary : ∀ first last, Part first last → allowed first → allowed last)
      (queryChildren : ∀ parent child, child ∈ GeneralNominalSourcePatternParts.queryChildren parent → queryScope parent → queryScope child)
      (queries : List Query) (bounds : List (Bounds state)) (origins : Nat → Option Origin) (offset : Nat)
      (terms : List (Expr Nat)) (tracked : ∀ query ∈ queries, queryScope query) (finished : Finished (inspectMany state queries bounds origins offset))
      (known : InputsAt models values state origins offset bounds terms)
      (sources : ∀ term ∈ terms, ∃ pattern, Sourced context remaining allowed pattern term) :
      Captures context remaining allowed models values (inspectMany state queries bounds origins offset) ∨
        ∃ hole ∈ remaining, Exposed models values queryScope (inspectMany state queries bounds origins offset) hole := by
    cases queries with
    | nil =>
      cases bounds with
      | nil => exact Or.inl (by intro captured member; simp only [inspectMany] at member; cases member)
      | cons => simp only [inspectMany,Finished] at finished; cases finished.2.2
    | cons query rest =>
      cases bounds with
      | nil => simp only [inspectMany,Finished] at finished; cases finished.2.2
      | cons bounds tail =>
        cases terms with
        | nil => obtain ⟨model,present⟩ := inhabited; exact False.elim (known model present)
        | cons term terms =>
          simp only [inspectMany,finished_append] at finished
          have pieces := finished
          rw [inspectMany]
          obtain ⟨pattern,source⟩ := sources term (List.mem_cons_self ..)
          have first := inspect_dispatch state inhabited valid hereditary queryChildren query bounds (origins offset) term
            (tracked query (List.mem_cons_self ..)) pieces.1
            (fun model present => (known model present).1) source
          rcases first with one | ⟨hole,present,exposed⟩
          · have later := many_dispatch state inhabited valid hereditary queryChildren rest tail origins (offset+1) terms
              (fun q mem => tracked q (List.mem_cons_of_mem _ mem)) pieces.2
              (fun model present => (known model present).2) (fun t member => sources t (List.mem_cons_of_mem _ member))
            rcases later with two | ⟨hole,present,exposed⟩
            · exact Or.inl (captures_append one two)
            · exact Or.inr ⟨hole,present,exposed_lift exposed .right⟩
          · exact Or.inr ⟨hole,present,exposed_lift exposed .left⟩
    termination_by sizeOf queries
end

end Yulang.GeneralNominalUniformReportDispatch
