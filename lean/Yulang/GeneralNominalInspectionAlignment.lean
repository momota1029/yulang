import Yulang.GeneralNominalInspectionFiniteValues

/-! Completion and arity depend on queries and intervals, while inherited
origins retain capture identity. Covered queries have singleton captures. -/
namespace Yulang.GeneralNominalInspectionAlignment
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query Bounds translate)
open GeneralDeclarationPatterns GeneralNominalTemplateSubstitution

def status (report : Report state) := (report.blocked,report.conflicts,report.arity)

theorem status_visit (bounds : Bounds state) (origin : Option Origin) (test : Test) (report : Report state) :
    status (report.visit bounds origin test) = status report := rfl

theorem status_append (one two : Report state) :
    status (one.append two) = ((status one).1 ++ (status two).1,
      (status one).2.1 ++ (status two).2.1,(status one).2.2 ++ (status two).2.2) := rfl

theorem status_append_congr (one : status (a : Report state) = status b) (two : status c = status d) :
    status (a.append c) = status (b.append d) := by rw [status_append,status_append,one,two]

mutual
  theorem inspect_status (state : GeneralNominalState.State) (query : Query) (bounds : Bounds state)
      (first last : Option Origin) : status (inspect state query bounds first) = status (inspect state query bounds last) := by
    cases query with
    | variables | deferred => simp only [inspect,status]
    | scalar => simp only [inspect,status_visit]
    | node shape children =>
      simp only [inspect,status_visit]
      split
      · split
        · exact many_status state children _ _ _ 0 0
        · rfl
      · rfl
      · rfl
    | nominal name children =>
      simp only [inspect,status_visit]
      split
      · split <;> rfl
      · split
        · split
          · rfl
          · split
            · exact many_status state children _ _ _ 0 0
            · split
              · rfl
              · split
                · split
                  · rfl
                  · apply status_append_congr <;> exact many_status state children _ _ _ 0 0
                · rfl
        · rfl
    termination_by sizeOf query
  theorem many_status (state : GeneralNominalState.State) (queries : List Query) (bounds : List (Bounds state))
      (first last : Nat → Option Origin) (one two : Nat) :
      status (inspectMany state queries bounds first one) = status (inspectMany state queries bounds last two) := by
    cases queries with
    | nil => cases bounds <;> simp only [inspectMany]
    | cons query rest =>
      cases bounds with
      | nil => simp only [inspectMany]
      | cons head tail =>
        simp only [inspectMany,status_append,inspect_status state query head (first one) (last two),
          many_status state rest tail first last (one+1) (two+1)]
    termination_by sizeOf queries
end

theorem finished_visit (bounds : Bounds state) (origin : Option Origin) (test : Test) (report : Report state) :
    Finished (report.visit bounds origin test) ↔ Finished report := Iff.rfl

theorem finished_append (first last : Report state) :
    Finished (first.append last) ↔ Finished first ∧ Finished last := by
  simp only [Finished,Report.append,List.append_eq_nil_iff]
  constructor
  · rintro ⟨⟨a,b⟩,⟨c,d⟩,e,f⟩; exact ⟨⟨a,c,e⟩,b,d,f⟩
  · rintro ⟨⟨a,b,c⟩,d,e,f⟩; exact ⟨⟨a,d⟩,⟨b,e⟩,c,f⟩

theorem finished_origins (state : GeneralNominalState.State) (queries : List Query) (bounds : List (Bounds state))
    (first last : Nat → Option Origin) (one two : Nat)
    (finished : Finished (inspectMany state queries bounds first one)) : Finished (inspectMany state queries bounds last two) := by
  have equal := many_status state queries bounds first last one two
  have condition : ∀ report : Report state, Finished report ↔ status report = ([],[],[]) := by
    intro report; simp only [Finished,status,Prod.mk.injEq]
  exact (condition _).mpr (equal ▸ (condition _).mp finished)

theorem finished_length (state : GeneralNominalState.State) (queries : List Query) (bounds : List (Bounds state))
    (origins : Nat → Option Origin) (offset : Nat) (finished : Finished (inspectMany state queries bounds origins offset)) :
    queries.length = bounds.length := by
  induction queries generalizing bounds offset with
  | nil => cases bounds with
    | nil => rfl
    | cons => simp only [inspectMany,Finished] at finished; cases finished.2.2
  | cons query rest ih => cases bounds with
    | nil => simp only [inspectMany,Finished] at finished; cases finished.2.2
    | cons head tail =>
      simp only [inspectMany] at finished
      have parts := (finished_append ..).mp finished
      exact congrArg Nat.succ (ih tail (offset+1) parts.2)

def Single : Query → Prop
  | .variables names => ∃ name, names = [name]
  | .node _ children | .nominal _ children => ∀ query ∈ children, Single query
  | _ => True

mutual
  theorem translated_single (pattern : Pattern) (covered : GeneralDeclarationPatterns.covered pattern = true) :
      Single (translate constructors interpretation pattern) := by
    cases pattern with
    | var name => simp only [translate,Single]; exact ⟨name,rfl⟩
    | join => cases covered
    | variant tag payload =>
      rw [variant_query payload covered]
      simp only [Single]
      intro q member; cases List.mem_singleton.mp member
      exact translated_single payload covered
    | app key arguments =>
      rw [translate.eq_def]
      dsimp only
      split
      · simp only [Single]
      · simp only [Single]; simp
      · simp only [Single]; simp
      · rename_i first last primitive
        have parts : GeneralDeclarationPatterns.covered first = true ∧ GeneralDeclarationPatterns.covered last = true := by
          simpa only [GeneralDeclarationPatterns.covered,coveredArgs,Bool.and_eq_true,and_true] using covered
        simp only [Single]
        intro q member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ translated_single first parts.1
        · cases List.mem_singleton.mp member; exact translated_single last parts.2
      · split
        · split
          · simp only [Single]
            intro q member
            obtain ⟨⟨p,present⟩,_,rfl⟩ := List.mem_map.mp member
            exact translated_single p (GeneralNominalChildAssembly.covered_member _ covered p present)
          · simp only [Single]
        · simp only [Single]
    | record label payload tail =>
      have parts : GeneralDeclarationPatterns.covered payload = true ∧ GeneralDeclarationPatterns.covered tail = true := by
        simpa only [GeneralDeclarationPatterns.covered,Bool.and_eq_true] using covered
      rw [translate.eq_def]
      dsimp only
      split
      · rename_i labels children found
        have rest := translated_single (constructors := constructors) (interpretation := interpretation) tail parts.2
        rw [found] at rest
        simp only [Single] at rest ⊢
        intro q member
        obtain ⟨entry,present,same⟩ := List.mem_map.mp member
        rw [← same]
        rcases List.mem_cons.mp (List.mem_mergeSort.mp present) with first | last
        · exact first ▸ translated_single payload parts.1
        · exact rest entry.2 (List.of_mem_zip last).2
      · simp only [Single]
    termination_by sizeOf pattern
end


theorem nominal_left (state : GeneralNominalState.State) (queries : List Query) (bounds : Bounds state)
    (origin : Option Origin) (finished : Finished (inspect state (.nominal name queries) bounds origin)) :
    ∃ descriptor intervals, state.nominals bounds.1 = some descriptor ∧ descriptor.declaration.name = name ∧
      typeArguments descriptor.arguments = some intervals ∧
      Finished (inspectMany state queries intervals
        (fun index => some (.nominal (origin.getD (.source (state.base.source bounds.1))) name index)) 0) ∧
      (inspectMany state queries intervals
        (fun index => some (.nominal (origin.getD (.source (state.base.source bounds.1))) name index)) 0).captures ⊆
          (inspect state (.nominal name queries) bounds origin).captures := by
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
          simp only [same,found,ite_eq_left point,ite_true,Report.visit]
          exact fun _ h => h
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
                simp only [inspect,recorded,same,found,strict,ite_false,upperAt,upperName,upperArgs,ite_true,Report.visit,Report.append]
                exact List.subset_append_left ..
            · simp only [Finished] at finished; cases finished.2.1
    · simp only [Finished] at finished; cases finished.2.1

end Yulang.GeneralNominalInspectionAlignment
