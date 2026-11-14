import Yulang.GeneralNominalSchemaCapture187

set_option backward.isDefEq.respectTransparency false
/-! Completed actual schema tests retain inspection tests and observation anchors. -/
namespace Yulang.GeneralNominalSchemaTests187
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalInspection (Query Bounds)
open GeneralNominalInspectionAlignment

def Witness (report : Report state) (test : Origin × Test) : Prop :=
  test ∈ report.tests ∧ ∃ bounds, (test.1,bounds) ∈ report.anchors

 theorem visit_root (report : Report state) (bounds : Bounds state) (origin : Origin) (test : Test) :
    Witness (report.visit bounds (some origin) test) (origin,test) := by
  constructor
  · exact List.mem_cons_self ..
  · exact ⟨bounds,List.mem_cons_self ..⟩

 theorem visit_retained (valid : Witness report test) :
    Witness (report.visit bounds origin checked) test :=
  ⟨List.mem_append_right _ valid.1,by obtain ⟨b,h⟩ := valid.2; exact ⟨b,List.mem_append_right _ h⟩⟩

 theorem append_left {first last : Report state} (valid : Witness first test) : Witness (first.append last) test :=
  ⟨List.mem_append_left _ valid.1,by obtain ⟨b,h⟩ := valid.2; exact ⟨b,List.mem_append_left _ h⟩⟩

 theorem append_right {first last : Report state} (valid : Witness last test) : Witness (first.append last) test :=
  ⟨List.mem_append_right _ valid.1,by obtain ⟨b,h⟩ := valid.2; exact ⟨b,List.mem_append_right _ h⟩⟩

mutual
 theorem schema_tests (state : GeneralNominalState.State) (query : Query)
    (bounds : Bounds state) (origin : Origin)
    (finished : Finished (inspect state query bounds (some origin)))
    (test : Origin × Test) (member : test ∈ (schema query origin .actual).tests) :
    Witness (inspect state query bounds (some origin)) test := by
  cases query with
  | variables names => simp [schema] at member
  | deferred reason => simp [schema] at member
  | scalar base =>
    simp only [schema,List.mem_singleton] at member
    subst test
    simp only [inspect]
    exact visit_root _ bounds origin (.scalar base)
  | node shape children =>
    simp only [schema] at member
    rcases List.mem_cons.mp member with sameTest | nested
    · subst test; simp only [inspect]; exact visit_root _ bounds origin (.structural shape)
    · simp only [inspect,finished_visit] at finished
      split at finished
      · rename_i lower childrenBounds upper targets low high
        split at finished
        · rename_i same
          have witnessed := schemas_tests state children _ (fun i => .structural origin shape i) 0 finished test nested
          simp only [inspect,low,high,same,and_self,ite_true,Option.map_some]
          exact visit_retained witnessed
        · simp only [Finished,block] at finished; cases finished.1
      · simp only [Finished] at finished; cases finished.2.1
      · simp only [Finished,block] at finished; cases finished.1
  | nominal key children =>
    simp only [schema] at member
    rcases List.mem_cons.mp member with sameTest | nested
    · subst test; simp only [inspect]; exact visit_root _ bounds origin (.nominal key children.length)
    · simp only [inspect,finished_visit] at finished ⊢
      apply visit_retained
      split at finished <;> try simp_all only
      · split at finished <;> try simp_all only <;> simp only [Finished,block] at finished
        · cases finished.2.1
        · cases finished.2.1
        · cases finished.1
      · split at finished <;> try simp_all only
        · split at finished <;> try simp_all only
          · simp only [Finished,block] at finished; cases finished.1
          · split at finished <;> try simp_all only
            · exact (schemas_tests state children _ (fun i => .nominal origin key i) 0 finished test nested)
            · split at finished <;> try simp_all only
              · simp only [Finished,block] at finished; cases finished.1
              · split at finished <;> try simp_all only
                · split at finished <;> try simp_all only
                  · simp only [Finished,block] at finished; cases finished.1
                  · exact (append_left (schemas_tests state children _ (fun i => .nominal origin key i) 0
                      ((finished_append ..).mp finished).1 test nested))
                · simp only [Finished] at finished; cases finished.2.1
        · simp only [Finished] at finished; cases finished.2.1
 termination_by sizeOf query

 theorem schemas_tests (state : GeneralNominalState.State) (queries : List Query)
    (bounds : List (Bounds state)) (origins : Nat → Origin) (offset : Nat)
    (finished : Finished (inspectMany state queries bounds (fun i => some (origins i)) offset))
    (test : Origin × Test) (member : test ∈ (schemas queries origins .actual offset).tests) :
    Witness (inspectMany state queries bounds (fun i => some (origins i)) offset) test := by
  cases queries with
  | nil => simp [schemas] at member
  | cons query rest => cases bounds with
    | nil => simp only [inspectMany,Finished] at finished; cases finished.2.2
    | cons head tail =>
      simp only [inspectMany] at finished ⊢
      simp only [schemas,Schema.append] at member
      rcases List.mem_append.mp member with first | last
      · exact append_left (schema_tests state query head (origins offset) ((finished_append ..).mp finished).1 test first)
      · exact append_right (schemas_tests state rest tail origins (offset+1) ((finished_append ..).mp finished).2 test last)
 termination_by sizeOf queries
end
end Yulang.GeneralNominalSchemaTests187
