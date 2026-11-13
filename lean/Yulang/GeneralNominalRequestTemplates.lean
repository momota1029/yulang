import Yulang.GeneralNominalSourceProducerHandoff
import Yulang.GeneralNominalSchemaVocabulary

/-! Constructor templates are extracted from translated source syntax, even
when other branches of that syntax are unsupported. -/
namespace Yulang.GeneralNominalRequestTemplates
open GeneralDeclarationPatterns GeneralNominalInspection GeneralNominalRecursiveInspection
open GeneralNominalOriginTerms GeneralNominalCompoundReadback GeneralNominalReadbackFunctionality
open GeneralNominalOpenPatternLabels GeneralNominalSourceLabelVocabulary
open GeneralNominalScopedRecipeLabels GeneralPatternVariableProvenance
open GeneralNominalSchemaVocabulary GeneralNominalSourcePatternParts

def rootTest : Query → Option Test
  | .scalar base => some (.scalar base)
  | .node shape _ => some (.structural shape)
  | .nominal name children => some (.nominal name children.length)
  | _ => none

theorem vocabularies_flatMap (queries : List Query) :
    vocabularies queries = queries.flatMap vocabulary := by
  induction queries <;> simp_all [vocabularies]

theorem test_source (query : Query) (pattern : Pattern)
    (translated : translate constructors interpretation pattern = query)
    (member : test ∈ vocabulary query) :
    ∃ part, Part pattern part ∧ rootTest (translate constructors interpretation part) = some test := by
  cases query with
  | variables | deferred => cases member
  | scalar base =>
    cases List.mem_singleton.mp member
    exact ⟨pattern,.refl,by rw [translated]; rfl⟩
  | node shape children | nominal name children =>
    rcases List.mem_cons.mp member with same | nested
    · exact ⟨pattern,.refl,by rw [translated,same]; rfl⟩
    · rw [vocabularies_flatMap] at nested
      obtain ⟨child,present,member⟩ := List.mem_flatMap.mp nested
      obtain ⟨part,path,meaning⟩ := GeneralNominalSourcePatternParts.child_source pattern
        (by rw [translated]; exact present) (by intro names equal; subst child; cases member)
      obtain ⟨source,subpath,root⟩ := test_source child part meaning member
      exact ⟨source,part_trans path subpath,root⟩
  termination_by sizeOf query
  decreasing_by all_goals have bound := List.sizeOf_lt_of_mem present; simp_all; omega

def recordPattern (empty : Nat) : List Nat → Nat → Pattern
  | [], _ => .app empty []
  | label :: labels, offset => .record label (.var offset) (recordPattern empty labels (offset+1))

def recordQueries : List Nat → Nat → List Query
  | [], _ => []
  | _ :: labels, offset => .variables [offset] :: recordQueries labels (offset+1)

theorem recordQueries_length (labels : List Nat) (offset : Nat) :
    (recordQueries labels offset).length = labels.length := by
  induction labels generalizing offset <;> simp_all [recordQueries]

theorem record_translation (emptyKnown : interpretation.primitives empty = some .emptyRecord)
    (labels : List Nat) (sorted : labels.Pairwise (· < ·)) (offset : Nat) :
    translate constructors interpretation (recordPattern empty labels offset) =
      .node (.record labels) (recordQueries labels offset) := by
  induction labels generalizing offset with
  | nil => simp [recordPattern,translate,emptyKnown,recordQueries]
  | cons label labels ih =>
    have tail := ih (List.pairwise_cons.mp sorted).2 (offset+1)
    simp only [recordPattern,translate,tail,recordQueries]
    have length := recordQueries_length labels (offset+1)
    have fst : ((label,Query.variables [offset]) :: labels.zip (recordQueries labels (offset+1))).map Prod.fst = label :: labels := by
      simp only [List.map_cons,List.map_fst_zip (Nat.le_of_eq length.symm)]
    have ordered : ((label,Query.variables [offset]) :: labels.zip (recordQueries labels (offset+1))).Pairwise
        (fun a b => decide (a.1 ≤ b.1) = true) := by
      have mapped := sorted.imp (fun h => Nat.le_of_lt h)
      rw [← fst,List.pairwise_map] at mapped
      exact mapped.imp (fun h => decide_eq_true h)
    rw [List.mergeSort_of_pairwise ordered]
    simp only [fst,List.map_cons,List.map_snd_zip (Nat.le_of_eq length)]

theorem record_scoped (known : empty ∈ keys) (labels : List Nat)
    (fields : labels ⊆ keys) (offset : Nat) : Scoped keys (recordPattern empty labels offset) := by
  induction labels generalizing offset with
  | nil => exact .app known (by simp)
  | cons label labels ih =>
    exact .record (fields (List.mem_cons_self ..)) (.var _)
      (ih (fun _ h => fields (List.mem_cons_of_mem _ h)) _)

theorem record_covered (labels : List Nat) (offset : Nat) :
    covered (recordPattern empty labels offset) = true := by
  induction labels generalizing offset <;> simp_all [recordPattern,covered,coveredArgs]

theorem record_uses (labels : List Nat) (offset : Nat) :
    Uses (fun name => offset ≤ name ∧ name < offset + labels.length) (recordPattern empty labels offset) := by
  induction labels generalizing offset with
  | nil => intro name member; cases member
  | cons label labels ih =>
    intro name member
    rcases List.mem_append.mp member with first | rest
    · cases List.mem_singleton.mp first; simp
    · have h := ih (offset+1) name rest
      simp only [List.length_cons]; omega

theorem recordQueries_index (labels : List Nat) (offset : Nat) :
    recordQueries labels offset = List.ofFn (fun i : Fin labels.length => Query.variables [offset+i.val]) := by
  induction labels generalizing offset with
  | nil => rfl
  | cons label labels ih =>
    simp only [recordQueries,List.length_cons,List.ofFn_succ,Fin.val_zero,Nat.add_zero,Fin.val_succ]
    rw [ih]
    congr 2
    funext i
    congr 2
    omega

theorem record_source (pattern : Pattern) (scope : Scoped keys pattern)
    (translated : translate constructors interpretation pattern = .node (.record labels) children) :
    labels ⊆ keys ∧ ∃ empty ∈ keys, interpretation.primitives empty = some .emptyRecord := by
  cases scope with
  | var | variant | join => simp only [translate] at translated; cases translated
  | app keyKnown arguments =>
    rw [translate.eq_def] at translated
    dsimp only at translated
    split at translated
    · cases translated
    · rename_i primitive
      cases translated
      exact ⟨by simp,_,keyKnown,primitive⟩
    · cases translated
    · cases translated
    · split at translated
      · split at translated <;> cases translated
      · cases translated
  | @record key payload tail keyKnown payloadScope tailScope =>
    simp only [translate] at translated
    split at translated
    · rename_i names queries tailQuery
      obtain ⟨fields,empty⟩ := record_source tail tailScope tailQuery
      cases translated
      refine ⟨?_,empty⟩
      intro name member
      obtain ⟨field,present,rfl⟩ := List.mem_map.mp member
      rcases List.mem_cons.mp (List.mem_mergeSort.mp present) with rfl | rest
      · exact keyKnown
      · exact fields (List.of_mem_zip rest).1
    · cases translated
  termination_by sizeOf pattern

theorem record_template (known : empty ∈ keys)
    (emptyKnown : context.interpretation.primitives empty = some .emptyRecord)
    (fields : labels ⊆ keys) (canonical : labels.Pairwise (· < ·)) :
    ∃ pattern, Label context pattern (.node (.structural (.record labels)) (fun i => .leaf i.val)) ∧
      Scoped keys pattern ∧ Uses (fun name => name < labels.length) pattern := by
  refine ⟨recordPattern empty labels 0,⟨record_covered labels 0,?_,canonical,fun _ => trivial⟩,
    record_scoped known labels fields 0,?_⟩
  · rw [record_translation emptyKnown labels canonical,recordQueries_index]
    simp only [Nat.zero_add,quote,arity,GeneralNormalizedObservation.Shape.arity]
  · intro name member
    simpa only [Nat.zero_add] using (record_uses labels 0 name member).2

def variables (count : Nat) : List Pattern := List.ofFn (fun i : Fin count => .var i.val)

theorem variables_covered (count : Nat) : coveredArgs (variables count) = true := by
  have general (patterns : List Pattern) (all : ∀ p ∈ patterns, covered p = true) : coveredArgs patterns = true := by
    induction patterns with
    | nil => rfl
    | cons first rest ih =>
      exact (Bool.and_eq_true ..).mpr ⟨all _ (List.mem_cons_self ..), ih (fun p h => all p (List.mem_cons_of_mem _ h))⟩
  apply general
  intro p member; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member; rfl

theorem variables_scoped (count : Nat) : ∀ p ∈ variables count, Scoped keys p := by
  intro p member; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member; exact .var _

theorem variables_uses (count : Nat) : ∀ name ∈ variablesArgs (variables count), name < count := by
  have general (patterns : List Pattern) (known : ∀ p ∈ patterns, Uses (fun n => n < count) p) :
      ∀ name ∈ variablesArgs patterns, name < count := by
    induction patterns with
    | nil => simp [variablesArgs]
    | cons head tail ih =>
      intro name member
      rcases List.mem_append.mp member with h | h
      · exact known _ (List.mem_cons_self ..) name h
      · exact ih (fun p h => known p (List.mem_cons_of_mem _ h)) name h
  apply general
  intro p member name present
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
  cases List.mem_singleton.mp present
  exact i.isLt

theorem root_template (pattern : Pattern) (scope : Scoped keys pattern)
    (root : rootTest (translate context.state.constructors context.interpretation pattern) = some test)
    (canonical : TestCanonical test) :
    ∃ pattern, Label context pattern (.node test (fun i => .leaf i.val)) ∧
      Scoped keys pattern ∧ Uses (fun name => name < arity test) pattern := by
  cases scope with
  | var | join => simp only [translate,rootTest] at root; cases root
  | @variant tag payload tagKnown payloadScope =>
    simp only [translate,rootTest] at root
    cases root
    refine ⟨.variant tag (.var 0),⟨rfl,?_,canonical,fun _ => trivial⟩,.variant tagKnown (.var _),?_⟩
    · simp [translate,GeneralCandidateInspection.plainNames,quote,List.ofFn_succ,arity,GeneralNormalizedObservation.Shape.arity]
    · intro name member; cases List.mem_singleton.mp member; exact Nat.zero_lt_one
  | @record key payload tail keyKnown payloadScope tailScope =>
    have scope := Scoped.record keyKnown payloadScope tailScope
    simp only [translate] at root
    split at root
    · rename_i labels children tailQuery
      obtain ⟨fields,empty,known,primitive⟩ := record_source (constructors := context.state.constructors) (interpretation := context.interpretation) _ scope
        (by simp only [translate,tailQuery]; rfl)
      cases root
      exact record_template known primitive fields canonical
    · cases root
  | @app key arguments keyKnown argumentScope =>
    rw [translate.eq_def] at root
    dsimp only at root
    split at root
    · rename_i base primitive
      cases root
      exact ⟨.app key [],⟨rfl,by simp [translate,primitive,quote],canonical,fun i => Fin.elim0 i⟩,
        .app keyKnown (by simp),by intro name member; cases member⟩
    · rename_i primitive
      cases root
      exact record_template keyKnown primitive (by simp) canonical
    · rename_i primitive
      cases root
      exact ⟨.app key [],⟨rfl,by simp [translate,primitive,quote,arity,GeneralNormalizedObservation.Shape.arity],canonical,fun i => Fin.elim0 i⟩,
        .app keyKnown (by simp),by intro name member; cases member⟩
    · rename_i first last primitive
      cases root
      refine ⟨.app key [.var 0,.var 1],⟨rfl,?_,canonical,fun _ => trivial⟩,
        .app keyKnown ?_,?_⟩
      · simp [translate,primitive,quote,List.ofFn_succ,arity,GeneralNormalizedObservation.Shape.arity]
      · intro p member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl <;> exact .var _
      · intro name member
        simp only [Pattern.variables,variablesArgs,List.mem_append,List.mem_singleton,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl <;> decide
    · split at root
      · rename_i declaration recorded
        split at root
        · rename_i accepted
          have inv := ((Bool.and_eq_true ..).mp ((Bool.and_eq_true ..).mp accepted).1).1
          have primitive := context.interpretation.disjoint key inv
          simp only [rootTest,List.length_map,List.length_attach] at root
          cases root
          refine ⟨.app key (variables _),⟨variables_covered _,?_,canonical,fun _ => trivial⟩,
            .app keyKnown (variables_scoped _),variables_uses _⟩
          simp only [variables,quote,arity]
          rw [translate.eq_def]
          simp only [primitive,recorded,List.length_ofFn,accepted,ite_true]
          simp only [List.attach_map_val,List.map_ofFn,Function.comp_def,translate]

        · cases root
      · cases root

theorem source_templates (context : GeneralNominalCandidates.Context) (pattern : Pattern)
    (scope : Scoped keys pattern) :
    NodeTemplates context keys (vocabulary (translate context.state.constructors context.interpretation pattern)) := by
  intro test member canonical
  obtain ⟨part,path,root⟩ := test_source _ pattern rfl member
  exact root_template part (part_scoped path scope) root canonical

theorem request_templates (context : GeneralNominalCandidates.Context)
    (requests : List GeneralNominalMaterialization.Request) :
    GeneralNominalSourceProducerHandoff.RequestTemplates context requests := by
  unfold GeneralNominalSourceProducerHandoff.RequestTemplates
  rw [generated_vocabulary]
  intro test member canonical
  obtain ⟨request,present,member⟩ := List.mem_flatMap.mp member
  exact source_templates context (normalize request.pattern)
    (collect_args_scoped _ _ (List.mem_map.mpr ⟨request,present,rfl⟩)) test member canonical

end Yulang.GeneralNominalRequestTemplates
