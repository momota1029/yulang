import Yulang.GeneralDictionaryActualSchema

/-! Variable scope follows the actual pattern translator and schema generator.
This removes a schematic variable-name premise from root-output replay. -/
namespace Yulang.GeneralDictionaryActualSchemaScope
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalMaterialization
open GeneralNominalRecursiveInspection GeneralNominalInspection

mutual
  def QueryScoped (allowed : Nat → Prop) : Query → Prop
    | .variables names => ∀ name ∈ names, allowed name
    | .node _ children | .nominal _ children => QueriesScoped allowed children
    | _ => True
  def QueriesScoped (allowed : Nat → Prop) : List Query → Prop
    | [] => True
    | q :: rest => QueryScoped allowed q ∧ QueriesScoped allowed rest
end

theorem queries_scoped_iff (allowed : Nat → Prop) (qs : List Query) :
    QueriesScoped allowed qs ↔ ∀ q ∈ qs, QueryScoped allowed q := by
  induction qs with
  | nil => simp [QueriesScoped]
  | cons q qs ih => simp [QueriesScoped,ih]

theorem query_scoped_mono (a b : Nat → Prop) (imp : ∀ name, a name → b name)
    (q : Query) (h : QueryScoped a q) : QueryScoped b q := by
  cases q with
  | variables names => exact fun n hn => imp n (h n hn)
  | scalar _ => trivial
  | deferred _ => trivial
  | node shape children | nominal shape children =>
    rw [QueryScoped,queries_scoped_iff] at h ⊢
    exact fun child member => query_scoped_mono a b imp child (h child member)
termination_by sizeOf q

mutual
  theorem schema_scoped (allowed : Nat → Prop) (query : Query) (origin : Origin) (mode : Mode)
      (h : QueryScoped allowed query) :
      ∀ entry ∈ (schema query origin mode).variables, allowed entry.name := by
    cases query with
    | variables names =>
      rw [schema]
      intro entry member
      obtain ⟨name,hn,rfl⟩ := List.mem_map.mp member
      exact h name hn
    | scalar base => simp [schema]
    | deferred p => simp [schema]
    | node shape children =>
      simpa only [schema] using schemas_scoped allowed children
        (fun i => .structural origin shape i) mode 0 h
    | nominal name children =>
      simpa only [schema] using schemas_scoped allowed children
        (fun i => .nominal origin name i) .actual 0 h
  termination_by sizeOf query

  theorem schemas_scoped (allowed : Nat → Prop) (qs : List Query) (origins : Nat → Origin)
      (mode : Mode) (index : Nat) (h : QueriesScoped allowed qs) :
      ∀ entry ∈ (schemas qs origins mode index).variables, allowed entry.name := by
    cases qs with
    | nil => simp [schemas]
    | cons q rest =>
      rw [schemas]
      intro entry member
      rcases List.mem_append.mp member with first | last
      · exact schema_scoped allowed q (origins index) mode h.1 entry first
      · exact schemas_scoped allowed rest origins mode (index+1) h.2 entry last
  termination_by sizeOf qs
end

theorem plain_names (p : Pattern) (names : List Nat)
    (h : GeneralCandidateInspection.plainNames p = some names) : names = p.variables := by
  cases p with
  | var n => simpa [GeneralCandidateInspection.plainNames,Pattern.variables] using h.symm
  | app _ _ | record _ _ _ | variant _ _ => simp [GeneralCandidateInspection.plainNames] at h
  | join a b =>
    simp only [GeneralCandidateInspection.plainNames] at h
    cases ha : GeneralCandidateInspection.plainNames a with
    | none => simp [ha] at h
    | some xs =>
      cases hb : GeneralCandidateInspection.plainNames b with
      | none => simp [ha,hb] at h
      | some ys =>
        simp [ha,hb] at h
        subst names
        rw [Pattern.variables,plain_names a xs ha,plain_names b ys hb]
termination_by sizeOf p

theorem variables_args_member (ps : List Pattern) (p : Pattern) (hp : p ∈ ps)
    (name : Nat) (hn : name ∈ p.variables) : name ∈ variablesArgs ps := by
  induction ps with
  | nil => simp at hp
  | cons first rest ih =>
    rcases List.mem_cons.mp hp with rfl | h
    · exact List.mem_append_left _ hn
    · exact List.mem_append_right _ (ih h)

theorem translated_scoped (constructors : Constructors) (interpretation : Interpretation)
    (p : Pattern) : QueryScoped (fun n => n ∈ p.variables) (translate constructors interpretation p) := by
  fun_induction translate constructors interpretation p with
  | case1 n => simp [QueryScoped,Pattern.variables]
  | case2 tag payload ih =>
    cases h : GeneralCandidateInspection.plainNames payload with
    | none => simpa [h,QueryScoped,QueriesScoped,Pattern.variables] using ih
    | some names =>
      simp only [QueryScoped,QueriesScoped,Pattern.variables,and_true]
      intro n member
      rwa [plain_names payload names h] at member
  | case3 key base h => simp [QueryScoped]
  | case4 key h => simp [QueryScoped,QueriesScoped]
  | case5 key h => simp [QueryScoped,QueriesScoped]
  | case6 key first last h ih1 ih2 =>
    simp only [QueryScoped,QueriesScoped,and_true]
    exact ⟨query_scoped_mono _ _ (fun n hn => by exact List.mem_append_left _ hn) _ ih1,
      query_scoped_mono _ _ (fun n hn => by exact List.mem_append_right _ (List.mem_append_left _ hn)) _ ih2⟩
  | case7 key actuals declaration hc good h1 h2 h3 h4 ih =>
    simp only [QueryScoped,queries_scoped_iff]
    intro q member
    obtain ⟨arg,_,rfl⟩ := List.mem_map.mp member
    exact query_scoped_mono _ _ (fun n hn => variables_args_member actuals arg.val arg.property n hn)
      _ (ih arg)
  | case8 key actuals declaration hc bad h1 h2 h3 h4 => trivial
  | case9 key actuals hc h1 h2 h3 h4 => trivial
  | case10 label payload tail labels children ht fields iht ihp =>
    simp only [QueryScoped,queries_scoped_iff]
    intro q member
    obtain ⟨field,hfield,rfl⟩ := List.mem_map.mp member
    have before := List.mem_mergeSort.mp hfield
    rcases List.mem_cons.mp before with rfl | rest
    · exact query_scoped_mono _ _ (fun n hn => List.mem_append_left _ hn) _ ihp
    · have childMember : field.2 ∈ children := (List.of_mem_zip rest).2
      rw [ht,QueryScoped,queries_scoped_iff] at iht
      exact query_scoped_mono _ _ (fun n hn => List.mem_append_right _ hn) _ (iht field.2 childMember)
  | case11 label payload tail no iht =>
    trivial
  | case12 other no1 no2 no3 no4 =>
    trivial
theorem fold_scoped (allowed : Nat → Prop) (ss : List Schema)
    (all : ∀ s ∈ ss, ∀ entry ∈ s.variables, allowed entry.name) :
    ∀ entry ∈ (ss.foldr Schema.append {}).variables, allowed entry.name := by
  induction ss with
  | nil => simp
  | cons s rest ih =>
    intro entry member
    rcases List.mem_append.mp member with first | last
    · exact all s (by simp) entry first
    · exact ih (fun t ht => all t (by simp [ht])) entry last

theorem generated_scoped (allowed : Nat → Prop) (state : GeneralNominalState.State)
    (interpretation : Interpretation) (rs : List Request)
    (scope : ∀ r ∈ rs, ∀ name ∈ (normalize r.pattern).variables, allowed name) :
    ∀ entry ∈ (generated state interpretation rs).variables, allowed entry.name := by
  apply fold_scoped
  intro s member
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp member
  exact schema_scoped allowed _ _ _
    (query_scoped_mono _ _ (scope r hr) _ (translated_scoped _ _ _))

/-- Checked associated equations contain only declared input/output names.
No constructor-pattern restriction is imposed: the translator handles all its
existing structural, primitive, nominal and deferred branches. -/
theorem root_generated_scoped (state : GeneralNominalState.State)
    (interpretation : Interpretation) (declaration : Declaration)
    (root : GeneralSourceDictionaries.Occurrence roles) (scopeCheck : declaration.Scoped) :
    ∀ entry ∈ (generated state interpretation (rootRequests declaration root)).variables,
      entry.name ∈ declaration.inputNames ∨ entry.name ∈ declaration.outputNames := by
  apply generated_scoped (fun n => n ∈ declaration.inputNames ∨ n ∈ declaration.outputNames) state interpretation
  intro r member name hn
  obtain ⟨output,_,member⟩ := List.mem_flatMap.mp member
  obtain ⟨equation,he,rfl⟩ := List.mem_map.mp member
  exact scopeCheck.2.1 equation (List.mem_of_find?_eq_some (Option.mem_toList.mp he)) name hn

/-- Single-input scope is derived from declaration checking rather than assumed
for generated schema entries. Output-only names retain their separate meaning. -/
theorem root_input_name (state : GeneralNominalState.State)
    (interpretation : Interpretation) (declaration : Declaration)
    (root : GeneralSourceDictionaries.Occurrence roles) (scopeCheck : declaration.Scoped)
    (binder : Nat) (names : declaration.inputNames = [binder]) :
    ∀ entry ∈ (generated state interpretation (rootRequests declaration root)).variables,
      entry.name ∉ declaration.outputNames → entry.name = binder := by
  intro entry member notOutput
  have h := root_generated_scoped state interpretation declaration root scopeCheck entry member
  have inside := h.resolve_right notOutput
  simpa [names] using inside

end Yulang.GeneralDictionaryActualSchemaScope
