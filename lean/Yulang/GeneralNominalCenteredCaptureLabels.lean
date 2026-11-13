import Yulang.GeneralNominalCenteredHeadMatching

/-! Minimum finite labels for the explicitly named captured values. Syntactic
variable occurrence is recovered from constructor matching by size accounting. -/
namespace Yulang.GeneralNominalCenteredCaptureLabels
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatching GeneralNominalGroundAccessibility
open GeneralNominalOriginTerms GeneralNominalFiniteMeaning GeneralNominalHeadMatchMass
open GeneralNominalMatchedAssembly (Aligned)
open GeneralNominalClosedPatternMass
open GeneralNominalSimultaneousCaptures (closed_normal)
open GeneralNominalPatersonLineage (mass)

mutual
  theorem variable_bound (pattern : Pattern) (substitution : Roles.Subst)
      (member : name ∈ pattern.variables) : (substitution name).size ≤ (pattern.encode.subst substitution).size := by
    cases pattern with
    | var n => cases List.mem_singleton.mp member; exact Nat.le_refl _
    | app key arguments =>
      have bound := variables_bound arguments substitution member
      simp only [Pattern.encode,Roles.Term.subst,Roles.Term.size]
      omega
    | variant tag payload =>
      have bound := variable_bound payload substitution member
      simp only [Pattern.encode,Roles.Term.subst,Roles.Term.size,Roles.substArgs,Roles.argsSize]
      omega
    | record label payload tail | join payload tail =>
      rcases List.mem_append.mp member with first | last
      · have bound := variable_bound payload substitution first
        simp only [Pattern.encode,Roles.Term.subst,Roles.Term.size,Roles.substArgs,Roles.argsSize]
        omega
      · have bound := variable_bound tail substitution last
        simp only [Pattern.encode,Roles.Term.subst,Roles.Term.size,Roles.substArgs,Roles.argsSize]
        omega
    termination_by sizeOf pattern
  theorem variables_bound (patterns : List Pattern) (substitution : Roles.Subst)
      (member : name ∈ variablesArgs patterns) : (substitution name).size ≤ Roles.argsSize (Roles.substArgs substitution (encodeArgs patterns)) := by
    cases patterns with
    | nil => cases member
    | cons head tail =>
      rcases List.mem_append.mp member with first | last
      · have bound := variable_bound head substitution first
        simp only [encodeArgs,Roles.substArgs,Roles.argsSize]
        omega
      · have bound := variables_bound tail substitution last
        simp only [encodeArgs,Roles.substArgs,Roles.argsSize]
        omega
    termination_by sizeOf patterns
end

def large : Nat → Roles.Term
  | 0 => .var 0
  | n+1 => .app 0 [large n]

theorem large_size (n : Nat) : (large n).size = n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [large,Roles.Term.size,Roles.argsSize,ih,Nat.add_comm]

theorem matched_variable (pattern : Pattern) (covered : covered pattern = true)
    (matched : Matches (Part context plan model)
      (GeneralNominalInspection.translate context.state.constructors context.interpretation pattern) term)
    (member : name ∈ pattern.variables) : ∃ value, Part context plan model name value := by
  classical
  apply Classical.byContradiction
  intro absent
  let substitution : Roles.Subst := fun n => if n = name then large (weight term) else .var n
  have lower := variable_bound pattern substitution member
  rw [translated_count pattern covered (GeneralNominalMatchedAssembly.matches_complete matched) substitution] at lower
  have upper := matched_mass matched (capture := fun n => (substitution n).size) (by
    intro n value known
    have different : n ≠ name := by intro same; subst n; exact absent ⟨value,known⟩
    simpa only [substitution,different,ite_false,Roles.Term.size] using
      GeneralNominalMatchedAssembly.closed_weight_positive value known.choose_spec.1.2.1)
  have tooLarge : (substitution name).size = weight term+1 := by simp [substitution,large_size]
  omega

theorem aligned_variable
    (matched : Aligned (fun pattern label => ∃ term, ClosedTerm context label term ∧
      Matches (Part context plan model)
        (GeneralNominalInspection.translate context.state.constructors context.interpretation pattern) term) patterns labels)
    (covered : coveredArgs patterns = true) (member : name ∈ variablesArgs patterns) :
    ∃ value, Part context plan model name value := by
  induction matched with
  | nil => cases member
  | @cons pattern label patterns labels known matched ih =>
    have parts : GeneralDeclarationPatterns.covered pattern = true ∧ coveredArgs patterns = true :=
      (Bool.and_eq_true ..).mp covered
    rcases List.mem_append.mp member with first | last
    · obtain ⟨term,_,head⟩ := known
      exact matched_variable pattern parts.1 head first
    · exact ih parts.2 last

def Meaning (context : GeneralNominalCandidates.Context) (plan : Plan roles)
    (model : GeneralNominalCommonBridge.Assignment) (name : Nat) (pattern : Pattern) : Prop :=
  ∃ term, ClosedTerm context pattern term ∧
    At model .actual (.source (plan.binder name)) (denote (fun _ => .bottom) term)

private theorem least (predicate : Nat → Prop) (nonempty : ∃ value, predicate value) :
    ∃ value, predicate value ∧ ∀ other, predicate other → value ≤ other := by
  classical
  obtain ⟨value,present⟩ := nonempty
  induction value using Nat.strongRecOn with
  | ind value ih =>
    by_cases smaller : ∃ other, other < value ∧ predicate other
    · obtain ⟨other,below,known⟩ := smaller
      exact ih other below known
    · exact ⟨value,present,fun other known => by
        by_cases below : value ≤ other
        · exact below
        · exact False.elim (smaller ⟨other,by omega,known⟩)⟩

theorem minimum_label (available : ∃ pattern, Meaning context plan model name pattern) :
    ∃ pattern, normalize pattern = pattern ∧ Meaning context plan model name pattern ∧
      ∀ other, Meaning context plan model name other → mass [pattern] ≤ mass [other] := by
  have nonempty : ∃ size, ∃ pattern, Meaning context plan model name pattern ∧ mass [pattern] = size := by
    obtain ⟨pattern,known⟩ := available
    exact ⟨mass [pattern],pattern,known,rfl⟩
  obtain ⟨size,⟨pattern,⟨term,closed,shared⟩,atSize⟩,minimal⟩ := least _ nonempty
  obtain ⟨fixed,normal,measured⟩ := closed_normal closed
  refine ⟨normalize pattern,fixed,⟨term,normal,shared⟩,?_⟩
  intro other known
  rw [measured,atSize]
  exact minimal (mass [other]) ⟨other,known,rfl⟩

def Ready (context : GeneralNominalCandidates.Context) (plan : Plan roles)
    (model : GeneralNominalCommonBridge.Assignment) (capture : Nat → Pattern) : Prop :=
  (∀ name, normalize (capture name) = capture name) ∧
  (∀ name, ¬ GeneralNominalSharedCaptures.Needed plan.packet name → capture name = .var name) ∧
  ∀ name, GeneralNominalSharedCaptures.Needed plan.packet name →
    Meaning context plan model name (capture name) ∧
      ∀ pattern, Meaning context plan model name pattern → mass [capture name] ≤ mass [pattern]

theorem ready_captures (matched : HeadMatches context plan model labels)
    (_nonempty : plan.packet.declaration.requirements ≠ []) : ∃ capture, Ready context plan model capture := by
  classical
  have witnesses : ∀ name, GeneralNominalSharedCaptures.Needed plan.packet name → ∃ pattern,
      normalize pattern = pattern ∧ Meaning context plan model name pattern ∧
        ∀ other, Meaning context plan model name other → mass [pattern] ≤ mass [other] := by
    intro name needed
    obtain ⟨clause,present,used⟩ := needed
    have declared := plan.packet.checked.scope.1 clause present name used
    obtain ⟨term,pattern,closed,meaning⟩ := aligned_variable matched
      (plan.packet.checked.countsCovered clause present).1 declared
    exact minimum_label ⟨pattern,term,closed,meaning⟩
  let capture := fun name => if needed : GeneralNominalSharedCaptures.Needed plan.packet name
    then Classical.choose (witnesses name needed) else .var name
  refine ⟨capture,?_,?_,?_⟩
  · intro name
    by_cases needed : GeneralNominalSharedCaptures.Needed plan.packet name
    · simpa only [capture,dite_eq_left needed] using (Classical.choose_spec (witnesses name needed)).1
    · simp only [capture,dite_eq_right needed,normalize]
  · intro name unused
    simp only [capture,dite_eq_right unused]
  · intro name needed
    simpa only [capture,dite_eq_left needed] using (Classical.choose_spec (witnesses name needed)).2

theorem captured_mass (ready : Ready context plan model capture) (part : Part context plan model name term) :
    (normalize (capture name)).encode.size ≤ weight term := by
  obtain ⟨pattern,closed,meaning⟩ := part
  by_cases needed : GeneralNominalSharedCaptures.Needed plan.packet name
  · have bound := (ready.2.2 name needed).2 pattern ⟨term,closed,meaning⟩
    rw [closed_mass closed] at bound
    simpa only [mass,counted,normalizeArgs,encodeArgs,Roles.argsSize,Nat.add_zero] using bound
  · rw [ready.2.1 name needed]
    simpa only [normalize,Pattern.encode,Roles.Term.size] using
      GeneralNominalMatchedAssembly.closed_weight_positive term closed.2.1

theorem list_mass (matched : Aligned (fun pattern label => ∃ term, ClosedTerm context label term ∧
      Matches (Part context plan model)
        (GeneralNominalInspection.translate context.state.constructors context.interpretation pattern) term) patterns labels)
    (covered : coveredArgs patterns = true) (ready : Ready context plan model capture) :
    mass (substArgs capture patterns) ≤ mass labels := by
  induction matched with
  | nil => exact Nat.le_refl _
  | @cons pattern label patterns labels known matched ih =>
    have parts : GeneralDeclarationPatterns.covered pattern = true ∧ coveredArgs patterns = true :=
      (Bool.and_eq_true ..).mp covered
    obtain ⟨term,closed,matchHead⟩ := known
    have head := instantiated_bound pattern parts.1 (GeneralNominalMatchedAssembly.matches_complete matchHead)
      closed matchHead capture (fun _ _ part => captured_mass ready part)
    have tail := ih parts.2
    simp only [mass,counted,substArgs,normalizeArgs,encodeArgs,Roles.argsSize,Nat.add_zero] at head tail ⊢
    exact Nat.add_le_add head tail

end Yulang.GeneralNominalCenteredCaptureLabels
