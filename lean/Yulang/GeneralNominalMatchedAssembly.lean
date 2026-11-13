import Yulang.GeneralNominalChildAssembly

/-! The remaining ground-root bridge is constructor-wise input matching.
Whole-head mass and actual child production are consequences, not premises. -/
namespace Yulang.GeneralNominalMatchedAssembly
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualInspectionSteps GeneralSourceDictionaries
open GeneralNominalSharedCaptures GeneralNominalCaptureAssembly GeneralNominalGroundAccessibility
open GeneralNominalOriginTerms GeneralNominalFiniteMeaning GeneralNominalHeadMatchMass
open GeneralNominalClosedPatternMass GeneralNominalChildAssembly
open GeneralNominalPatersonLineage (mass)

def CapturedPart (context : GeneralNominalCandidates.Context) (packet : Packet roles)
    (model : GeneralNominalCommonBridge.Assignment) (name : Nat) (term : Expr Nat) : Prop :=
  (¬ Needed packet name ∧ term.leaves = []) ∨ ∃ origin pattern, Usable packet name origin ∧ ClosedTerm context pattern term ∧
    At model .actual origin (denote (fun _ => .bottom) term)


theorem recorded_capture_part (packet : Packet roles) (model : GeneralNominalCommonBridge.Assignment)
    (branch : packet.Holds model) (generation : GenerationGuard state packet)
    (captured : GeneralNominalRecursiveInspection.Capture packet.context.state)
    (member : captured ∈ (inheritedReport packet).captures)
    (recorded : captured.origin = some origin) (closed : ClosedTerm context pattern term)
    (meaning : At model .actual origin (denote (fun _ => .bottom) term)) :
    CapturedPart context packet model captured.name term := by
  by_cases needed : Needed packet captured.name
  · obtain ⟨representative,usable⟩ := generation captured.name needed
    obtain ⟨other,found,agree⟩ := usable.1.2 captured member rfl
    have same : other = origin := Option.some.inj (found.symm.trans recorded)
    subst other
    exact Or.inr ⟨representative,pattern,usable,closed,
      GeneralNominalSimultaneousCaptures.at_same meaning (GeneralNominalOriginTerms.same_symm (agree model branch))⟩
  · exact Or.inl ⟨needed,closed.2.1⟩

inductive Aligned (relation : α → β → Prop) : List α → List β → Prop
  | nil : Aligned relation [] []
  | cons : relation first last → Aligned relation rest tail → Aligned relation (first :: rest) (last :: tail)

theorem closed_weight_positive (term : Expr Nat) (closed : term.leaves = []) : 1 ≤ weight term := by
  cases term with
  | leaf => simp [Expr.leaves] at closed
  | node test children =>
    cases test with
    | scalar => simp [weight,GeneralNominalCompoundReadback.quote,queryMass]
    | nominal => simp [weight,GeneralNominalCompoundReadback.quote,queryMass]
    | structural shape => cases shape <;> simp [weight,GeneralNominalCompoundReadback.quote,queryMass] <;> omega

def HeadMatches (context : GeneralNominalCandidates.Context) (packet : Packet roles)
    (model : GeneralNominalCommonBridge.Assignment) (labels : List Pattern) : Prop :=
  Aligned (fun pattern label => ∃ term, ClosedTerm context label term ∧
    Matches (CapturedPart context packet model)
      (GeneralNominalInspection.translate context.state.constructors context.interpretation pattern) term)
    (normalizeArgs packet.declaration.head) labels

theorem matches_complete (matched : Matches relation query term) : Complete query := by
  induction matched with
  | capture | scalar => simp only [Complete]
  | structural shape queries children matched ih =>
    simp only [Complete]
    intro query member
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
    exact ih index
  | nominal name count queries children matched ih =>
    simp only [Complete]
    intro query member
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
    exact ih index

theorem captured_mass (ready : Ready context packet model capture)
    (part : CapturedPart context packet model name term) :
    (normalize (capture name)).encode.size ≤ weight term := by
  rcases part with ⟨unused,closed⟩ | ⟨origin,pattern,usable,closed,meaning⟩
  · rw [ready.2.1 name unused]
    simpa only [normalize,Pattern.encode,Roles.Term.size] using closed_weight_positive term closed
  · by_cases needed : Needed packet name
    · have bound := (ready.2.2 name needed).2 origin usable pattern term closed meaning
      rw [closed_mass closed] at bound
      simpa only [mass,counted,normalizeArgs,encodeArgs,Roles.argsSize,Nat.add_zero] using bound
    · rw [ready.2.1 name needed]
      simpa only [normalize,Pattern.encode,Roles.Term.size] using closed_weight_positive term closed.2.1

theorem list_mass (matched : Aligned (fun pattern label => ∃ term, ClosedTerm context label term ∧
      Matches (CapturedPart context packet model)
        (GeneralNominalInspection.translate context.state.constructors context.interpretation pattern) term) patterns labels)
    (covered : coveredArgs patterns = true) (ready : Ready context packet model capture) :
    mass (substArgs capture patterns) ≤ mass labels := by
  induction matched with
  | nil => exact Nat.le_refl _
  | @cons pattern label patterns labels known matched ih =>
    have parts : GeneralDeclarationPatterns.covered pattern = true ∧ coveredArgs patterns = true := by
      simpa only [coveredArgs,Bool.and_eq_true] using covered
    obtain ⟨term,closed,matchHead⟩ := known
    have head := instantiated_bound pattern parts.1 (matches_complete matchHead) closed matchHead capture
      (fun _ _ part => captured_mass ready part)
    have tail := ih parts.2
    simp only [mass,counted,substArgs,normalizeArgs,encodeArgs,Roles.argsSize,Nat.add_zero] at head tail ⊢
    exact Nat.add_le_add head tail

theorem head_mass (matched : HeadMatches context packet model labels)
    (nonempty : packet.declaration.requirements ≠ []) (ready : Ready context packet model capture) :
    mass (substArgs capture (normalizeArgs packet.declaration.head)) ≤ mass labels := by
  obtain ⟨clause,present⟩ := List.exists_mem_of_ne_nil _ nonempty
  exact list_mass matched (packet.checked.countsCovered clause present).1 ready

def ReachableHeadMatching (roles : Roles.RoleDecls) (registry : Registry)
    (context : GeneralNominalCandidates.Context) (root : Occurrence roles) : Prop :=
  ∀ (state : Tracked roles) (packet : Packet roles) (support : List (Occurrence roles)),
    B4Target.Steps (Step registry root) (initial context root) state →
    state.current.context.state.constructors = context.state.constructors →
    state.current.context.interpretation = context.interpretation →
    GeneralNominalFeedbackSteps.Installable registry state.current packet →
    PacketGuard state packet support → packet.declaration.requirements ≠ [] →
    ∀ model, Models state.current model → packet.Holds model →
    ∀ labels, Inputs context model packet.site labels → HeadMatches context packet model labels

theorem assembly_of_matching (matching : ReachableHeadMatching roles registry context root) :
    NormalizedCaptureAssembly roles registry context root := by
  intro state packet support trace constructors interpretation enabled guard nonempty model valid branch labels inputs capture ready
  refine ⟨head_mass (matching state packet support trace constructors interpretation enabled guard nonempty model valid branch labels inputs)
    nonempty ready,?_⟩
  intro clause present signature
  exact children state.current packet enabled (by rw [enabled.1.2.1]; exact constructors)
    (by rw [enabled.1.2.1]; exact interpretation) branch guard.1.2.2.1 ready clause present signature

theorem ground_accessible_of_matching (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (point : GeneralNominalActualBudget.PointSource context root)
    (ground : GroundRoots context root rootLabels)
    (matching : ReachableHeadMatching roles registry context root) :
    Acc (fun next current => Step registry root current next) (initial context root) :=
  ground_accessible_of_assembly checked source point ground (assembly_of_matching matching)

end Yulang.GeneralNominalMatchedAssembly
