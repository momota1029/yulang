import Yulang.B4TargetV8
import Yulang.B4SkeletonV7

/-! Reachable-state composition for V8. Evidence and child production are
required at selected nodes only; rejected output or sharing conflicts impose no dictionary
obligation. The remaining twelve operational bridges retain their V5 shape. -/
namespace Yulang.B4SkeletonV8
open CommonRoleOutermostResolver
open B4Target (Vocabulary Steps)
open B4TargetV3 (Executor SameDiagnostic Completed same_diagnostic_refl)
open B4TargetV8
universe u
variable {v : Vocabulary.{u}}

abbrev B4Statement (b : SourceBoundary v) (e : Executor v) : Prop := Statement b e
abbrev Frontiers := B4Skeleton.Frontiers

/-- Model evidence is required only for the saturation root or a genuinely
generated demand, once parent and immediate children are stable in this same
reachable snapshot. Unrelated demands impose no obligation. -/
def EvidenceAt (b : SourceBoundary v) (r : v.Registry) (s : v.State) (root : v.Demand) : Prop :=
  ∀ (model : v.Model),
    b.Models s model → ∀ (d : v.Demand) (key : Nat) (children : List v.Demand)
      (dictionaries : List Dictionary), (d = root ∨ b.Generated r s root d) →
    b.Stable r s d →
    (∀ child, child ∈ children → b.Stable r s child) →
    Local b r s d (.selected key children) →
    All₂ (fun child dictionary => b.Evidence r s model child dictionary) children dictionaries →
    b.Evidence r s model d (.node key dictionaries)

def EvidenceNode (b : SourceBoundary v) : Prop :=
  ∀ (r : v.Registry), b.Checked r → ∀ (s : v.State) (root : v.Demand),
    Reachable b r root s → EvidenceAt b r s root

theorem evidenceAt_of_no_selection {b : SourceBoundary v} {r : v.Registry} {s : v.State} {root : v.Demand}
    (excluded : ∀ d key children, (d = root ∨ b.Generated r s root d) →
      ¬ Local b r s d (.selected key children)) : EvidenceAt b r s root := by
  intro model valid d key children dictionaries reached stable childStable selected evidence
  exact False.elim (excluded d key children reached selected)

/-- One selected edge preserves membership in the saturation root's generated
closure. This is explicit because SourceBoundary imposes no law on Generated.
There is no recursive classification or dictionary-evidence premise here. -/
def GeneratedChildren (b : SourceBoundary v) : Prop :=
  ∀ (r : v.Registry), b.Checked r → ∀ (s : v.State) (root d : v.Demand)
    (key : Nat) (children : List v.Demand), Reachable b r root s →
    (d = root ∨ b.Generated r s root d) → b.Stable r s d →
    Local b r s d (.selected key children) →
    ∀ child, child ∈ children → b.Generated r s root child

mutual
  /-- Every recursive node gets stability from the same saturation closure. -/
  theorem dictionary_evidence (b : SourceBoundary v) (node : EvidenceNode b)
      (generatedChildren : GeneratedChildren b)
      (r : v.Registry) (checked : b.Checked r) (s : v.State) (root : v.Demand) (reachable : Reachable b r root s)
      (rootStable : b.Stable r s root)
      (generatedStable : ∀ child, b.Generated r s root child → b.Stable r s child)
      (model : v.Model) (models : b.Models s model)
      (dictionary : Dictionary) (d : v.Demand)
      (reached : d = root ∨ b.Generated r s root d)
      (derived : Classify b r s d (.selected dictionary)) :
      b.Evidence r s model d dictionary := by
    have stable : b.Stable r s d := by
      rcases reached with same | generated
      · exact same ▸ rootStable
      · exact generatedStable d generated
    cases dictionary with
    | node key dictionaries =>
        cases derived with
        | selected selected children =>
            have childGenerated := generatedChildren r checked s root d key _ reachable reached stable selected
            exact node r checked s root reachable model models d key _ dictionaries reached stable
              (fun child member => generatedStable child (childGenerated child member)) selected
              (dictionaries_evidence b node generatedChildren r checked s root reachable rootStable
                generatedStable model models _ _
                (fun child member => Or.inr (childGenerated child member)) children)
  termination_by sizeOf dictionary

  theorem dictionaries_evidence (b : SourceBoundary v) (node : EvidenceNode b)
      (generatedChildren : GeneratedChildren b)
      (r : v.Registry) (checked : b.Checked r) (s : v.State) (root : v.Demand) (reachable : Reachable b r root s)
      (rootStable : b.Stable r s root)
      (generatedStable : ∀ child, b.Generated r s root child → b.Stable r s child)
      (model : v.Model) (models : b.Models s model)
      (dictionaries : List Dictionary) (demands : List v.Demand)
      (reached : ∀ child, child ∈ demands → child = root ∨ b.Generated r s root child)
      (derived : All₂ (fun d dictionary => Classify b r s d (.selected dictionary))
        demands dictionaries) :
      All₂ (fun d dictionary => b.Evidence r s model d dictionary) demands dictionaries := by
    cases derived with
    | nil => exact .nil
    | cons first rest =>
        exact .cons (dictionary_evidence b node generatedChildren r checked s root reachable rootStable
          generatedStable model models _ _ (reached _ (by simp)) first)
          (dictionaries_evidence b node generatedChildren r checked s root reachable rootStable
            generatedStable model models _ _ (fun child member => reached child (by simp [member])) rest)
  termination_by sizeOf dictionaries
end

/-- Twelve operational laws and two selected-node production laws. -/
structure B4Bridges (b : SourceBoundary v) (e : Executor v) (frontiers : Frontiers v) : Prop where
  progress : ∀ r, b.Checked r → ∀ s d, Reachable b r d s →
    Acc (fun next current => b.Step r d current next) s
  execution : ∀ r, b.Checked r → ∀ s d, Reachable b r d s →
    Steps (b.Step r d) s (e.run r s d).1
  halted : ∀ r, b.Checked r → ∀ s d, Reachable b r d s →
    ∀ next, ¬ b.Step r d (e.run r s d).1 next
  closure : ∀ r, b.Checked r → ∀ s d, Reachable b r d s →
    (∀ next, ¬ b.Step r d s next) →
    b.Stable r s d ∧ ∀ child, b.Generated r s d child → b.Stable r s child
  stepModels : ∀ r, b.Checked r → ∀ d before after, Reachable b r d before →
    b.Step r d before after → ∀ model, b.Models after model → b.Models before model
  frontierLocal : ∀ r, b.Checked r → ∀ s root, Reachable b r root s → ∀ d f,
    (frontiers r s).frontier d = f ↔ Local b r s d f
  localIdentity : ∀ r s root, Reachable b r root s → (frontiers r s).Local = Local b r s
  whereAccessible : ∀ r, b.Checked r → ∀ s root, Reachable b r root s →
    Acc (Child (Local b r s)) root
  treeExecution : ∀ r (_checked : b.Checked r) s d, Reachable b r d s →
    ∀ (exact : FrontierExact (frontiers r (e.run r s d).1))
    (accessible : Acc (Child (frontiers r (e.run r s d).1).Local) d),
    (e.run r s d).2 = resolve (frontiers r (e.run r s d).1) exact d accessible
  canonicalLocalOrder : ∀ r r', b.Checked r → b.Checked r' → b.Reorders r r' →
    ∀ s root, Reachable b r root s → Reachable b r' root s → ∀ d f,
    Local b r (e.run r s root).1 d f ↔ Local b r' (e.run r' s root).1 d f
  dictionaryRefl : ∀ dictionary, b.DictionaryEquivalent dictionary dictionary
  evidenceNode : EvidenceNode b
  generatedChildren : GeneratedChildren b
  initialReorders : ∀ r r', b.Checked r → b.Checked r' → b.Reorders r r' →
    ∀ s d, b.Initial r d s → b.Initial r' d s

/-- A local model law need only hold at actually reachable intermediate states. -/
theorem steps_models (b : SourceBoundary v) (r : v.Registry) (d : v.Demand)
    (rule : ∀ before after, Reachable b r d before → b.Step r d before after →
      ∀ model, b.Models after model → b.Models before model)
    (reachable : Reachable b r d before) (trace : Steps (b.Step r d) before after) :
    ∀ model, b.Models after model → b.Models before model := by
  induction trace with
  | refl => exact fun _ h => h
  | tail previous step ih =>
      exact fun model h => ih model (rule _ _ (B4TargetV5.reachable_steps (prior b) reachable previous) step model h)

/-- Conditional composition with exact selected-node evidence and generation scope. -/
theorem b4_of_bridges (b : SourceBoundary v) (e : Executor v) (frontiers : Frontiers v)
    (bridges : B4Bridges b e frontiers) : B4Statement b e := by
  have exact (r : v.Registry) (checked : b.Checked r) (s : v.State)
      (root : v.Demand) (reachable : Reachable b r root s) :
      FrontierExact (frontiers r s) := by
    intro d f
    rw [bridges.localIdentity r s root reachable]
    exact bridges.frontierLocal r checked s root reachable d f
  have accessible (r : v.Registry) (checked : b.Checked r) (s : v.State)
      (root : v.Demand) (reachable : Reachable b r root s) :
      Acc (Child (frontiers r s).Local) root := by
    rw [bridges.localIdentity r s root reachable]
    exact bridges.whereAccessible r checked s root reachable
  have finalReach (r : v.Registry) (checked : b.Checked r) (s : v.State)
      (d : v.Demand) (reachable : Reachable b r d s) : Reachable b r d (e.run r s d).1 :=
    B4TargetV5.reachable_steps (prior b) reachable (bridges.execution r checked s d reachable)
  have exactTree : Exact b e := by
    intro r checked s d tree initial
    have reachable := B4TargetV5.reachable_initial (prior b) initial
    have final := finalReach r checked s d reachable
    rw [bridges.treeExecution r checked s d reachable
      (exact r checked _ d final) (accessible r checked _ d final)]
    have rule := resolve_tree_exact_of_frontier_exact (frontiers r (e.run r s d).1)
      (exact r checked _ d final) d (accessible r checked _ d final) tree
    simpa only [bridges.localIdentity r _ d final] using rule
  refine ⟨?_, exactTree, ?_, ?_, ?_⟩
  · intro r checked s d initial
    have reachable := B4TargetV5.reachable_initial (prior b) initial
    obtain ⟨stable, generated⟩ := bridges.closure r checked _ d
      (finalReach r checked s d reachable) (bridges.halted r checked s d reachable)
    exact ⟨bridges.progress r checked s d reachable, bridges.execution r checked s d reachable,
      stable, generated, steps_models b r d (bridges.stepModels r checked d)
        reachable (bridges.execution r checked s d reachable)⟩
  · intro r r' checked checked' order s d initial
    have initial' := bridges.initialReorders r r' checked checked' order s d initial
    have resolved := (exactTree r checked s d _ initial).mp rfl
    have transported := B4Skeleton.resolves_transport
      (fun q f h => (bridges.canonicalLocalOrder r r' checked checked' order s d
        (B4TargetV5.reachable_initial (prior b) initial) (B4TargetV5.reachable_initial (prior b) initial') q f).mp h) resolved
    have same := (exactTree r' checked' s d _ initial').mpr transported
    rw [same]
    exact same_diagnostic_refl (base b) bridges.dictionaryRefl _
  · intro r checked s d dictionary initial derived model models
    have reachable := B4TargetV5.reachable_initial (prior b) initial
    have final := finalReach r checked s d reachable
    obtain ⟨rootStable, generatedStable⟩ := bridges.closure r checked _ d final
      (bridges.halted r checked s d reachable)
    exact dictionary_evidence b bridges.evidenceNode bridges.generatedChildren r checked _ d final
      rootStable generatedStable model models dictionary d (Or.inl rfl) derived
  · intro r checked s d initial returned
    have resolved := (exactTree r checked s d .rejected initial).mp returned
    cases resolved with
    | rejected localRule => exact (B4TargetV8.rejected_iff.mp localRule)

/-- This direction only transports existing evidence; the new boundary's
unconditional EvidenceNode is still a separate obligation. -/
theorem evidenceNode_of_prior {b : SourceBoundary v}
    (node : B4SkeletonV7.EvidenceNode b.toV7) : EvidenceNode b := by
  intro r checked s root reachable model models d key children dictionaries
    reached stable childStable selected evidence
  exact node r checked s root reachable model models d key children dictionaries
    reached stable childStable (B4TargetV8.selected_iff.mp selected).1 evidence

/-- Selected V8 edges are also selected V7 edges, with no added generation premise. -/
theorem generatedChildren_of_prior {b : SourceBoundary v}
    (generated : B4SkeletonV7.GeneratedChildren b.toV7) : GeneratedChildren b := by
  intro r checked s root d key children reachable reached stable selected child member
  exact generated r checked s root d key children reachable reached stable
    (B4TargetV8.selected_iff.mp selected).1 child member

end Yulang.B4SkeletonV8
