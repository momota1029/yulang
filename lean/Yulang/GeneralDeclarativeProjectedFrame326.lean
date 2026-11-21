import Yulang.GeneralDeclarativePairProbe326
import Yulang.GeneralDeclarativeProjectPair326
import Yulang.GeneralDeclarativeOrderedTail326
import Yulang.GeneralDeclarativeFrameReadback325
import Yulang.GeneralDeclarativeEvidenceFold325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeProjectedFrame326
open GeneralDeclarations (Checked Declaration Registry)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeHeadFrame325 (FromSource each)
open GeneralDeclarativePairCenters326 (pair)
open GeneralDeclarativePairProbe326 (normalized_center)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeTermWalk322 (Walk Binds)
open GeneralDeclarativeNFHead324 (fact)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeFrameReadback325 (ClauseFrame clause sourceNames)
open GeneralDeclarativeNFComplete324 (ReadBack local_sound)
open GeneralDeclarativeProducedNames325 (exact_input coherent)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeAppliedSource325 (stable_after_written)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativePriority321 (Local Candidates selected_generated)
open GeneralDeclarativeEvidenceFold325 (LocalWitness same_model)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeOutputRequests323 (child_declared)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarationPatterns (Pattern normalize Constructors)
open CommonRoleOutermostResolver (All₂ Classify)

inductive Head (s : State) (c : Constructors) (i : Interpretation)
    {complete : Nat → Prop} (p : Supported s complete)
    (cap : Nat → Capture) (arg : Capture) (pat : Pattern) : Prop where
  | ordinary : FromSource s c i p cap arg pat → Head s c i p cap arg pat
  | projected : translate c i (normalize pat) = some (pair leftCode rightCode) →
      Derives s (.variable arg.center) (pair left right) →
      Walk .actual left leftCode firstUses → Walk .actual right rightCode lastUses →
      Binds s cap (firstUses ++ lastUses) → Head s c i p cap arg pat

  | joined : translate c i (normalize pat) = some (pair leftCode rightCode) →
      Derives s (.variable arg.center) center →
      GeneralDeclarativeProjectPair326.project center = some (left,right) →
      Walk .actual left leftCode firstUses → Walk .actual right rightCode lastUses →
      Binds s cap (firstUses ++ lastUses) → Head s c i p cap arg pat

theorem head_fact {s : State} {p : Supported s complete} (bounds : Bounds s arg)
    (evidence : Head s c i p cap arg pat) : Result s (fact c i cap arg pat) := by
  cases evidence with
  | ordinary h => exact each bounds h
  | projected src center l r shared => exact normalized_center src center l r shared
  | joined src center seen l r shared =>
    exact GeneralDeclarativePairUnion326.with_joined_centers src center
      (GeneralDeclarativeProjectPair326.recorded seen) l r shared

/-- Exactly the usual normalized head batch for a known closed record
spine when visible labels appear in a different storage order. The
remaining names are produced by the ordinary fresh-tail constructor. -/
theorem ordered_record_fact {s : State} (kept : List Nat)
    (arg : Capture) (raw : CommonRoleCanonicalRows.Row Expr)
    (labelOrder : keys.Nodup)
    (read : GeneralDeclarativeOrderedRecord326.order (CommonRoleCanonicalRows.normalize raw) keys =
      some printed)
    (terminalKnown : GeneralDeclarativeFreshTail326.Closed terminal)
    (visible : Derives s (.variable arg.center)
      (GeneralDeclarativeRecordResidual323.withTail raw terminal))
    (source : translate c i (normalize pat) = some code)
    (walk : Walk .actual (GeneralDeclarativeRecordResidual323.withTail printed
        (.variable (GeneralDeclarativeFreshTail326.tailRow s kept arg.center raw keys terminal).left))
      code links)
    (captures : Binds (GeneralDeclarativeFreshTail326.extended s kept arg.center raw keys terminal)
      cap links) :
    Result (GeneralDeclarativeFreshTail326.extended s kept arg.center raw keys terminal)
      (fact c i cap arg pat) :=
  GeneralDeclarativeForwardHead325.by_walk source
    (GeneralDeclarativeOrderedTail326.actual_decl_order kept raw labelOrder read terminalKnown visible)
    walk captures

structure Frame (s : State) (r : Registry) (i : Interpretation)
    {complete : Nat → Prop} (p : Supported s complete) (d : Demand) (decl : Declaration)
    (base : Nat → Capture) (place : Placement) : Prop where
  head : All₂ (fun a ptn => Bounds s a ∧ Head s r.constructors i p (sourceNames decl place base).input a ptn)
    d.arguments decl.head
  ranges : ∀ n ∈ decl.inputNames, Bounds s (base n)
  clauses : ∀ cl ∈ decl.requirements, ClauseFrame s r i decl cl (sourceNames decl place base) place
  returned : ∃ rows, collect (one r i decl d (sourceNames decl place base).input) d.outputs = some rows ∧
    rows ⊆ s.equations

theorem readback {s : State} {p : Supported s complete} (checked : Checked r)
    (visible : decl ∈ r.declarations) (use : Frame s r i p d decl base place) :
    ReadBack s r i d decl (sourceNames decl place base) place := by
  refine ⟨?_,?_,coherent _ _ _,fun c used => clause (use.clauses c used)⟩
  · exact GeneralDeclarativeNormalized320.ordered_map use.head (fun _ _ _ _ h => ⟨h.1,head_fact h.1 h.2⟩)
  · intro n used
    unfold sourceNames
    rw [exact_input (checked.2 decl visible) used]
    exact use.ranges n used

def Generated (s : State) (r : Registry) (i : Interpretation)
    {complete : Nat → Prop} (p : Supported s complete) (d : Demand)
    (decl : Declaration) (out : List Demand) : Prop :=
  ∃ base place, Frame s r i p d decl base place ∧ children decl (sourceNames decl place base) place = out

abbrev Rule (s : State) (r : Registry) (i : Interpretation)
    {complete : Nat → Prop} (p : Supported s complete) (tests : Candidates) := Local s r i p tests (Generated s r i p)

theorem local_witness {s : State} {p : Supported s complete} (checked : Checked r) :
    LocalWitness r i s (Rule s r i p tests) := by
  intro m valid d declared key kids choice
  obtain ⟨impl,rfl,⟨⟨vis,role⟩,_⟩,base,place,shown,rfl⟩ := selected_generated choice
  obtain ⟨rows,built,held⟩ := shown.returned
  have ⟨coverage,stable⟩ := stable_after_written checked vis built held
  exact ⟨⟨impl,(sourceNames impl place base).input,rfl,
    local_sound checked vis role declared coverage (readback checked vis shown) stable m valid⟩,
    fun _ used => child_declared checked vis used⟩

/-- Extending the positive readback to actual projections does not
extend the independent priority or provenance conditions in Local. -/
theorem sound {s : State} {p : Supported s complete} (checked : Checked r)
    (wanted : Declared r d) (valid : Models s m)
    (picked : Classify (Rule s r i p tests) d (.selected dict)) : Evidence r i m d dict :=
  same_model (local_witness checked) valid wanted picked

end Yulang.GeneralDeclarativeProjectedFrame326
