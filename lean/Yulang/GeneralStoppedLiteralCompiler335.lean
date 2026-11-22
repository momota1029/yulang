import Yulang.GeneralDeclarativeWitnessClassify334

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralStoppedLiteralCompiler335
open GeneralDeclarations (Registry Declaration Clause Checked)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeStableReads329 (Heads weakened names_all)
open GeneralDeclarativeStableTies329 (Consequence rows pairOf)
open GeneralDeclarativeStableAssemble329 (firsts prepare_grows)
open GeneralDeclarativeOpaqueCapture328 (choice_exact)
open GeneralDeclarativeStableCompiler329 (Frame)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeAppliedClause327 (prepared_exists targetsOnly compiled_frames)
open GeneralDeclarativeFrameReadback325 (sourceNames)
open GeneralDeclarativeClauseBatch327 (prepare)
open GeneralDeclarativeClausePlacement327 (placement)
open GeneralDeclarativeWhereOutputBatch327 (whole)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeGrowth327 (Extends facts trans fits)
open GeneralDeclarativeOpaqueBatch328 (check_exact)

/-- An independent representation test only. A linear head already
supplies one literal available capture per binder. Reuse all three
names at a bare-binder occurrence; do not replace the main compiler
or choose a rule for multiple incompatible intervals. -/
def compile (r : Registry) (i : Interpretation) (d : Demand) (impl : Declaration)
    (named : State) (spans : List (Nat × Capture)) (keep : List Nat)
    (fallback : Nat → Capture) (targets : Clause → Nat → Nat) : Option (State × List Demand) := do
  if ¬(spans.map Prod.fst).Nodup then none else
    let base := firsts spans fallback
    let inputs := (sourceNames impl (targetsOnly targets) base).input
    let (prepared,ports) ← prepare r.constructors i (stateNames named ++ keep) inputs named impl.requirements
    let place := placement impl.requirements ports targets
    let chosen := sourceNames impl place base
    let whereRows ← whole r i impl chosen targets
    let rootRows ← collect (one r i impl d chosen.input) d.outputs
    pure (appendFacts (appendFacts prepared whereRows) rootRows,children impl chosen place)

theorem no_tie (linear : (spans.map Prod.fst).Nodup) :
    rows (firsts spans fallback) (spans.map pairOf) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro e found
  obtain ⟨use,tracked,_⟩ := List.mem_map.mp found
  obtain ⟨present,different⟩ := List.mem_filter.mp tracked
  obtain ⟨⟨key,range⟩,here,rfl⟩ := List.mem_map.mp present
  have identity : firsts spans fallback key = range := choice_exact linear here
  simp only [pairOf,identity,bne_self_eq_false] at different
  contradiction

theorem exact_frame {s : State} (checked : Checked r) (cover : Coverage r i)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role) (demand : Declared r d)
    (walks : Heads s r.constructors i d.arguments impl.head spans)
    (bounds : ∀ a ∈ spans, Bounds s a.2) (linear : (spans.map Prod.fst).Nodup)
    (keep : List Nat) (fallback : Nat → Capture) (targets : Clause → Nat → Nat) :
    ∃ out kids, Nonempty (Frame out r i d impl kids) ∧
      compile r i d impl s spans keep fallback targets = some (out,kids) := by
  let base := firsts spans fallback
  obtain ⟨prep,ports,ready⟩ := prepared_exists (s := s) cover visible targets base keep
  let place := placement impl.requirements ports targets
  let named := sourceNames impl place base
  obtain ⟨ws,rs,atWhere,atRoot,_,_,_,_,_⟩ :=
    compiled_frames checked cover visible role demand targets base keep ready
  let afterWhere := appendFacts prep ws
  let current := appendFacts afterWhere rs
  let kids := children impl named place
  have keepPrep : Extends prep current := trans (facts _ _) (facts _ _)
  have grown : Extends s current := trans (prepare_grows ready) keepPrep
  have ranges : ∀ k ∈ impl.inputNames, Bounds current (base k) := by
    intro key tracked
    rw [GeneralDeclarations.Declaration.inputNames,← names_all walks] at tracked
    obtain ⟨span,listed,same⟩ := List.mem_map.mp tracked
    rw [← same]
    have exact := choice_exact (fallback := fallback) linear listed
    change Bounds current (GeneralDeclarativeOpaqueCapture328.choose fallback span.1 spans)
    rw [exact]
    exact fits grown (bounds _ listed)
  have tied : Consequence current base (spans.map pairOf) := by
    intro eq member
    have none := no_tie (fallback := fallback) linear
    exact (List.not_mem_nil (none ▸ member)).elim
  let frame : Frame current r i d impl kids :=
    ⟨base,spans,weakened grown walks,tied,ranges,targets,stateNames s ++ keep,s,prep,ports,
      ready,keepPrep,ws,atWhere,fun _ member => List.mem_append_left _ (List.mem_append_right _ member),
      rs,atRoot,fun _ member => List.mem_append_right _ member,check_exact.mpr rfl⟩
  refine ⟨current,kids,⟨frame⟩,?_⟩
  simp only [compile,linear,not_true_eq_false,ite_false]
  change _ = some (current,kids)
  dsimp only [base] at ready atWhere atRoot
  rw [ready]
  change (do
    let whereRows ← whole r i impl named targets
    let rootRows ← collect (one r i impl d named.input) d.outputs
    pure (appendFacts (appendFacts prep whereRows) rootRows, kids)) = _
  rw [atWhere,atRoot]
  rfl

end Yulang.GeneralStoppedLiteralCompiler335
