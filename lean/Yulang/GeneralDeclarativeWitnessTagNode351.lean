import Yulang.GeneralDeclarativeWitnessTagConcrete351

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTagNode351
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand bounds_sound)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open GeneralDeclarativeWitnessTagLocal351 (Route PatternData next spans context prepared)
open GeneralDeclarativeWitnessCompiler350 (Accepted)
open GeneralDeclarativeEndpointBody336 (Body calculate sound)
open GeneralDeclarativeExactDictionary337 (Evidence LocalNode)
open GeneralDeclarativeStableReads329 (names_one)
open GeneralDeclarativeStableAssemble329 (tieState firsts)
open GeneralDeclarativeStableCanonical329 (exact uses_existing)
open GeneralDeclarativeStableTies329 (pairOf from_use)
open GeneralDeclarativeGrowth327 (facts trans restrict)
open GeneralDeclarativeCurrentReceipt330 (relays_models)
open GeneralDeclarativeEqualities322 (semantic)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Registry Declaration Checked)
open GeneralNominalInspection (Interpretation)
open CommonRoleOutermostResolver (All₂)

variable {s : State} {t : Table} {a : Attached s t} {arg : Capture} {tag : Nat}
variable {r : Registry} {i : Interpretation} {d : Demand} {impl : Declaration}

theorem local_node (h : Route a arg tag) (x : PatternData r.constructors i pat tag)
    {keep fallback targets current wire}
    (compiled : Accepted (context d impl h x keep fallback targets) current wire)
    (well : Checked r) (covered : Coverage r i)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role) (declared : Declared r d)
    (args : d.arguments = [arg]) (head : impl.head = [pat])
    (m : Assignment) (fit : Models current m) :
    LocalNode r i m d impl.id compiled.compiled.kids ∧
      (∀ child ∈ compiled.compiled.kids, Declared r child) := by
  obtain ⟨_,read,ranges⟩ := prepared h x keep
  have order : (spans h x keep).map Prod.fst = impl.inputNames := by
    rw [GeneralDeclarations.Declaration.inputNames,head]
    simpa only [GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.variablesArgs,
      List.append_nil] using names_one read
  obtain ⟨ordinary,kids,b,expected,_,names,_,_,growth⟩ :=
    calculate well covered visible role declared keep fallback targets order ranges
  have seen := GeneralDeclarativeWitnessCompiler350.actual compiled
  change GeneralDeclarativeNestedBody332.compileBody r i d impl (next h x keep)
    (spans h x keep) keep fallback targets = some (compiled.compiled.state,compiled.compiled.kids) at seen
  cases Option.some.inj (expected.symm.trans seen)
  have printed := relays_models (GeneralDeclarativeWitnessCompiler350.retained compiled) m fit
  have tied := restrict growth m printed
  have prefixFit := restrict (trans (facts (next h x keep) _) growth) m printed
  have shares := ((exact (next h x keep) (firsts (spans h x keep) fallback)
    (spans h x keep) (uses_existing _ _) m).mp tied).2
  obtain ⟨meaning,children⟩ := sound b well covered visible role declared m printed
  obtain ⟨code,form,written,center,walk⟩ := read.actual
  refine ⟨⟨impl,b.capture,spans h x keep,rfl,⟨?_,meaning,shares,?_⟩⟩,children⟩
  · rw [args,head]
    exact .cons (.literal (bounds_sound read.fits m prefixFit) written (semantic center m prefixFit) walk) .nil
  · intro p requested
    have present : pairOf p ∈ b.spans.map pairOf := List.mem_map.mpr ⟨p,names.symm ▸ requested,rfl⟩
    have sound := from_use b.tied present m printed
    have inNames : p.1 ∈ impl.inputNames := by
      rw [← order]
      exact List.mem_map.mpr ⟨p,requested,rfl⟩
    unfold Body.capture GeneralDeclarativeFrameReadback325.sourceNames
    rw [GeneralDeclarativeProducedNames325.exact_input (well.2 impl visible) inNames]
    exact sound

theorem leaf_evidence (h : Route a arg tag) (x : PatternData r.constructors i pat tag)
    {keep fallback targets current wire}
    (compiled : Accepted (context d impl h x keep fallback targets) current wire)
    (well : Checked r) (covered : Coverage r i)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role) (declared : Declared r d)
    (args : d.arguments = [arg]) (head : impl.head = [pat])
    (leaf : compiled.compiled.kids = []) (m : Assignment) (fit : Models current m) :
    Evidence r i m d (.node impl.id []) := by
  have node := (local_node h x compiled well covered visible role declared args head m fit).1
  rw [leaf] at node
  exact .node node .nil

end Yulang.GeneralDeclarativeWitnessTagNode351
