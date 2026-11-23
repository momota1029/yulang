import Yulang.GeneralDeclarativeWitnessRecordWindowFixture358
import Yulang.GeneralDeclarativeWitnessSiblingLinks358

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessClosedRecordLocal358
open GeneralDeclarativeWitnessDeclaredState357 (Current WrittenBody point context authoredRegistry)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source)
open GeneralDeclarativeWitnessSharedTailProjection358 (Range Supported authored_visibility_same_model)
open GeneralDeclarativeWitnessClassifyVariance357 (roleView roleView_span SourceChecked)
open GeneralDeclarativeWitnessJoinedCheck357 (Layout)
open GeneralDeclarativeWitnessCompiler350 (Wire trip trip_injective map_injective decode retained)
open GeneralDeclarativeHead320 (Equation State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarationPatterns (normalizeArgs)
open GeneralDeclarations (Declaration)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent record)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans record_congr)

def closed (tail : Nat) : Equation := ⟨tail,.primitive .exactEmpty []⟩

structure Chosen (a : Source) (s : Current) (d : Demand) (impl : Declaration) (kids : List Demand) where
  proj : Range
  supported : Supported a s.ordinary proj
  tailAuthor : closed proj.remainder ∈ a.authored
  tailRetained : closed proj.remainder ∈ s.ordinary.equations
  identifying : (roleView s d.role).declarations = [impl]
  actual : d.arguments = [proj.outer]
  fieldBinder : Nat
  tailBinder : Nat
  distinct : fieldBinder ≠ tailBinder
  head : normalizeArgs impl.head = [.record proj.label (.var fieldBinder) (.var tailBinder)]
  body : WrittenBody s d impl [(fieldBinder,proj.projected),(tailBinder,point proj.remainder)] kids

structure Checked (a : Source) (s : Current) (d : Demand) (w : Wire) where
  impl : Declaration
  kids : List Demand
  chosen : Chosen a s d impl kids
  printed : w.children = kids.map GeneralDeclarativeWitnessCompiler350.printDemand
  output : w.outputRows = chosen.body.finished.fixed

def read (a : Source) (s : Current) (d : Demand) (r : Range) (field tail : Nat)
    (l : Layout) (w : Wire) : Option (Checked a s d w) :=
  match only : (roleView s d.role).declarations with
  | [impl] =>
    if read : GeneralDeclarativeWitnessSharedTailProjection358.check a s.ordinary r = true then
      if ids : d.arguments.map trip = [trip r.outer] ∧ field ≠ tail ∧
          normalizeArgs impl.head = [.record r.label (.var field) (.var tail)] ∧
          closed r.remainder ∈ a.authored ∧ closed r.remainder ∈ s.ordinary.equations then do
        let named := context s d impl l.named [(field,r.projected),(tail,point r.remainder)]
          l.keep l.fallback l.via
        let verified ← decode named s.ordinary w
        let body : WrittenBody s d impl [(field,r.projected),(tail,point r.remainder)] verified.compiled.kids :=
          ⟨l.named,l.keep,l.fallback,l.via,verified.compiled,verified.run,rfl,retained verified⟩
        pure ⟨impl,verified.compiled.kids,
          ⟨r,GeneralDeclarativeWitnessSharedTailProjection358.check_exact.mp read,ids.2.2.2.1,
           ids.2.2.2.2,only,map_injective (fun h => trip_injective h) ids.1,field,tail,
           ids.2.1,ids.2.2.1,body⟩,verified.printed,verified.fixed⟩
      else none
    else none
  | _ => none

theorem same_model {a s d w} (read : Checked a s d w)
    (valid : SourceChecked s) (m : Assignment) (fit : Models s.ordinary m) :
    Declared (authoredRegistry s) d ∧
    (∀ d ∈ read.kids,Declared (authoredRegistry s) d) ∧
    Equivalent (m read.chosen.proj.remainder).1 CommonNominalFullCarrier.exactEmpty ∧
    Equivalent (m read.chosen.proj.outer.lower).1
      (record read.chosen.proj.label (m read.chosen.proj.projected.lower).1 CommonNominalFullCarrier.exactEmpty) ∧
    Equivalent (m read.chosen.proj.outer.center).1
      (record read.chosen.proj.label (m read.chosen.proj.projected.center).1 CommonNominalFullCarrier.exactEmpty) ∧
    Equivalent (m read.chosen.proj.outer.upper).1
      (record read.chosen.proj.label (m read.chosen.proj.projected.upper).1 CommonNominalFullCarrier.exactEmpty) ∧
    (w.outputRows.map Equation.left = d.outputs.map GeneralSourceState.Output.target ∧
      ∀ row ∈ w.outputRows,Holds m row) := by
  have member : read.impl ∈ (roleView s d.role).declarations := by
    rw [read.chosen.identifying]
    exact List.mem_cons_self
  have visible := (roleView_span s d.role read.impl).mp member
  have signature := valid.2 read.impl visible.1
  have tail : Equivalent (m read.chosen.proj.remainder).1 CommonNominalFullCarrier.exactEmpty :=
    fit.2 _ read.chosen.tailRetained
  have casts := authored_visibility_same_model read.chosen.supported m fit
  have unmask (p : Nat) := record_congr read.chosen.proj.label (eqv_refl (m p).1) tail
  refine ⟨GeneralDeclarativeWitnessRootDeclared357.written_root_declared read.chosen.body
    signature.signature signature.identified.2.2.1 visible.2,
    GeneralDeclarativeWitnessDeclaredState357.body_declared read.chosen.body signature.signature,
    tail,eqv_trans casts.1 (unmask _),eqv_trans casts.2.1 (unmask _),
    eqv_trans casts.2.2 (unmask _),?_⟩
  rw [read.output]
  exact GeneralDeclarativeWitnessDeclaredState357.output_meaning read.chosen.body m fit

end Yulang.GeneralDeclarativeWitnessClosedRecordLocal358
