import Yulang.GeneralDeclarativeI65I74NestedInvariantEntry440
import Yulang.GeneralDeclarativeWitnessVarianceFixtures357
import Yulang.GeneralDeclarativeWitnessRecordWindowFixture358

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
namespace Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.ScopedExample
open GeneralDeclarativeI65
open GeneralDeclarativeWitnessSparseVariance357 (compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open CommonRoleOutermostResolver (Dictionary)
open CommonDeclaredNominalInspection (Parameter Registry)
open CommonRecursiveNominalIntervals (admitContext)
open CommonNominalFullCarrier (Ty Subtype Equivalent nominal subtype_refl)
open GeneralDeclarativeWitnessRecordWindowFixture358 (payload integer_to_payload strict_original_payload_bounds)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open PresenceNormalForm (Atom)
open Checker408 (Problem Result)

inductive Lane where
  | listList | listBox | listArrow
  deriving DecidableEq

def Lane.inner : Lane → Nat
  | .listList => 9
  | .listBox => 20
  | .listArrow => 42

def Lane.mode : Lane → Parameter
  | .listList => inv
  | .listBox => ⟨.value,.covariant⟩
  | .listArrow => ⟨.value,.contravariant⟩

def actual (l : Lane) : Declaration := ⟨80,7,[namedShape 9 l.inner 6],[],[],[]⟩
def rawRows (l : Lane) : List Equation :=
  [rawNominal 0 9 1,rawNominal 1 l.inner 3,
    ⟨2,.primitive (.scalar .int) []⟩,
    ⟨4,.join (.primitive (.scalar .int) []) (.primitive (.scalar .bool) [])⟩]
def atomAt (a b : Nat) : Atom Nat := .tyLe (.var a) (.var b)
def atoms : List (Atom Nat) := [atomAt 2 2,atomAt 4 4,atomAt 2 4,atomAt 2 3,atomAt 3 4]
def ordinary (l : Lane) : GeneralDeclarativeHead320.State := ⟨⟨atoms,[]⟩,rawRows l⟩
def roleDemand : Demand := ⟨7,[⟨0,0,0⟩],[]⟩

def table : Registry :=
  List.replicate 9 [] ++ [[inv]] ++ List.replicate 10 [] ++ [[⟨.value,.covariant⟩]] ++
    List.replicate 21 [] ++ [[⟨.value,.contravariant⟩]] ++ List.replicate 48 [] ++ [[]]

def surface (l : Lane) (ds : List Declaration := [actual l]) : InputBundle :=
  let rows : List Row := [⟨9,some ⟨[.type],9⟩,.invariant⟩,
    ⟨20,some ⟨[.type],20⟩,.unclassified⟩,⟨42,some ⟨[.type],42⟩,.unclassified⟩,
    ⟨90,some ⟨[],90⟩,.unclassified⟩]
  ⟨⟨.absent,rows⟩,⟨.absent,rows⟩,⟨0,[⟨7,1,[]⟩]⟩,ds⟩

def endpoints (l : Lane) (issuer : List Nat := [71]) : List Origin :=
  [⟨0,issuer,nestedEndpoint 9 l.inner 2 4⟩,⟨1,issuer,nestedInner l.inner 2 4⟩]

def build (l : Lane) (raw : GeneralDeclarativeHead320.State := ordinary l)
    (modes : Registry := table) (origins : List Origin := endpoints l)
    (ds : List Declaration := [actual l]) : Option Problem := do
  let bodies := GeneralDeclarativeWitnessVarianceFixtures357.source
  let graph ← compile bodies
  let source ← GeneralSourceMetadataBareBundle291.compile (surface l ds)
  let env : Environment := ⟨3,2,0,bodies,graph,source⟩
  let s : GeneralDeclarativeI65.State := ⟨⟨env,raw,[]⟩,modes,origins,[]⟩
  let b6 : B6OccurrenceAtlas401 s := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨s,b6⟩,⟨[71],roleDemand⟩⟩

def wire : Wire := ⟨0,1,0,1,⟨[0,1,2,3,4],[0,1,1,1,1]⟩,
  ⟨[0,1,2,3,4],[2,0,1,1,1]⟩⟩
def report (l : Lane) : Result := leafReport (actual l)
def test (l : Lane) (p : Option Problem := build l) (r : Result := report l)
    (w : Witness := .nested wire) : Bool :=
  (p.map fun p => check p r w).getD false

theorem exact_original_nested_entry_all_three_modes440 (l : Lane) : test l = true := by
  cases l <;> decide +kernel

theorem actual_declared_inner_changes_when_inherited440 :
    admitContext table false (nestedInner 20 2 4) = false ∧
    admitContext table true (nestedInner 20 2 4) = true ∧
    admitContext table false (nestedInner 42 2 4) = false ∧
    admitContext table true (nestedInner 42 2 4) = true := by decide +kernel

def missingCross (l : Lane) : GeneralDeclarativeHead320.State := ⟨⟨[atomAt 2 2,atomAt 4 4,atomAt 2 3,atomAt 3 4],[]⟩,rawRows l⟩
def wrongModes : Registry := List.replicate 9 [] ++ [[inv]] ++ List.replicate 10 [] ++ [[inv]] ++
  List.replicate 21 [] ++ [[⟨.value,.contravariant⟩]] ++ List.replicate 48 [] ++ [[]]

theorem wrong_modes_missing_explicit_cross_bad_origin_and_report_fail440 :
    test .listBox (build .listBox (ordinary .listBox) wrongModes) = false ∧
    test .listBox (build .listBox (missingCross .listBox)) = false ∧
    test .listBox (build .listBox (ordinary .listBox) table (endpoints .listBox [72])) = false ∧
    test .listBox (build .listBox) {report .listBox with tree := .ambiguous} = false ∧
    test .listBox (build .listBox) (report .listBox) (.nested {wire with innerRow := 0}) = false := by
  decide +kernel

def innerCycle : GeneralDeclarativeHead320.State :=
  {ordinary .listBox with equations := rawRows .listBox ++ [⟨3,.variable 1⟩]}
def rootOnlyCertificate : List410.ExactEscapeWire :=
  ⟨[0,2,1,2,3],[0,1,1,1]⟩
def innerRawCycle : GeneralDeclarativeWitnessCycle350.Wire :=
  ⟨0,⟨1,.same,3⟩,[],.forward 4⟩

theorem real_entered_inner_cycle_is_not_raw_root440 :
    List410.checkExactEscape innerCycle 0 rootOnlyCertificate = true ∧
    GeneralDeclarativePriority321.RootRecurs innerCycle ⟨7,[⟨1,1,1⟩],[]⟩ ∧
    test .listBox (build .listBox innerCycle) (report .listBox)
      (.nested {wire with rootEscape := rootOnlyCertificate}) = false := by
  exact ⟨by decide +kernel,
    GeneralDeclarativeWitnessCycle350.rooted (w := innerRawCycle) (by decide +kernel),
    by decide +kernel⟩

def rawRootCycle : GeneralDeclarativeHead320.State :=
  {ordinary .listBox with equations := rawRows .listBox ++ [⟨1,.variable 0⟩]}
def rootRawWire : GeneralDeclarativeWitnessCycle350.Wire :=
  ⟨0,⟨0,.same,1⟩,[],.forward 4⟩
def previousRoot : Witness :=
  .previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous
    (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous (.previous
    (.previous (.previous (.rawRoot rootRawWire))))))))))))))))))))

theorem actual_root_K2_remains_on_previous_entry440 :
    test .listBox (build .listBox rawRootCycle) (report .listBox) = false ∧
    test .listBox (build .listBox rawRootCycle) Check408.rawReport previousRoot = true := by
  decide +kernel

def rogueOuter : GeneralDeclarativeHead320.State :=
  {ordinary .listBox with equations := rawRows .listBox ++ [⟨6,.variable 0⟩,rawNominal 6 9 5]}
def rogueSafe : List410.ExactEscapeWire := ⟨[0,1,2,3,4,5,0],[0,1,1,1,1,1]⟩
def alternate : Declaration := {actual .listBox with id := 81,head := [.var 8]}

theorem raw_outer_alternate_and_actual_visible_rival_cannot_be_ignored440 :
    List410.checkExactEscape rogueOuter 0 rogueSafe = true ∧
    test .listBox (build .listBox rogueOuter) (report .listBox)
      (.nested {wire with rootEscape := rogueSafe}) = false ∧
    test .listBox (build .listBox (ordinary .listBox) table (endpoints .listBox)
      [actual .listBox,alternate]) = false := by decide +kernel

def centerValue (upper : Bool) : Ty := if upper then payload else .base .int

def model (l : Lane) (upper : Bool) : I72.Model :=
  ⟨fun n => ((match n with
    | 0 => nominal 9 [.inl (nominal l.inner [.inl (centerValue upper)])]
    | 1 => nominal l.inner [.inl (centerValue upper)]
    | 2 => .base .int
    | 3 => centerValue upper
    | 4 => payload
    | _ => .bottom),Common.rowEmpty),
    fun _ => none,
    fun n => if n = 0 then some (nestedEndpoint 9 l.inner 2 4)
      else if n = 1 then some (nestedInner l.inner 2 4) else none⟩

theorem fitted_nonpoint440 (l : Lane) (upper : Bool) {p : Problem} (got : build l = some p) :
    I72.Fits p.state (model l upper) := by
  unfold build at got
  cases graph : compile GeneralDeclarativeWitnessVarianceFixtures357.source with
  | none => simp [graph] at got
  | some sem =>
    cases source : GeneralSourceMetadataBareBundle291.compile (surface l [actual l]) with
    | none => simp [graph,source] at got
    | some src =>
      simp only [graph,source,Option.pure_def] at got
      cases got
      refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
      · intro a used
        change a ∈ atoms at used
        simp only [atoms,List.mem_cons,List.not_mem_nil,or_false] at used
        rcases used with rfl|rfl|rfl|rfl|rfl
        · exact subtype_refl _
        · exact subtype_refl _
        · exact integer_to_payload
        · cases upper
          · exact subtype_refl _
          · exact integer_to_payload
        · cases upper
          · exact integer_to_payload
          · exact subtype_refl _
      · intro _ noRow
        cases noRow
      · intro e seen
        change e ∈ rawRows l at seen
        simp only [rawRows,List.mem_cons,List.not_mem_nil,or_false] at seen
        rcases seen with rfl|rfl|rfl|rfl <;> exact eqv_refl _
      · intro _ noRow
        cases noRow
      · intro o inList
        change o ∈ endpoints l at inList
        simp only [endpoints,List.mem_cons,List.not_mem_nil,or_false] at inList
        rcases inList with rfl|rfl <;> rfl

theorem same_original_nonpoint_selects_fixed_dictionary_with_two_centers440 (l : Lane) :
    ∃ p, build l = some p ∧ check p (report l) (.nested wire) = true ∧
      (∀ upper, I72.Fits p.state (model l upper) ∧
        ReportEvidence p.state (model l upper) p.root (report l)) ∧
      ¬Equivalent ((model l false).assignment 3).1 ((model l true).assignment 3).1 := by
  have yes := exact_original_nested_entry_all_three_modes440 l
  unfold test at yes
  cases h : build l with
  | none => simp [h] at yes
  | some p =>
    have checked : check p (report l) (.nested wire) = true := by simpa [h] using yes
    have fit (upper : Bool) := fitted_nonpoint440 l upper h
    exact ⟨p,rfl,checked,fun upper =>
      ⟨fit upper,(check_sound p _ _ checked).2 _ (fit upper)⟩,
      fun eq => strict_original_payload_bounds eq.2⟩

#print axioms exact_original_nested_entry_all_three_modes440
#print axioms actual_declared_inner_changes_when_inherited440
#print axioms wrong_modes_missing_explicit_cross_bad_origin_and_report_fail440
#print axioms real_entered_inner_cycle_is_not_raw_root440
#print axioms actual_root_K2_remains_on_previous_entry440
#print axioms raw_outer_alternate_and_actual_visible_rival_cannot_be_ignored440
#print axioms fitted_nonpoint440
#print axioms same_original_nonpoint_selects_fixed_dictionary_with_two_centers440

end Yulang.GeneralDeclarativeI65.I72.NestedInvariant440.ScopedExample
