import YulangClosure.SourceSignatureExtractedR301

/-!
R301 finite source instance. Expected data below is handwritten from
`source-signature-r301.yu`, not emitted by the Rust producer. The generated
module retains its same-run JSON, including the native-identity table and HIR
diagnostics. Nat labels are meaningful only inside that extraction artifact.

Line 2: `(() -> ['arg]int) -> [F, E, F, 'out]('a -> [E]int)`.
E/F are artifact families 0/1; row positions 5/6/7 locate the three bracket
rows at bytes [29,36), [43,59), [65,69). Line 3's explicit empty row is key 11
at [94,97). Line 4's hole is key 15 at [124,125). These ranges authenticate
human inspection of this fixture, not native identity across executions.

This checks finite retained data against R300's syntax and field machinery.
It supplies no general Rust/Lean equivalence, primitive license, IF whole-map
action, solver acceptance, or concrete R159 admission instance.
-/
namespace YulangClosure.SourceSignatureExtractedChecksR301

open PrimitiveOperation SourceSignatureRealizationR300
open SourceSignatureExtractionR300

abbrev Row := EffectRow Nat Nat
abbrev Sig := Signature Nat Nat

def argumentRow : Row := ⟨5, [], ["'arg"]⟩
def callableRow : Row := ⟨6, [1, 0, 1], ["'out"]⟩
def resultRow : Row := ⟨7, [0], []⟩
def emptyRow : Row := ⟨11, [], []⟩

def expectedArgument : Sig :=
  .function none (.primitive none .unit) (.primitive (some argumentRow) .int)
def expectedResult : Sig :=
  .function (some callableRow) (.variable none "'a") (.primitive (some resultRow) .int)
def expectedNested : Sig := .function none expectedArgument expectedResult

theorem nested_exact : signature0 = expectedNested := rfl

theorem empty_exact : signature1 =
    (.function none (.primitive none .unit) (.primitive (some emptyRow) .int) : Sig) := rfl

theorem retained_exact : signature2 =
    (.function none (.tuple none [.variable none "'a", .hole none 15])
      (.function none (.primitive none .unit) (.primitive none .int)) : Sig) := rfl

/-- All seven source paths, complete rows and independently tracked signs.
Two nested argument edges restore the positive signs. -/
theorem nested_fields :
    ([[], [.argument], [.argument, .argument], [.argument, .result],
      [.result], [.result, .argument], [.result, .result]] : List (List SourceSignatureRealizationR300.Step)).map
      (fieldRead signature0 true true) =
    [some (expectedNested, none, true, true),
     some (expectedArgument, none, false, false),
     some (.primitive none .unit, none, true, true),
     some (.primitive (some argumentRow) .int, some argumentRow, false, false),
     some (expectedResult, some callableRow, true, true),
     some (.variable none "'a", none, false, false),
     some (.primitive (some resultRow) .int, some resultRow, true, true)] := rfl

theorem retained_tuple_fields :
    fieldRead signature2 true true [.argument, .element 0] =
      some (.variable none "'a", none, false, false) ∧
    fieldRead signature2 true true [.argument, .element 1] =
      some (.hole none 15, none, false, false) ∧
    lookup signature2 [.argument, .element 2] = none := ⟨rfl, rfl, rfl⟩

theorem independent_signs :
    fieldRead signature0 true false [.argument, .argument] =
      some (.primitive none .unit, none, true, false) := rfl

/-- Apply R300's original typed field constructor and its readback theorem to
this actual extracted callable subtree, for arbitrary initial signs. -/
theorem callable_field_readback (p v : Bool) :
    fieldRead signature0 p v [.result] = some (expectedResult, some callableRow, p, v) :=
  fieldRead_exact (.result (.root expectedResult)) p v

theorem argument_result_field :
    Nonempty (Field signature0 [.argument, .result] (.primitive (some argumentRow) .int)) :=
  (lookup_iff_field signature0 (.primitive (some argumentRow) .int)
    [.argument, .result]).mp rfl

/-- Value-shape preflight only: no solver/preflight execution is claimed. -/
theorem operation_value_shapes :
    operationValues signature0 = true ∧ operationValues signature1 = true ∧
      operationValues signature2 = false := ⟨rfl, rfl, rfl⟩

theorem positive_callable_plan :
    operationEffectPlan 4 (some callableRow) (some 0) true true =
      some (.view true 6 [0, 1, 0, 1] (some "'out")) :=
  operation_written_positive 4 6 [1, 0, 1] ["'out"] (some 0) true (by decide)

theorem negative_argument_tail :
    operationEffectPlan 4 (some argumentRow) none false false =
      some (.tail false "'arg") :=
  operation_written_negative_tail 4 5 "'arg" none false

theorem omitted_empty_distinct :
    effects (.primitive (Hole := Nat) (Effect := Row) none .int) ≠
      effects (.primitive (Hole := Nat) (Effect := Row) (some emptyRow) .int) := by
  intro impossible
  cases impossible

theorem family_only_outer :
    selfFamily 0 [] = some 0 ∧ selfFamily 0 [.argument] = none ∧
      selfFamily 0 [.result] = none := ⟨rfl, rfl, rfl⟩

/-- R300's exact original Union consumer is applied to R159's unchanged App
inversion. This is a necessary consequence of an arbitrary original App proof;
it does not manufacture that proof from `signature0` or change the environment. -/
theorem original_app_requires_computation_check {Value : Type}
    (kernel : OriginalSource.Kernel Value)
    (environment : OriginalSource.Environment Value)
    (context : OriginalSource.Context) (mark : OriginalSource.Mark)
    (callee argument : OriginalSource.Source .expression)
    (typed : OriginalSource.SourceJudgment kernel environment context
      (.app mark callee argument)) :
    ∃ candidate, kernel.admitted environment ⟨mark.site, .viewLogic, 0⟩ candidate ∧
      OriginalSource.Local kernel
        (environment.extend ⟨mark.site, .viewLogic, 0⟩ candidate)
        (.checking ⟨.computation, mark.site, context,
          ⟨mark.site, .callableImage⟩, ⟨mark.site, .synthesis⟩⟩) := by
  obtain ⟨_, candidate, admitted, body⟩ :=
    (SourceAppAdmissionR159.app_source_iff kernel environment context mark callee argument).mp typed
  obtain ⟨locals, _, _⟩ :=
    (SourceAppAdmissionR159.app_continuation_iff kernel _ context mark callee argument).mp body
  exact ⟨candidate, admitted,
    locals _ (actual_union_consumer context mark callee argument)⟩

end YulangClosure.SourceSignatureExtractedChecksR301
