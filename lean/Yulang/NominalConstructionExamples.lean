import Yulang.NominalListViews

namespace Yulang.NominalConstructionExamples

open Directed Directed.Computation NominalConstructions NominalConstructionRuntime PureCasts

private def integerType : Casts.Ty := .base .int
private def wrappedType : Casts.Ty := .nominal 99 []

private def first : Argument 1 := ⟨0, ⟨10, wrappedType⟩⟩
private def second : Argument 1 := ⟨0, ⟨20, integerType⟩⟩

private def increment : PureCasts.Declaration 1 Nat Unit Unit Nat Nat where
  body := fun value => .pure (value + 1)
  row := []
  bounded := fun _ => trivial

private def runtime : Runtime 1 1 Nat Unit Unit Nat where
  fits := Casts.equalityCompatibility
  source := fun argument =>
    .request (raw argument.original.site) () (fun _ => .pure argument.original.site)
  convert := fun _ _ => .declared increment rfl

private def construction : Construction 1 :=
  ⟨.structLiteral 7, 500, [first, second]⟩

private def expected : Expectation 1 := fun _ => some integerType

/-- The second site's matching type suppresses its available conversion code. -/
theorem compatible_site_does_not_convert :
    runtime.code (.boundary second integerType) = .keep := rfl

/-- The first site converts after its request; the second retains its value.
The two original requests occur in their written order. -/
theorem casts_keep_order_and_skip_compatible_site :
    runValues runtime (construction.plan expected).instructions =
      (.request (raw 10) () (fun _ =>
        .request (raw 20) () (fun _ => .pure [11, 20])) :
          Computation 1 Nat Unit Unit (List Nat)) := rfl

theorem eof_retains_original_values_and_order :
    runValues runtime (construction.plan (fun _ => none)).instructions =
      (.request (raw 10) () (fun _ =>
        .request (raw 20) () (fun _ => .pure [10, 20])) :
          Computation 1 Nat Unit Unit (List Nat)) := rfl

private def listValue : Built 1 Nat := ⟨.listLiteral 8, 600, fun _ => .expected integerType, [11, 20]⟩

theorem list_uses_constructed_payloads :
    NominalListViews.listView listValue = some [11, 20] := rfl

theorem list_cursor_and_index_agree :
    NominalListViews.nextItem listValue.values = some (11, [20]) ∧
      NominalListViews.index listValue.values 0 = some 11 ∧
      NominalListViews.index listValue.values 1 = some 20 := ⟨rfl, rfl, rfl⟩

theorem list_fold_observes_the_same_payloads :
    NominalListViews.fold (fun total value => total + value) 0 listValue.values = 31 := rfl

end Yulang.NominalConstructionExamples
