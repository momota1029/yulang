import Yulang.NominalDataAssembly

namespace Yulang.NominalDataAssemblyExamples

open Directed Directed.Computation NominalConstructions NominalConstructionRuntime PureCasts
open CaseValues NominalDataAssembly

private def integerType : Casts.Ty := .base .int
private def wrappedType : Casts.Ty := .nominal 99 []
private def integer (value : Int) : Value Empty := .literal (.int value)
private def first : Argument 1 := ⟨0, ⟨10, wrappedType⟩⟩
private def second : Argument 1 := ⟨0, ⟨20, integerType⟩⟩

private def unbox : PureCasts.Declaration 1 Nat Unit Unit (Value Empty) (Value Empty) where
  body := fun value => .pure (match value with
    | .nominal 99 0 (.literal (.int number)) => integer (number + 1)
    | _ => value)
  row := []
  bounded := fun _ => trivial

private def runtime : Runtime 1 1 Nat Unit Unit (Value Empty) where
  fits := Casts.equalityCompatibility
  source := fun argument => .request (raw argument.original.site) () (fun _ =>
    .pure (if argument.original.site = 10 then .nominal 99 0 (integer 10) else integer 20))
  convert := fun _ _ => .declared unbox rfl

private def expected : Expectation 1 := fun _ => some integerType

private def construction (constructor : Constructor) : Construction 1 :=
  ⟨constructor, 500, [first, second]⟩

private def structCode : Code Empty (.structLiteral 7) :=
  .structLiteral 7 3 (.record 0 (.var 10) (.record 0 (.var 20) .emptyRecord))

private def enumCode : Code Empty (.enumConstructor 8 2) :=
  .enumeration 8 2 (.pair (.var 10) (.var 20))

private def listCode : Code Empty (.listLiteral 9) :=
  .list 9 (.cons (.var 10) (.cons (.var 20) .nil))

/-- Both written sites request, including the value hidden by the first field.
The converted field becomes part of the actual concrete struct payload. -/
theorem struct_casts_at_sites_and_keeps_hidden_requests :
    mapValue (fun built => built.evaluation.result)
      (NominalDataAssembly.execute runtime
        ((construction (.structLiteral 7)).plan expected) structCode) =
      (.request (raw 10) () (fun _ => .request (raw 20) () (fun _ =>
        .pure (.ok (.nominal 7 3 (.record [(0, integer 11)]))))) :
          Computation 1 Nat Unit Unit (Except CaseDataTerms.Error (Value Empty))) := rfl

/-- Constructor identity, enum tag and ordered pair payload all survive the
site-to-concrete-AST bridge. The already compatible second site is unchanged. -/
theorem enum_casts_then_constructs_payload :
    mapValue (fun built => built.evaluation.result)
      (NominalDataAssembly.execute runtime
        ((construction (.enumConstructor 8 2)).plan expected) enumCode) =
      (.request (raw 10) () (fun _ => .request (raw 20) () (fun _ =>
        .pure (.ok (.nominal 8 2 (.pair (integer 11) (integer 20)))))) :
          Computation 1 Nat Unit Unit (Except CaseDataTerms.Error (Value Empty))) := rfl

theorem list_casts_then_constructs_elements :
    mapValue (fun built => built.evaluation.result)
      (NominalDataAssembly.execute runtime
        ((construction (.listLiteral 9)).plan expected) listCode) =
      (.request (raw 10) () (fun _ => .request (raw 20) () (fun _ =>
        .pure (.ok (.list [integer 11, integer 20])))) :
          Computation 1 Nat Unit Unit (Except CaseDataTerms.Error (Value Empty))) := rfl

/-- With no target, the already constructed wrapped value stays wrapped; no
conversion is lifted through the completed outer list. -/
theorem eof_list_keeps_original_values :
    mapValue (fun built => built.evaluation.result)
      (NominalDataAssembly.execute runtime
        ((construction (.listLiteral 9)).plan (fun _ => none)) listCode) =
      (.request (raw 10) () (fun _ => .request (raw 20) () (fun _ =>
        .pure (.ok (.list [.nominal 99 0 (integer 10), integer 20])))) :
          Computation 1 Nat Unit Unit (Except CaseDataTerms.Error (Value Empty))) := rfl

end Yulang.NominalDataAssemblyExamples
