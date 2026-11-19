import Yulang.GeneralRebaseInstallNovelty279

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseOccurrenceCode279
open GeneralSourceDictionaries (Occurrence)
open GeneralSourceState (Demand Output Interval)

structure DemandCode where
  role : Nat
  arguments : List Interval
  outputs : List (Nat × Nat)
  deriving DecidableEq, Repr

structure OccurrenceCode where
  identity : Nat
  demand : DemandCode
  deriving DecidableEq, Repr

def outputCode (o : Output) : Nat × Nat := (o.name,o.target)

def demandCode (d : Demand roles) : DemandCode :=
  ⟨d.role,List.ofFn d.arguments,d.outputs.map outputCode⟩

def occurrenceCode (o : Occurrence roles) : OccurrenceCode :=
  ⟨o.identity,demandCode o.demand⟩

theorem outputCode_injective (a b : Output) (same : outputCode a = outputCode b) : a = b := by
  cases a
  cases b
  simp only [outputCode,Prod.mk.injEq] at same
  cases same.1
  cases same.2
  rfl

theorem outputCodes_injective (a b : List Output) (same : a.map outputCode = b.map outputCode) :
    a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons first rest ih =>
    cases b with
    | nil => simp at same
    | cons next tail =>
      simp only [List.map_cons,List.cons.injEq] at same
      rw [outputCode_injective _ _ same.1, ih _ same.2]

theorem argumentsCode_injective (a b : Fin n → Interval) (same : List.ofFn a = List.ofFn b) :
    a = b := by
  funext i
  have idx := congrArg (fun (xs : List Interval) => xs[i.val]?) same
  simpa [List.getElem?_ofFn,i.isLt] using idx

theorem demandCode_injective (a b : Demand roles) (same : demandCode a = demandCode b) :
    a = b := by
  cases a with
  | mk roleA argsA outsA proofA =>
    cases b with
    | mk roleB argsB outsB proofB =>
      simp only [demandCode,DemandCode.mk.injEq] at same
      obtain ⟨r,args,outs⟩ := same
      subst roleB
      have equalArgs := argumentsCode_injective _ _ args
      have equalOutputs := outputCodes_injective _ _ outs
      subst argsB
      subst outsB
      rfl

theorem occurrenceCode_injective (a b : Occurrence roles) (same : occurrenceCode a = occurrenceCode b) :
    a = b := by
  cases a with
  | mk idA demandA =>
    cases b with
    | mk idB demandB =>
      simp only [occurrenceCode,OccurrenceCode.mk.injEq] at same
      cases same.1
      cases demandCode_injective _ _ same.2
      rfl

def codeEdge (edge : Occurrence roles × Occurrence roles) : OccurrenceCode × OccurrenceCode :=
  (occurrenceCode edge.1,occurrenceCode edge.2)

theorem edgeCode_injective (a b : Occurrence roles × Occurrence roles) (same : codeEdge a = codeEdge b) :
    a = b := Prod.ext (occurrenceCode_injective _ _ (congrArg Prod.fst same))
      (occurrenceCode_injective _ _ (congrArg Prod.snd same))

end Yulang.GeneralRebaseOccurrenceCode279
