import Yulang.GeneralDeclarativeRawCapture344

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRawReplayArgs344
open GeneralNominalCenters (Plan)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Clause)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeRawCapture344 (rawCap operands)
open GeneralDeclarativeNormalizedPort344 (compound)
open GeneralDeclarativeClauseBatch327 (Input Port)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEmissionOperands322 (Compound)
open GeneralWhereVersionCompiler317 (child)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralNominalVersionedFrame231 (capture emittedCenter)
open GeneralStoppedOrdinarySite335 (argument)
open GeneralStoppedPlacement335 (Meaning)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonRoleOutermostResolver (All₂)
open GeneralDeclarativeSourceEmission322 (Names useArg demand inputs)
open GeneralWhereVersionCompiler317 (allocation)
open GeneralDeclarativeDemand320 (Demand)

def names (p : Plan rs) : Names := ⟨rawCap p,(capture p.packet).outputs⟩

def emittedDemand (p : Plan rs) (cl : Clause) (port : Nat → Capture) : Demand :=
  demand p.packet.declaration cl (names p) port (allocation p cl).outputs

theorem bare (p : Plan rs) (cl : Clause) (found : cl ∈ p.packet.declaration.requirements)
    (sig : cl.Signature rs) (idx : Fin (rs cl.role).arity) (key : Nat)
    (same : normalize (cl.arguments[idx.val]'(by rw [sig.1]; exact idx.isLt)) = .var key) :
    argument (child p cl sig) idx = rawCap p key := by
  have notOutput := GeneralVersionedCompoundRows313.clause_arg p cl found
    ⟨idx.val,by rw [sig.1]; exact idx.isLt⟩ key same
  unfold argument
  change (⟨(GeneralDeclarationDemands.inputInterval (capture p.packet)
      (GeneralWhereVersionCompiler317.args p cl idx) _).1,
    emittedCenter p cl.id idx.val _,(GeneralDeclarationDemands.inputInterval (capture p.packet)
      (GeneralWhereVersionCompiler317.args p cl idx) _).2⟩ : Capture) = _
  simp only [GeneralDeclarationDemands.inputInterval,same,emittedCenter,rawCap,
    GeneralNominalVersionedExpressionFrame236.variableSource,notOutput,ite_false]

theorem one (p : Plan rs) (cl : Clause) (found : cl ∈ p.packet.declaration.requirements)
    (sig : cl.Signature rs) (idx : Fin (rs cl.role).arity) (m : Assignment) (typed : Holds p m)
    {s : State} (fit : Models s m) {port : Port}
    (ready : Input s p.packet.registry.constructors p.packet.context.interpretation (rawCap p) cl port) :
    let pat := cl.arguments[idx.val]'(by rw [sig.1]; exact idx.isLt)
    Meaning m (argument (child p cl sig) idx) (useArg (names p) (port.input idx.val) pat) := by
  let pat := cl.arguments[idx.val]'(by rw [sig.1]; exact idx.isLt)
  change Meaning m (argument (child p cl sig) idx) (useArg (names p) (port.input idx.val) pat)
  cases normalized : normalize pat with
  | var key =>
    rw [GeneralDeclarativeSourceEmission322.source_var _ _ _ normalized,bare p cl found sig idx key normalized]
    exact ⟨eqv_refl _,eqv_refl _,eqv_refl _⟩
  | app | record | variant | join =>
    all_goals
      have present : cl.arguments[idx.val]? = some pat := List.getElem?_eq_some_iff.mpr
        ⟨by rw [sig.1]; exact idx.isLt,rfl⟩
      have isCompound : Compound pat := by
        intro name impossible
        rw [normalized] at impossible
        cases impossible
      have real := compound p cl found sig idx m typed fit (rawCap p) port ready pat present isCompound
        (fun code _ mode => operands p m mode code)
      simpa only [useArg,normalized] using real

theorem ofFn_pair {α β : Type} {rel : α → β → Prop} {n : Nat} (a : Fin n → α) (b : Fin n → β)
    (together : ∀ i, rel (a i) (b i)) : All₂ rel (List.ofFn a) (List.ofFn b) := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ]
    exact .cons (together 0) (ih (fun i => a i.succ) (fun i => b i.succ) (fun i => together i.succ))

theorem named_inputs (ns : Names) (port : Nat → Capture) (start : Nat) (ps : List Pattern) :
    inputs ns port start ps =
      List.ofFn (fun idx : Fin ps.length => useArg ns (port (start+idx.val)) ps[idx.val]) := by
  induction ps generalizing start with
  | nil => rfl
  | cons head tail ih =>
    rw [List.ofFn_succ]
    simp only [inputs,List.getElem_cons_succ,Fin.val_succ]
    rw [ih]
    simp only [Nat.add_assoc,Nat.add_comm 1]
    rfl

theorem cast_list {α : Type} {a b : Nat} (eq : a = b) (f : Fin a → α) :
    List.ofFn f = List.ofFn (fun j : Fin b => f (Fin.cast eq.symm j)) := by
  cases eq
  rfl

theorem arguments (p : Plan rs) (cl : Clause) (found : cl ∈ p.packet.declaration.requirements)
    (sig : cl.Signature rs) (m : Assignment) (typed : Holds p m)
    {s : State} (fit : Models s m) {port : Port}
    (ready : Input s p.packet.registry.constructors p.packet.context.interpretation (rawCap p) cl port) :
    All₂ (Meaning m) (GeneralStoppedOrdinarySite335.demand (child p cl sig)).arguments
      (emittedDemand p cl port.input).arguments := by
  change All₂ (Meaning m) (List.ofFn (argument (child p cl sig)))
    (inputs (names p) port.input 0 cl.arguments)
  rw [named_inputs,cast_list sig.1]
  apply ofFn_pair
  intro idx
  simpa only [Nat.zero_add,Fin.val_cast] using one p cl found sig idx m typed fit ready

theorem literal_outputs (p : Plan rs) (cl : Clause) (sig : cl.Signature rs) (port : Nat → Capture) :
    (emittedDemand p cl port).outputs = (child p cl sig).occurrence.demand.outputs := rfl

end Yulang.GeneralDeclarativeRawReplayArgs344
