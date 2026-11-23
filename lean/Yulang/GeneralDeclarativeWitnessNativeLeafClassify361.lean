import Yulang.GeneralDeclarativeWitnessMixedDependency361

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 59000
set_option maxHeartbeats 57000000
namespace Yulang.GeneralDeclarativeWitnessNativeLeafClassify361
open GeneralDeclarativeWitnessNativeDirectSource361 (Wire)
open GeneralDeclarativeWitnessNativePortTransport361 (Port view Part)
open GeneralDeclarativeWitnessNativeKinds361 (Shaped read)
open GeneralDeclarativeWitnessMixedDependency361 (Path Node height exactGraph no_strict_loop board_checked)
open GeneralDeclarativeWitnessNativeValue360 (Code)
open GeneralDeclarativeWitnessNativeInstall360 (Fits NativeViews)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority)
open GeneralDeclarativeWitnessNativeLowerCut361 (levels)
open GeneralDeclarativeWitnessRank350 (sound)
open GeneralDeclarativeWitnessSequentialNative360 (Sequence)
open GeneralDeclarativeWitnessSequentialReceiver361 (Received)
open GeneralDeclarativeWitnessNativeReceiver360 (key)
open GeneralDeclarativeWitnessNestedInstall360 (Run)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Frontier Tree Dictionary Result Classify)

def visible {negative r} (s : @Sequence negative r) : List Declaration :=
  r.env.source.declarations.filter (fun impl => impl.role == s.receiver.role)

def isHead : Code → Bool
  | .leaf _ => false
  | _ => true

structure Choice {negative : Bool} {r : Run negative} {s : Sequence r} {gate : ReleaseAuthority} {wire : Wire}
    (port : Port s gate wire) where
  impl : Declaration
  only : visible s = [impl]
  binder : Nat
  authoredShape : impl.head.map normalize = [.var binder] ∧ impl.requirements = [] ∧
    impl.associated = [] ∧ s.receiver.outputs = []
  frame : impl = port.stated.receiver
  observed : Shaped r.env r.typed.write.code
  hasHead : isHead r.typed.write.code = true
  noLoop : ∀ projection n,¬ Path s.final projection true n n

theorem source_visible {negative} {r : Run negative} {s : Sequence r}
    {gate wire} (p : Port s gate wire) : p.stated.receiver ∈ visible s := by
  have occurs := List.mem_of_getElem? p.stated.targetSource
  have role := p.stated.childIdentity.2
  have parent := GeneralDeclarativeWitnessNativeDirectSource361.same_actual_source p.stated s.continuation
  have row : s.continuation.impl.requirements[wire.clausePosition]? = some p.stated.row := by
    rw [parent]; exact p.stated.actualRow
  have childRole : s.receiver.role = p.stated.row.role := by
    have equals := p.atChild
    simpa [GeneralDeclarativeWitnessNativePreparation360.Prepared.kids,
      GeneralDeclarativeEmissionForest322.children,row,GeneralDeclarativeSourceEmission322.demand] using
      (congrArg (Option.map Demand.role) equals).symm
  exact List.mem_filter.mpr ⟨occurs,by simp [role,childRole]⟩

/-- A positive finite check on the whole visible role table, independently
checked constructor kinds and authorized input lineage. It never calls
the receiver body compiler. No result is a missing fragment witness,
not rejection or deferral of the corresponding Yulang program. -/
def choose {negative} {r : Run negative} {s : Sequence r} {gate wire} (p : Port s gate wire) :
    Option (Choice p) :=
  match only : visible s with
  | [impl] =>
    have same : impl = p.stated.receiver := (List.mem_singleton.mp (only ▸ source_visible p)).symm
    match head : impl.head.map normalize with
    | [.var binder] =>
      if body : impl.requirements = [] ∧ impl.associated = [] ∧ s.receiver.outputs = [] then
        if graph : exactGraph s = true ∧ isHead r.typed.write.code = true then do
          let observed ← read r.env r.typed.write.code
          have rank := Bool.and_eq_true_iff.mp graph.1
          some ⟨impl,only,binder,⟨head,body⟩,same,observed,graph.2,
            fun _ => no_strict_loop (sound rank.1) (board_checked rank.2)⟩
        else none
      else none
    | _ => none
  | _ => none

inductive Local {negative : Bool} {r : Run negative} {s : Sequence r} {gate : ReleaseAuthority} {wire : Wire}
    (p : Port s gate wire) : Demand → Frontier Demand → Prop where
  | terminal (localChoice : Choice p) : Local p s.receiver (.selected localChoice.impl.id [])

theorem declarative_leaf {negative} {r : Run negative} {s : Sequence r} {gate wire} {p : Port s gate wire}
    (c : Choice p) : Classify (Local p) s.receiver (.selected (.node c.impl.id [])) :=
  ⟨.selected c.impl.id [],.selected (.terminal c) .nil,.selected .nil (.selected rfl)⟩

theorem actual_compiler_agrees_on_declaration {negative} {r : Run negative} {s : Sequence r} {gate wire}
    {p : Port s gate wire} (scope : wire.child = key) (c : Choice p) (out : Received s) :
    out.prepared.impl = c.impl := by
  rw [c.frame]
  have finds := p.stated.targetSource
  rw [scope] at finds
  exact Option.some.inj (out.prepared.authored.symm.trans finds)

end Yulang.GeneralDeclarativeWitnessNativeLeafClassify361
