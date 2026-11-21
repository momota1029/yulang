import Yulang.GeneralDeclarativeEmissionForest322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEmissionErasure322
open GeneralDeclarativeSourceEmission322 (Names demand inputs inputs_match_source outputs_match_source)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration Clause)
open GeneralDeclarationPatterns (Pattern)
open GeneralSourceState (Output)

abbrev Requests := Nat × List (Nat × Nat) × List Output

def forgetCenter (d : Demand) : Requests :=
  (d.role,d.arguments.map (fun arg => (arg.lower,arg.upper)),d.outputs)

def oldDemand (d : GeneralSourceState.Demand roles) : Requests :=
  (d.role,List.ofFn d.arguments,d.outputs)

def oldPlacement {roles : Roles.RoleDecls} (p : Placement) (clause : Clause) :
    GeneralDeclarationDemands.Allocation roles clause :=
  ⟨fun i => ((p.compound clause i.val).lower,(p.compound clause i.val).upper),p.targets clause⟩

theorem input_length (names : Names) (compound : Nat → Capture) (i : Nat) (ps : List Pattern) :
    (inputs names compound i ps).length = ps.length := by
  induction ps generalizing i with
  | nil => rfl
  | cons _ more ih => simp [inputs,ih]

theorem one_source {roles : Roles.RoleDecls} (d : Declaration) (c : Clause)
    (valid : c.Signature roles) (names : Names) (p : Placement) :
    forgetCenter (demand d c names (p.compound c) (p.targets c)) =
    oldDemand (GeneralDeclarationDemands.childDemand d c valid names.old (oldPlacement p c)) := by
  let actual := demand d c names (p.compound c) (p.targets c)
  let fromSource := GeneralDeclarationDemands.childDemand d c valid names.old (oldPlacement p c)
  have n : actual.arguments.length = (roles c.role).arity := by
    change (inputs names (p.compound c) 0 c.arguments).length = _
    exact (input_length ..).trans valid.1
  have generated : actual.arguments.map (fun a => (a.lower,a.upper)) = List.ofFn fromSource.arguments := by
    apply List.ext_getElem
    · simpa [fromSource,GeneralDeclarationDemands.childDemand] using n
    · intro i earlier later
      have within : i < (roles c.role).arity := by simpa only [List.length_map,n] using earlier
      obtain ⟨arg,there,old⟩ := inputs_match_source d c valid names (p.compound c) (p.targets c) ⟨i,within⟩
      have inActual : i < actual.arguments.length := n.symm ▸ within
      have atPos : actual.arguments[i]'inActual = arg := by
        have exactAt : actual.arguments[i]? = some (actual.arguments[i]'inActual) := List.getElem?_eq_getElem inActual
        exact Option.some.inj (exactAt.symm.trans there)
      simpa only [List.getElem_map,List.getElem_ofFn,atPos,fromSource,oldPlacement] using old
  exact Prod.ext rfl (Prod.ext generated (outputs_match_source d c valid names (p.compound c) (p.targets c)))

theorem all_source {roles : Roles.RoleDecls} (d : Declaration) (valid : d.Signature roles)
    (names : Names) (p : Placement) (invocation : Nat) :
    (children d names p).map forgetCenter =
      (GeneralDeclarationDemands.emitAll invocation d valid names.old (oldPlacement p)).map (fun entry => oldDemand entry.demand) := by
  calc
    _ = d.requirements.attach.map (fun item =>
      forgetCenter (demand d item.val names (p.compound item.val) (p.targets item.val))) := by
        simp [children,List.map_map,Function.comp_def]
    _ = _ := by
      simp only [GeneralDeclarationDemands.emitAll,List.map_map,Function.comp_def]
      apply List.map_congr_left
      intro item _
      exact one_source d item.val (valid.2.2.2 item.val item.property) names p

end Yulang.GeneralDeclarativeEmissionErasure322
