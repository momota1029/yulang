import Yulang.GeneralDeclarativeI65I74ListFrameOrigin449

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ListSites449.Frame
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem Result)
open GeneralDeclarations (Declaration DeclarationChecked)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open RetainedSplit446.LocalHeader (selectedHeader selected_header_exact446)
open List410 (ExactEscapeWire)

structure ListFrameChoice (p : Problem) (d : Declaration) where
  only : visible p.state.core p.root = [d]
  roster : AuthoredFrame p.state.core p.root.demand.arguments d.head
  someInput : p.root.demand.arguments ≠ []
  distinct : (roster.bindings.map Prod.fst).Nodup
  authoredRole : ∃ row ∈ p.state.core.current.environment.source.roles.rows,
    row.role = p.root.demand.role
  rolesValid : GeneralSourceMetadataRoles291.Valid p.state.core.current.environment.source.roles
  checked : DeclarationChecked (authoredRegistry p.state.core.current).constructors
    (authoredRegistry p.state.core.current).roles d
  covered : DeclarationCovered p.state.core.current.environment d
  noWhere : d.requirements = []
  noOutputs : p.root.demand.outputs = []
  safe : ¬RootCycle p.state p.root

structure FrameWire where
  origins : List Nat
  certificates : List ExactEscapeWire

def readListFrameChoice (p : Problem) (d : Declaration)
    (scope : visible p.state.core p.root = [d]) (w : FrameWire) : Option (ListFrameChoice p d) := do
  let core := p.state.core
  if role : (Checker408.originalRole p).isSome = true then
    if valid : GeneralSourceMetadataRoles291.check core.current.environment.source.roles = true then
      if header : selectedHeader core.current.environment d = true then
        if out : p.root.demand.outputs.isEmpty = true then
          if hasArg : p.root.demand.arguments ≠ [] then
            let roster ← readAuthoredFrame core p.root.demand.arguments d.head w.origins
            if unique : (roster.bindings.map Prod.fst).Nodup then
              if clear : checkSiteTable core.current.ordinary
                  (p.root.demand.arguments.map Capture.lower) w.certificates = true then
                have roleBound : ∃ row ∈ core.current.environment.source.roles.rows,
                    row.role = p.root.demand.role := by
                  cases present : Checker408.originalRole p with
                  | none => simp [present] at role
                  | some row =>
                    have actual := GeneralSourceMetadataRoles291.indexed present
                    exact ⟨row,actual.1,actual.2⟩
                let checked := (selected_header_exact446 core.current d).mp header
                let safe := (inspection_safety_is_original_root_safety449 (d := d) roster.visits).mp
                  (table_only_validates_actual_safe_sites449 clear)
                some ⟨scope,roster,hasArg,unique,roleBound,
                  (GeneralSourceMetadataRoles291.check_exact _).mp valid,checked.2.2,checked.2.1,
                  checked.1,List.isEmpty_iff.mp out,safe⟩
              else none
            else none
          else none
        else none
      else none
    else none
  else none

theorem independent_list_frame_replays_exactly449 {p : Problem} {d : Declaration}
    (a : ListFrameChoice p d) : ∃ w, readListFrameChoice p d a.only w = some a := by
  obtain ⟨indices,replayed⟩ := independent_frame_has_exact_origin_indices449 a.roster
  have safe := (inspection_safety_is_original_root_safety449 (d := d) a.roster.visits).mpr a.safe
  obtain ⟨cuts,pass⟩ := (exact_per_site_finite_witnesses449 p.state.core.current.ordinary
    (p.root.demand.arguments.map Capture.lower)).mp safe
  refine ⟨⟨indices,cuts⟩,?_⟩
  have role := Opaque448.original_role_is_read448 a.authoredRole (p := p)
  have header := (selected_header_exact446 p.state.core.current d).mpr ⟨a.noWhere,a.covered,a.checked⟩
  have valid := (GeneralSourceMetadataRoles291.check_exact _).mpr a.rolesValid
  have out : p.root.demand.outputs.isEmpty = true := List.isEmpty_iff.mpr a.noOutputs
  unfold readListFrameChoice
  rw [dite_eq_left role,dite_eq_left valid,dite_eq_left header,dite_eq_left out,
    dite_eq_left a.someInput,replayed]
  simp only [Bind.bind,Option.bind,dite_eq_left a.distinct,dite_eq_left pass]

def ListFrameChoice.head {p d} (a : ListFrameChoice p d) : SourceHead p.state.core p.root d :=
  .ordered a.roster.capture (distinct_authored_bindings_have_exact_list_heads449 a.roster a.distinct)

def ListFrameChoice.candidate {p d} (a : ListFrameChoice p d) : AuthoredCandidate p.state.core p.root d :=
  ⟨by simp [a.only],a.covered,a.checked.signature,a.head⟩

def ListFrameChoice.tape {p d} (a : ListFrameChoice p d) :
    CandidateTape p.state.core p.root (visible p.state.core p.root) :=
  a.only.symm ▸ .next (.matched a.candidate) .nil

theorem actual_single_declaration_list_frame_is_settled449 {p d} (a : ListFrameChoice p d) :
    TapedMatch p.state.core p.root a.tape d := by
  have localShape : ∀ rows (h : rows = [d]),
      let t : CandidateTape p.state.core p.root rows := h.symm ▸ .next (.matched a.candidate) .nil
      t.waits = false ∧ t.live = [d] := by
    intro rows h
    cases h
    exact ⟨rfl,rfl⟩
  exact ⟨a.safe,(localShape _ a.only).1,(localShape _ a.only).2⟩

end Yulang.GeneralDeclarativeI65.I72.ListSites449.Frame
