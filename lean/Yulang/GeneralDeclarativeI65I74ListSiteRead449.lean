import Yulang.GeneralDeclarativeI65I74ListInspections449
import Yulang.GeneralDeclarativeI65I74OpaqueWholeEntry448

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ListSites449
open Yulang.GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessConstructorModes357 (readUse)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open Checker408 (Problem)
open PresenceNormalForm (Atom)
open List410 (ExactEscapeWire VerifiedList InvariantListHead invariantValue410 listPoint410)
open RetainedSplit446.LocalHeader (selectedHeader selected_header_exact446)
open SplitEscape446

structure Wire where
  original : Nat
  cuts : List ExactEscapeWire


open PresenceNormalForm (Atom)

/-- The witness has only the origin-table index and raw escape colours.
Read the original binder and point endpoint in the same problem. The
raw proof visits the demanded root; a literal variable does not visit
its payload, even if that payload can itself exhibit a closed path. -/
def readListSites (p : Problem) (d : Declaration)
    (whole : visible p.state.core p.root = [d]) (w : Wire) :
    Option (VerifiedList p d) := do
  let core := p.state.core
  let env := core.current.environment
  let src := env.source
  if roleSeen : (Checker408.originalRole p).isSome = true then
    if roleValid : GeneralSourceMetadataRoles291.check src.roles = true then
      if header : selectedHeader env d = true then
        if boundary : p.root.demand.outputs.isEmpty = true then
          match named : d.head, args : p.root.demand.arguments with
          | [.app key [.var binder]], [arg] =>
            if clear : checkSiteTable core.current.ordinary [arg.lower] w.cuts = true then
              match atOrigin : core.origins[w.original]? with
              | none => none
              | some origin =>
                match endpoint : origin.endpoint with
                | .nominal originKey [.inl (.point (.ordinary (.var payload)))] =>
                  if same : originKey = key ∧ origin.slot = arg.lower ∧
                      origin.slot = arg.center ∧ origin.slot = arg.upper then
                    let actual ← readUse env key 1
                    if mode : names actual.mode 1 = some [invariantValue410] then
                      if table : core.modes[key]? = some [invariantValue410] then
                        if atom : (Atom.tyLe (.var payload) (.var payload) : Atom Nat)
                            ∈ core.current.ordinary.normal.ordinary then
                          let knownRoles := (GeneralSourceMetadataRoles291.check_exact _).mp roleValid
                          let headerFacts := (selected_header_exact446 core.current d).mp header
                          let noOut := List.isEmpty_iff.mp boundary
                          have author : ∃ row ∈ src.roles.rows, row.role = p.root.demand.role := by
                            cases roleAt : Checker408.originalRole p with
                            | none => simp [roleAt] at roleSeen
                            | some row =>
                              have original := GeneralSourceMetadataRoles291.indexed roleAt
                              exact ⟨row,original.1,original.2⟩
                          let matched : InvariantListHead p.state p.root d :=
                            ⟨whole,author,knownRoles,headerFacts.2.2,headerFacts.2.1,arg,args,key,binder,named,origin,
                              List.mem_of_getElem? atOrigin,same.2.1,same.2.2.1,same.2.2.2,
                              payload,by rw [endpoint,same.1]; rfl,actual,mode,table,atom,headerFacts.1,noOut⟩
                          let safe : ¬RootCycle p.state p.root := by
                            rintro ⟨a,position,cycle⟩
                            rw [args] at position
                            cases List.mem_singleton.mp position
                            exact table_only_validates_actual_safe_sites449 clear arg.lower List.mem_cons_self cycle
                          some ⟨matched,safe⟩
                        else none
                      else none
                    else none
                  else none
                | _ => none
            else none
          | _,_ => none
        else none
      else none
    else none
  else none

theorem checked_list_footprint_is_actual449 {p d scope w v}
    (_h : readListSites p d scope w = some v) :
    ListFrameVisits p.state.core p.root.demand.arguments d.head [v.known.arg.lower] :=
  one_authored_list_has_exact_visit449 v.known

theorem read_derived_list_exact449 {p : Problem} {d : Declaration} (a : VerifiedList p d)
    (w : Wire) (found : p.state.core.origins[w.original]? = some a.known.origin)
    (table : checkSiteTable p.state.core.current.ordinary [a.known.arg.lower] w.cuts = true) :
    readListSites p d a.known.only w = some a := by
  let b := a.known
  have role := Opaque448.original_role_is_read448 (p := p) b.authoredRole
  have valid := (GeneralSourceMetadataRoles291.check_exact _).mpr b.validRoles
  have header := (selected_header_exact446 p.state.core.current d).mpr ⟨b.noWhere,b.covered,b.checked⟩
  have outputs : p.root.demand.outputs.isEmpty = true := by simp [b.noOutputs]
  unfold readListSites
  rw [dite_eq_left role,dite_eq_left valid,dite_eq_left header,dite_eq_left outputs]
  split
  · rename_i key binder arg head args
    have shape := GeneralDeclarationPatterns.Pattern.app.inj
      (List.singleton_inj.mp (head.symm.trans b.named))
    have ke := shape.1
    have bi := GeneralDeclarationPatterns.Pattern.var.inj (List.singleton_inj.mp shape.2)
    have atArg := List.singleton_inj.mp (args.symm.trans b.asked)
    subst key
    subst binder
    subst arg
    rw [dite_eq_left table]
    split
    · rename_i missing
      rw [found] at missing
      cases missing
    · rename_i original picked
      have baseline := Option.some.inj (picked.symm.trans found)
      subst original
      split
      · rename_i originKey payload endpoint
        have parts := CommonRecursiveNominalIntervals.Endpoint.nominal.inj
          (endpoint.symm.trans b.endpoint)
        have keyEq := parts.1
        have payloadEq := Core.PresenceGeneration.TyTerm.var.inj
          (CommonRecursiveNominalIntervals.Endpoint.ordinary.inj
            (CommonRecursiveNominalIntervals.Bounds.point.inj
              (Sum.inl.inj (List.singleton_inj.mp parts.2))))
        subst originKey
        subst payload
        rw [dite_eq_left (show b.key = b.key ∧ _ from ⟨rfl,b.lower,b.center,b.upper⟩)]
        rw [RetainedFull445.read_use_reconstructs_exact_placement445 b.use]
        simp only [Bind.bind,Option.bind]
        rw [dite_eq_left b.mode,dite_eq_left b.table,dite_eq_left b.atom]
      · rename_i wrong
        exact (wrong _ _ b.endpoint).elim
  · rename_i wrong
    exact (wrong _ _ _ b.named b.asked).elim

theorem independent_list_has_exact_per_site_wire449 {p : Problem} {d : Declaration}
    (a : VerifiedList p d) :
    ∃ w : Wire, readListSites p d a.known.only w = some a := by
  let b := a.known
  have safe := (inspection_safety_is_original_root_safety449
    (one_authored_list_has_exact_visit449 b)).mpr a.rawSafe
  obtain ⟨cuts,yes⟩ := (exact_per_site_finite_witnesses449 p.state.core.current.ordinary
    [b.arg.lower]).mp safe
  obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp b.authored
  exact ⟨⟨index,cuts⟩,read_derived_list_exact449 a _ found yes⟩


end Yulang.GeneralDeclarativeI65.I72.ListSites449
