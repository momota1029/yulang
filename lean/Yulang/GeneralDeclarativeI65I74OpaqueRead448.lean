import Yulang.GeneralDeclarativeI65I74NamedEntry409
import Yulang.GeneralDeclarativeI65I74SelectedEntry447

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Opaque448
open Yulang.GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessConstructorModes357 (readUse)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open Checker408 (Problem Result)
open Named409 (NamedHead VerifiedName)
open RetainedSplit446.LocalHeader (selectedHeader selected_header_exact446)
open SplitEscape446
open List410 (ExactEscapeWire)

structure NamedWire where
  original : Nat
  escape : ExactEscapeWire

/-- Use the original ordered list, actual role metadata and origin. Bare
named syntax makes the recursion inside its nominal declaration opaque;
the unfiltered ordinary K2 check still applies before every positive leaf. -/
def readOpaque (p : Problem) (d : Declaration)
    (whole : visible p.state.core p.root = [d]) (w : NamedWire) :
    Option (VerifiedName p d) := do
  let core := p.state.core
  let env := core.current.environment
  let src := env.source
  if roleSeen : (Checker408.originalRole p).isSome = true then
    if header : selectedHeader env d = true then
      if boundary : p.root.demand.outputs.isEmpty = true then
        match named : d.head, args : p.root.demand.arguments with
        | [.app key []], [arg] =>
          if ranked : splitCheck446 core.current.ordinary arg.lower w.escape = true then
            match atOrigin : core.origins[w.original]? with
            | none => none
            | some origin =>
              match endpoint : origin.endpoint with
              | .nominal originKey [] =>
                if same : originKey = key ∧ origin.slot = arg.lower ∧ origin.slot = arg.upper then
                  let actual ← readUse env key 0
                  if mode : names actual.mode 0 = some [] then
                    if table : core.modes[key]? = some [] then
                      let checked := (selected_header_exact446 core.current d).mp header
                      have author : ∃ row ∈ src.roles.rows, row.role = p.root.demand.role := by
                        cases roleAt : Checker408.originalRole p with
                        | none => simp [roleAt] at roleSeen
                        | some row =>
                          have original := GeneralSourceMetadataRoles291.indexed roleAt
                          exact ⟨row,original.1,original.2⟩
                      let matched : NamedHead p.state p.root d :=
                        ⟨whole,author,checked.2.2,checked.2.1,arg,args,key,named,origin,List.mem_of_getElem? atOrigin,
                          same.2.1,same.2.2,by rw [endpoint,same.1],actual,mode,table,checked.1,List.isEmpty_iff.mp boundary⟩
                      let safe : ¬RootCycle p.state p.root := by
                        rintro ⟨a,mem,cycle⟩
                        rw [args] at mem
                        cases List.mem_singleton.mp mem
                        exact checked_split_escape_excludes_exact_raw_K2446 ranked cycle
                      some ⟨matched,safe⟩
                    else none
                  else none
                else none
              | _ => none
          else none
        | _,_ => none
      else none
    else none
  else none

private theorem key_seen {A : Type} (n : Nat) (rows : List (Nat × A))
    (h : ∃ a, (n,a) ∈ rows) :
    (GeneralSourceMetadataFiniteLookup291.get n rows).isSome = true := by
  induction rows with
  | nil => rcases h with ⟨_,atNil⟩; cases atNil
  | cons row rows ih =>
    rcases row with ⟨name,item⟩
    by_cases same : n = name
    · simp [GeneralSourceMetadataFiniteLookup291.get,same]
    · rw [GeneralSourceMetadataFiniteLookup291.get,ite_eq_right same]
      apply ih
      obtain ⟨a,member⟩ := h
      rcases List.mem_cons.mp member with hit|tail
      · exact (same (congrArg Prod.fst hit)).elim
      · exact ⟨a,tail⟩

theorem original_role_is_read448 {p : Problem}
    (h : ∃ row ∈ p.state.core.current.environment.source.roles.rows, row.role = p.root.demand.role) :
    (Checker408.originalRole p).isSome = true := by
  obtain ⟨row,member,role⟩ := h
  unfold Checker408.originalRole
  apply key_seen
  exact ⟨row,List.mem_map.mpr ⟨row,member,by simp [role]⟩⟩

theorem read_opaque_exact448 {p : Problem} {d : Declaration} (a : VerifiedName p d)
    (w : NamedWire) (atOrigin : p.state.core.origins[w.original]? = some a.known.origin)
    (safe : splitCheck446 p.state.core.current.ordinary a.known.arg.lower w.escape = true) :
    readOpaque p d a.known.only w = some a := by
  let x := a.known
  have role := original_role_is_read448 x.authoredRole (p := p)
  have header := (selected_header_exact446 p.state.core.current d).mpr
    ⟨x.noWhere,x.covered,x.checked⟩
  have outputs : p.root.demand.outputs.isEmpty = true := by simp [x.noOutputs]
  unfold readOpaque
  rw [dite_eq_left role,dite_eq_left header,dite_eq_left outputs]
  split
  · rename_i key arg written args
    have keyEq := (GeneralDeclarationPatterns.Pattern.app.inj
      (List.singleton_inj.mp (written.symm.trans x.named))).1
    have argEq := List.singleton_inj.mp (args.symm.trans x.asked)
    subst key
    subst arg
    rw [dite_eq_left safe]
    split
    · rename_i missing
      rw [atOrigin] at missing
      cases missing
    · rename_i o found
      have originEq := Option.some.inj (found.symm.trans atOrigin)
      subst o
      split
      · rename_i k endpoint
        have key := (CommonRecursiveNominalIntervals.Endpoint.nominal.inj
          (endpoint.symm.trans x.endpoint)).1
        subst k
        rw [dite_eq_left (show x.key = x.key ∧ _ from ⟨rfl,x.lo,x.hi⟩)]
        rw [RetainedFull445.read_use_reconstructs_exact_placement445 x.use]
        simp only [Bind.bind,Option.bind]
        rw [dite_eq_left x.mode,dite_eq_left x.table]
      · rename_i wrong
        exact (wrong _ x.endpoint).elim
  · rename_i wrong
    exact (wrong _ _ x.named x.asked).elim

theorem independent_opaque_has_wire448 {p : Problem} {d : Declaration} (a : VerifiedName p d) :
    ∃ w : NamedWire, readOpaque p d a.known.only w = some a := by
  have noCycle : ¬GeneralDeclarativeK2Alias321.AliasCycle p.state.core.current.ordinary
      (GeneralDeclarativeGraphRows321.observed p.state.core.current.ordinary) a.known.arg.lower :=
    fun cycle => a.rawSafe ⟨a.known.arg,a.known.asked ▸ List.mem_cons_self,cycle⟩
  obtain ⟨escape,safe⟩ := (raw_safe_iff_finite_split_witness446 _ _).mp noCycle
  obtain ⟨idx,atOrigin⟩ := List.mem_iff_getElem?.mp a.known.authored
  exact ⟨⟨idx,escape⟩,read_opaque_exact448 a _ atOrigin safe⟩


end Yulang.GeneralDeclarativeI65.I72.Opaque448
