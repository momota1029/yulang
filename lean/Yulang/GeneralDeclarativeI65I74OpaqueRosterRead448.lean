import Yulang.GeneralDeclarativeI65I74OpaqueRoster448

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Opaque448.Roster
open Yulang.GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessConstructorModes357 (readUse Mode)
open RetainedSplit446.LocalHeader (selectedHeader selected_header_exact446)
open Checker408 (Problem)
open SplitEscape446

def readBareRow (s : GeneralDeclarativeI65.State) (d : Declaration) : Option (BareRow s d) := do
  if header : selectedHeader s.current.environment d = true then
    match bare : d.head with
    | [.app key []] =>
      let u ← readUse s.current.environment key 0
      match mode : u.mode with
      | .declared [] =>
          if table : s.modes[key]? = some [] then
            let data := (selected_header_exact446 s.current d).mp header
            some ⟨key,bare,u,mode,table,data.1,data.2.1,data.2.2⟩
          else none
      | _ => none
    | _ => none
  else none

theorem read_bare_row_exact448 {s d} (b : BareRow s d) :
    readBareRow s d = some b := by
  have header := (selected_header_exact446 s.current d).mpr ⟨b.noWhere,b.covered,b.checked⟩
  unfold readBareRow
  rw [dite_eq_left header]
  split
  · rename_i n head
    have same := (GeneralDeclarationPatterns.Pattern.app.inj
      (List.singleton_inj.mp (head.symm.trans b.bare))).1
    subst n
    rw [RetainedFull445.read_use_reconstructs_exact_placement445 b.use]
    simp only [Bind.bind,Option.bind]
    split
    · rw [dite_eq_left b.table]
    · rename_i wrong
      exact (wrong b.mode).elim
  · rename_i miss
    exact (miss _ b.bare).elim

def readBareRows (s : GeneralDeclarativeI65.State) : (rows : List Declaration) → Option (BareRows s rows)
  | [] => some .nil
  | d::rest => do
    let current ← readBareRow s d
    let others ← readBareRows s rest
    pure (.next current others)

theorem read_bare_roster_exact448 {s rows} (data : BareRows s rows) :
    readBareRows s rows = some data := by
  induction data with
  | nil => rfl
  | next row rest ih =>
    simp [readBareRows,read_bare_row_exact448 row,ih,Bind.bind,Option.bind,Option.pure_def]

def onePhysical (s : GeneralDeclarativeI65.State) (logical slot : Nat) : Bool :=
  (physicalSources s logical).all (fun found => found == slot)

theorem one_physical_iff_existing_source448 {s logical slot}
    (present : slot ∈ physicalSources s logical) :
    onePhysical s logical slot = true ↔ SinglePhysical s logical := by
  simp only [onePhysical,List.all_eq_true,beq_iff_eq,SinglePhysical]
  constructor
  · intro all a ha b hb
    exact (all a ha).trans (all b hb).symm
  · intro same a ha
    exact same a ha slot present

structure VerifiedPoint (p : Problem) where
  known : BarePoint p.state.core p.root
  safe : ¬RootCycle p.state p.root

/-- The entire original physical source read is finite. The wire names
just one authentic endpoint and a raw certificate. Candidate evidence
and route exclusivity cannot be supplied by the witness. -/
def readBarePoint (p : Problem) (w : NamedWire) : Option (VerifiedPoint p) := do
  let c := p.state.core
  match asked : p.root.demand.arguments with
  | [arg] =>
    if raw : splitCheck446 c.current.ordinary arg.lower w.escape = true then
      match atOrigin : c.origins[w.original]? with
      | none => none
      | some source =>
        match observed : source.endpoint with
        | .nominal key [] =>
          if direct : source.slot = arg.lower ∧ source.slot = arg.upper then
            if one : onePhysical c arg.lower source.slot = true then
              have origin := List.mem_of_getElem? atOrigin
              have directRoute : OriginRoute c source arg.lower := direct.1 ▸ .direct
              have picked : source.slot ∈ physicalSources c arg.lower :=
                physical_sources_exact.mpr ⟨source,origin,directRoute,rfl⟩
              have safe : ¬RootCycle p.state p.root := by
                rintro ⟨entry,member,cycle⟩
                rw [asked] at member
                cases List.mem_singleton.mp member
                exact checked_split_escape_excludes_exact_raw_K2446 raw cycle
              some ⟨⟨arg,asked,source,origin,direct.1,direct.2,key,observed,
                (one_physical_iff_existing_source448 picked).mp one⟩,safe⟩
            else none
          else none
        | _ => none
    else none
  | _ => none

theorem read_bare_point_exact448 {p : Problem} (b : VerifiedPoint p) (w : NamedWire)
    (location : p.state.core.origins[w.original]? = some b.known.rootOriginal)
    (raw : splitCheck446 p.state.core.current.ordinary b.known.arg.lower w.escape = true) :
    readBarePoint p w = some b := by
  let a := b.known
  have picked : a.rootOriginal.slot ∈ physicalSources p.state.core a.arg.lower :=
    physical_sources_exact.mpr ⟨a.rootOriginal,a.authored,a.actualLower ▸ .direct,rfl⟩
  have one := (one_physical_iff_existing_source448 picked).mpr a.physical
  unfold readBarePoint
  split
  · rename_i arg asked
    have eq := List.singleton_inj.mp (asked.symm.trans a.asked)
    subst arg
    dsimp only
    rw [dite_eq_left raw]
    split
    · rename_i miss
      rw [location] at miss
      cases miss
    · rename_i source atSource
      have eq := Option.some.inj (atSource.symm.trans location)
      subst source
      split
      · rename_i k read
        have eq := (CommonRecursiveNominalIntervals.Endpoint.nominal.inj (read.symm.trans a.exact)).1
        subst k
        rw [dite_eq_left (show a.rootOriginal.slot = a.arg.lower ∧ a.rootOriginal.slot = a.arg.upper from
          ⟨a.actualLower,a.actualUpper⟩),dite_eq_left one]
      · rename_i mismatch
        exact (mismatch _ a.exact).elim
  · rename_i mismatch
    exact (mismatch _ a.asked).elim

theorem independent_bare_point_has_finite_wire448 {p : Problem} (b : VerifiedPoint p) :
    ∃ w : NamedWire, readBarePoint p w = some b := by
  have noCycle : ¬GeneralDeclarativeK2Alias321.AliasCycle p.state.core.current.ordinary
      (GeneralDeclarativeGraphRows321.observed p.state.core.current.ordinary) b.known.arg.lower :=
    fun cycle => b.safe ⟨b.known.arg,b.known.asked ▸ List.mem_cons_self,cycle⟩
  obtain ⟨data,passes⟩ := (raw_safe_iff_finite_split_witness446 _ _).mp noCycle
  obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp b.known.authored
  exact ⟨⟨index,data⟩, read_bare_point_exact448 b _ found passes⟩

end Yulang.GeneralDeclarativeI65.I72.Opaque448.Roster
