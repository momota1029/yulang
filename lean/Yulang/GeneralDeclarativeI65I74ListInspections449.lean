import Yulang.GeneralDeclarativeI65I74ListEntry410
import Yulang.GeneralDeclarativeI65I74SplitCompact447

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ListSites449
open Yulang.GeneralDeclarativeI65
open List410 (ExactEscapeWire InvariantListHead listPoint410 invariantValue410)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWitnessConstructorModes357 (Use)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open PresenceNormalForm (Atom)
open SplitEscape446 SplitEscape446.SplitCompact447

/-- An inspected constructor position is based on its actual authored
point endpoint and mode, not on an arbitrary name submitted for K2. -/
structure WrittenListSite (s : GeneralDeclarativeI65.State) (a : Capture) (h : Pattern) where
  key : Nat
  binder : Nat
  headSyntax : h = .app key [.var binder]
  origin : Origin
  authored : origin ∈ s.origins
  lower : origin.slot = a.lower
  center : origin.slot = a.center
  upper : origin.slot = a.upper
  payload : Nat
  endpoint : origin.endpoint = listPoint410 key payload
  use : Use s.current.environment key 1
  mode : names use.mode 1 = some [invariantValue410]
  table : s.modes[key]? = some [invariantValue410]
  atom : Atom.tyLe (.var payload) (.var payload) ∈ s.current.ordinary.normal.ordinary

/-- Exactly the site at each written, non-variable head. A plain
binder captures its authored payload without adding an inspected site. -/
inductive ListFrameVisits (s : GeneralDeclarativeI65.State) : List Capture → List Pattern → List Nat → Prop where
  | nil : ListFrameVisits s [] [] []
  | next {arg head args heads positions}
      (read : WrittenListSite s arg head)
      (tail : ListFrameVisits s args heads positions) :
      ListFrameVisits s (arg :: args) (head :: heads) (arg.lower :: positions)

theorem list_frame_sites_are_ordered_original_roots449 {s args heads positions}
    (observedFrame : ListFrameVisits s args heads positions) :
    positions = args.map Capture.lower := by
  induction observedFrame with
  | nil => rfl
  | next _ _ ih => simp [ih]

theorem one_authored_list_has_exact_visit449 {s q d} (a : InvariantListHead s q d) :
    ListFrameVisits s.core q.demand.arguments d.head [a.arg.lower] := by
  rw [a.asked,a.named]
  exact .next ⟨a.key,a.binder,rfl,a.origin,a.authored,a.lower,a.center,a.upper,
    a.payload,a.endpoint,a.use,a.mode,a.table,a.atom⟩ .nil

theorem literal_binder_does_not_inspect_payload449 {s a h} (input : WrittenListSite s a h)
    (view : GeneralDeclarativeK2Graph321.View) (index : Nat) :
    ¬GeneralDeclarativeInspect321.Visit view input.payload (.variable input.binder) index :=
  GeneralDeclarativeInspect321.variable_has_no_visit

def checkSiteTable (s : GeneralDeclarativeHead320.State) : List Nat → List ExactEscapeWire → Bool
  | [],[] => true
  | site::rest,certificate::later => splitCheck446 s site certificate && checkSiteTable s rest later
  | _,_ => false

/-- No site identity is passed by the wire: it is zipped in the exact
derived order. Missing or extra certificate rows fail. -/
theorem accepted_table_has_exact_count449 {s sites certs}
    (ok : checkSiteTable s sites certs = true) : certs.length = sites.length := by
  induction sites generalizing certs with
  | nil => cases certs <;> simp [checkSiteTable] at ok ⊢
  | cons site sites ih =>
    cases certs with
    | nil => simp [checkSiteTable] at ok
    | cons cert rest =>
      obtain ⟨_,tail⟩ := Bool.and_eq_true_iff.mp ok
      simp [ih tail]

def SitesSafe (s : GeneralDeclarativeHead320.State) (sites : List Nat) : Prop :=
  ∀ position ∈ sites, ¬AliasCycle s (observed s) position

theorem table_only_validates_actual_safe_sites449 {s sites certs}
    (ok : checkSiteTable s sites certs = true) : SitesSafe s sites := by
  induction sites generalizing certs with
  | nil => intro site membership; cases membership
  | cons current rest ih =>
    cases certs with
    | nil => simp [checkSiteTable] at ok
    | cons cert tail =>
      obtain ⟨front,back⟩ := Bool.and_eq_true_iff.mp ok
      intro site member
      rcases List.mem_cons.mp member with equal|later
      · subst site
        exact checked_split_escape_excludes_exact_raw_K2446 front
      · exact ih back site later

theorem exact_per_site_finite_witnesses449 (s : GeneralDeclarativeHead320.State) (sites : List Nat) :
    SitesSafe s sites ↔ ∃ certs : List ExactEscapeWire, checkSiteTable s sites certs = true := by
  constructor
  · intro every
    induction sites with
    | nil => exact ⟨[],rfl⟩
    | cons site rest ih =>
      obtain ⟨front,good,_,_⟩ := (raw_safe_iff_small_witness447 s site).mp
        (every site List.mem_cons_self)
      obtain ⟨tail,ready⟩ := ih (fun n member => every n (List.mem_cons_of_mem _ member))
      exact ⟨front::tail,Bool.and_eq_true_iff.mpr ⟨good,ready⟩⟩
  · rintro ⟨certs,yes⟩
    exact table_only_validates_actual_safe_sites449 yes

theorem inspection_safety_is_original_root_safety449 {s : I72.State} {q d sites}
    (trace : ListFrameVisits s.core q.demand.arguments (d : GeneralDeclarations.Declaration).head sites) :
    SitesSafe s.core.current.ordinary sites ↔ ¬RootCycle s q := by
  have order := list_frame_sites_are_ordered_original_roots449 trace
  rw [order]
  constructor
  · intro good
    rintro ⟨arg,authored,cycle⟩
    exact good arg.lower (List.mem_map.mpr ⟨arg,authored,rfl⟩) cycle
  · intro good site member cycle
    obtain ⟨arg,authored,exactSite⟩ := List.mem_map.mp member
    exact good ⟨arg,authored,exactSite ▸ cycle⟩

end Yulang.GeneralDeclarativeI65.I72.ListSites449
