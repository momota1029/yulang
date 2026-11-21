import Yulang.GeneralDeclarativeInlineFootprint331

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlineOrigins331
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Supported Origin Available restriction backed_iff)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeInlineFootprint331 (Replay trace)
open GeneralDeclarativeInlineLineage331 (Trail carries)
open GeneralDeclarativeInlineMaterial331 (ordinary seed)
open GeneralDeclarativeInlineAllocation331 (jobs)
open GeneralDeclarativeInlineGround331 (job_spelling)
open GeneralDeclarativeNewNames321 (numbered rhs_exact)

abbrev Requirement := Equation × Origin

def fromOrigins {s : State} (p : Supported s done) (rows : List Requirement) : Prop :=
  ∀ entry ∈ rows, p.derivesFrom entry.1 entry.2
def owners (rows : List Requirement) : List Nat :=
  rows.flatMap (fun entry => match entry.2 with | .source => [] | .output owner => [owner])
def complete (done : Nat → Prop) (rows : List Requirement) : Prop :=
  ∀ owner ∈ owners rows, done owner

theorem liveIff (done : Nat → Prop) (rows : List Requirement) :
    complete done rows ↔ ∀ entry ∈ rows, Available done entry.2 := by
  constructor
  · intro justified entry occurs
    cases h : entry.2 with
    | source => exact .source
    | output owner =>
      exact .completed (justified owner (List.mem_flatMap.mpr ⟨entry,occurs,by rw [h]; exact List.mem_cons_self⟩))
  · intro active owner used
    obtain ⟨entry,listed,looked⟩ := List.mem_flatMap.mp used
    cases h : entry.2 with
    | source =>
      simp only [h,List.not_mem_nil] at looked
    | output other =>
      rw [h] at looked
      cases List.mem_singleton.mp looked
      have actual := active entry listed
      rw [h] at actual
      cases actual with
      | completed done => exact done

theorem decorate {s : State} (p : Supported s done) (rows : List Equation)
    (uses : rows ⊆ (restriction p).equations) :
    ∃ linked : List Requirement, linked.map Prod.fst = rows ∧
      fromOrigins p linked ∧ complete done linked := by
  induction rows with
  | nil =>
    exact ⟨[],rfl,fun e h => False.elim (List.not_mem_nil h),fun owner h => False.elim (List.not_mem_nil h)⟩
  | cons row later ih =>
    obtain ⟨o,written,ready⟩ := (backed_iff p row).mp (uses List.mem_cons_self)
    obtain ⟨links,exactRows,original,current⟩ := ih (fun _ h => uses (List.mem_cons_of_mem _ h))
    refine ⟨(row,o)::links,by simp [exactRows],?_,(liveIff _ _).mpr ?_⟩
    · intro entry h
      rcases List.mem_cons.mp h with rfl|other
      · exact written
      · exact original _ other
    · intro entry h
      rcases List.mem_cons.mp h with rfl|other
      · exact ready
      · exact (liveIff _ _).mp current _ other

theorem rows_live {s : State} (p : Supported s done) (origins : fromOrigins p links)
    (completed : complete done links) :
    links.map Prod.fst ⊆ (restriction p).equations := by
  intro row kept
  obtain ⟨entry,inside,rfl⟩ := List.mem_map.mp kept
  exact (backed_iff _ _).mpr ⟨entry.2,origins _ inside,(liveIff _ _).mp completed _ inside⟩

/-- For any actual inline read, retain only the row occurrences used
by its derivation and one actual available origin for each such row.
On another supported view, the identical symbolic occurrences are
replayed when those exact origins and normal bounds still hold.
Dependencies are conjunctive. They are not renamed to source. -/
theorem exact_uses {s : State} {p : Supported s done}
    (source : Read (restriction p) mode input code seen) :
    ∃ links : List Requirement, fromOrigins p links ∧ complete done links ∧
      ∀ (t : State) {later : Nat → Prop} (q : Supported t later), s.normal = t.normal →
        fromOrigins q links → complete later links →
        Read (restriction q) mode input code seen := by
  obtain ⟨rows,inside,replay⟩ := trace source
  obtain ⟨links,same,why,active⟩ := decorate p rows inside
  refine ⟨links,why,active,?_⟩
  intro t later q normal known complete
  exact replay (restriction q) normal (same ▸ rows_live q known complete)

/-- A compiled field job may be replayed with a finite conjunction of
original owners still required. The equation's truth in the current
table cannot discharge an unfinished owner's requirement. -/
theorem allocation_origins {s : State} {p : Supported s done}
    (source : Read (restriction p) .actual (.variable arg.center) code seen)
    (freshRow : row ∈ ordinary s arg keep seen) :
    ∃ loc ∈ seen, row.right = loc.term ∧
      (∀ n, loc.term ≠ .variable n) ∧
      ∃ links : List Requirement, fromOrigins p links ∧ complete done links ∧
        ∀ (t : State) {later : Nat → Prop} (q : Supported t later), s.normal = t.normal →
          fromOrigins q links → complete later links →
          Trail (restriction q) (.variable arg.center) loc.term := by
  have literal : row ∈ numbered (seed s arg keep seen) (jobs seen) := freshRow
  have rhs : row.right ∈ jobs seen := by
    rw [← rhs_exact (seed s arg keep seen) (jobs seen)]
    exact List.mem_map.mpr ⟨row,literal,rfl⟩
  obtain ⟨u,witness,belongs⟩ := List.mem_flatMap.mp rhs
  obtain ⟨exact,compound⟩ := job_spelling belongs
  obtain ⟨links,known,complete,replay⟩ := exact_uses source
  exact ⟨u,witness,exact,compound,links,known,complete,fun t {_} q normal old done =>
    carries (replay t q normal old done) u witness⟩

end Yulang.GeneralDeclarativeInlineOrigins331
