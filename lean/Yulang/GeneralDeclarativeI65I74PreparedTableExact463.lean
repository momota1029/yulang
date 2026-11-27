import Yulang.GeneralDeclarativeI65I74PreparedLocatedReport463

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463
open Yulang.GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (Current)
open Checker408 (Problem)
open EligibleFieldStart461 WrittenPattern460

/-- This theorem is exact about the supplied finite batches, not about
whether arbitrary declaration readiness has a finite GD certificate. -/
theorem prepare_batch_succeeds_iff_every_supplied_certificate_checks
    {cur : Current} (gd : CertificateProtocol cur) (input : List (Declaration × gd.Data)) :
    (∃ t, prepareTable gd input = some t) ↔ ∀ dw ∈ input, gd.verify dw.1 dw.2 = true := by
  induction input with
  | nil => simp [prepareTable]
  | cons first rest ih =>
    obtain ⟨d,w⟩ := first
    constructor
    · rintro ⟨t,done⟩
      by_cases h : gd.verify d w = true
      · cases hr : prepareTable gd rest with
        | none => simp [prepareTable,prepareOne,h,hr,Option.bind] at done
        | some all =>
          intro pair mem
          rcases List.mem_cons.mp mem with rfl | later
          · exact h
          · exact ih.mp ⟨all,hr⟩ pair later
      · simp [prepareTable,prepareOne,h,Option.bind] at done
    · intro all
      have first : gd.verify d w = true := all (d,w) List.mem_cons_self
      obtain ⟨tail,done⟩ := ih.mpr (fun pair mem => all pair (List.mem_cons_of_mem _ mem))
      refine ⟨⟨d :: tail.rows, ?_⟩, ?_⟩
      · intro dec ok
        rcases List.mem_cons.mp ok with eq | later
        · exact eq.symm ▸ gd.sound d w first
        · exact tail.prepared dec later
      · simp [prepareTable,prepareOne,first,done,Option.bind]

theorem read_address_depends_on_prepared_membership_only
    {p : Problem} (a b : CheckedTable p.state.core.current)
    (same : ∀ d, d ∈ a.rows ↔ d ∈ b.rows) (addr : AnchorAddress) :
    readPrepared a addr = readPrepared b addr := by
  cases origin : readOriginalAnchor p addr with
  | none => simp [readPrepared,origin,Option.bind]
  | some source =>
    by_cases req : checkRequestOnly source = true
    · have eq : tableContains a source.declaration = tableContains b source.declaration := by
        simp [tableContains,same source.declaration]
      by_cases included : tableContains a source.declaration = true
      · have other : tableContains b source.declaration = true := eq ▸ included
        simp [readPrepared,origin,Option.bind,req,included,other]
        rfl
      · have other : ¬ tableContains b source.declaration = true := eq ▸ included
        simp [readPrepared,origin,Option.bind,req,included,other]
    · simp [readPrepared,origin,Option.bind,req]

/-- Datum values from different proof producers cannot leak into a request
when the loaded resolved declarations are the same. -/
theorem prepared_request_is_independent_of_origin_of_certificate_data
    {p : Problem} {a b : CheckedTable p.state.core.current}
    (ga gb : CertificateProtocol p.state.core.current)
    (as : List (Declaration × ga.Data)) (bs : List (Declaration × gb.Data))
    (ap : prepareTable ga as = some a) (bp : prepareTable gb bs = some b)
    (same : (as.map Prod.fst).Perm (bs.map Prod.fst)) (addr : AnchorAddress) :
    readPrepared a addr = readPrepared b addr := by
  apply read_address_depends_on_prepared_membership_only
  intro d
  rw [prepared_table_retains_only_exact_declaration_order ga as a ap,
    prepared_table_retains_only_exact_declaration_order gb bs b bp]
  exact same.mem_iff


/-- The exact field result, stamp, physical ordinals, and all original
occurrences depend on prepared membership and the same original wire only. -/
theorem located_field_result_ignores_certificate_producer_and_loaded_order
    (p : RetainedFull445.FullProblem) (a b : CheckedTable p.state.base.core.current)
    (same : ∀ d, d ∈ a.rows ↔ d ∈ b.rows) (w : PreparedWire ⟨p,a⟩) :
    readLocated w = readLocated (input := ⟨p,b⟩) ⟨w.start,w.along⟩ := by
  have read := read_address_depends_on_prepared_membership_only (p := p.old) a b same w.start
  simp only [readLocated,read]

end Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463
