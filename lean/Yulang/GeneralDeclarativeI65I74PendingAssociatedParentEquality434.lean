import Yulang.GeneralDeclarativeI65I74PendingAssociatedSeparation434

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PendingAssociated434
open GeneralDeclarativeI65
open Checker408 (Problem Result)
open CommonNominalFullCarrier (nominal Equivalent)
open CommonRoleOutermostResolver (Dictionary Summarizes Tree)

/-- Conservativity of the current ordinary equation at the actual
parent's B6 address. In every fitted model the retained parent equation
has exactly its source meaning `A = list B`. It is not removed just
because that parent cannot be used as a completed head producer.
This is not evidence for selection of either event. -/
theorem pending_parent_keeps_original_where_equation_in_every_model434
    {s q} (o : OriginalPendingWhere434 s q) (m : I72.Model) (fit : Fits s m) :
    (o.event.outputs o.out).receipt.actualEquation m =
      some (o.episode.a,nominal o.episode.key [.inl (m.assignment o.episode.b).1]) ∧
    Equivalent (m.assignment o.episode.a).1
      (nominal o.episode.key [.inl (m.assignment o.episode.b).1]) := by
  have body := fixed_value_code_same_model403 (o.event.outputs o.out).rhs m _ o.rawRhs
  have retained : retainedOutput434 o.episode.key o.episode.a o.episode.b ∈
      s.core.current.ordinary.equations := by
    rw [o.episode.exactRows]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  refine ⟨?_,fit.1.1.2 _ retained⟩
  simp only [NamedMixedReceipt401.actualEquation,NamedMixedOutput401.receipt,body,
    Option.map_some,o.exactTarget]
  rfl

/-- A checked pause yields, at that same original event and State, both
the retained equation in every fitting model and a precise obstruction
to using the event through any actual selected parent trace. -/
theorem checked_pending_preserves_equation_without_completion434
    {p : Problem} {r : Result} {w : Wire}
    (yes : check p r (.pendingAssociated w) = true) :
    ∃ o : Replay434 p, replay434 p w = some o ∧
      (∀ m : I72.Model, Fits p.state m →
        (o.original.event.outputs o.original.out).receipt.actualEquation m =
          some (o.original.episode.a,
            nominal o.original.episode.key [.inl (m.assignment o.original.episode.b).1]) ∧
        Equivalent (m.assignment o.original.episode.a).1
          (nominal o.original.episode.key [.inl (m.assignment o.original.episode.b).1])) ∧
      ∀ t : Tree, ∀ key : Nat, ∀ ds : List Dictionary,
        SourceTrace R17.named426 p.state o.original.parent t (some o.original.event) →
        ¬ Summarizes t (.selected (.node key ds)) := by
  obtain ⟨o,source,_⟩ := checked_pending_reads_actual_original_episode434 yes
  exact ⟨o,source,pending_parent_keeps_original_where_equation_in_every_model434 o.original,
    fun _ _ _ trace => original_pending_parent_has_no_selected_trace434 o.original trace⟩

end Yulang.GeneralDeclarativeI65.I72.PendingAssociated434
