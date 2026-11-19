import Yulang.GeneralRebaseCertifiedPathSettle266
import Yulang.GeneralRebaseCertifiedFixture266

namespace Yulang.GeneralRebaseCertifiedPathCount266
open GeneralRebaseStep258
open GeneralRebaseBudget258 (Runs)
open GeneralRebaseCertifiedObserver266 (Edge observe chosen chosen_exact step_exact)
open GeneralRebaseCertifiedPath266
open GeneralRebaseLiveProjection264 (SourceState project)
open GeneralSourceState (Output)
variable {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}

def strict_count (owners : List Nat) (pool : List Output) (path : Path registry root first last) : Nat :=
 ((edges path).filter fun edge => chosen owners pool (project owners pool edge.before) edge).length

theorem exact_run (owners : List Nat) (pool : List Output)
 (table : List (Edge registry root)) (path : Path registry root first last) (included : edges path ⊆ table) :
 Runs (observe owners pool table) (strict_count owners pool path)
   (project owners pool first) (project owners pool last) := by
 induction path with
 | nil => exact .nil _
 | cons edge tail ih =>
   have rest := ih (fun _ member => included (List.mem_cons_of_mem _ member))
   by_cases active : chosen owners pool (project owners pool edge.before) edge = true
   · have step := (step_exact owners pool table _ _).mpr
       ⟨edge,included List.mem_cons_self,rfl,rfl,((chosen_exact ..).mp active).2⟩
     simpa only [strict_count,edges,List.filter_cons,active,ite_true,List.length_cons] using Runs.next step rest
   · have omitted : chosen owners pool (project owners pool edge.before) edge = false :=
       Bool.eq_false_iff.mpr active
     have same : project owners pool edge.after = project owners pool edge.before := by
       apply Classical.byContradiction
       intro differ
       exact active ((chosen_exact ..).mpr ⟨rfl,differ⟩)
     simp only [strict_count,edges,List.filter_cons,omitted,Bool.false_eq_true,ite_false]
     exact same ▸ rest

theorem strict_count_bound (owners : List Nat) (pool : List Output)
 (path : Path registry root first last) :
 strict_count owners pool path ≤ (edges path).length := List.length_filter_le _ _

theorem exact_terminal_budget (owners : List Nat) (pool : List Output)
 (path : Path registry root first last) :
 strict_count owners pool path + rank owners pool last ≤ rank owners pool first :=
 GeneralRebaseBudget258.budget _ (exact_run owners pool (edges path) path (fun _ h => h))

noncomputable def compoundPath :=
 Path.cons GeneralRebaseCertifiedFixture266.realEdge (Path.nil GeneralDictionaryCompoundFrame238.installed)

theorem compound_count :
 strict_count GeneralRebaseSourceStrictFixture265.owners GeneralRebaseSourceStrictFixture265.pool compoundPath = 1 := by
 have active := (chosen_exact GeneralRebaseSourceStrictFixture265.owners GeneralRebaseSourceStrictFixture265.pool _
    GeneralRebaseCertifiedFixture266.realEdge).mpr ⟨rfl,GeneralRebaseSourceStrictFixture265.strict⟩
 simp only [strict_count,compoundPath,edges,List.filter_cons,active,ite_true,List.filter_nil,List.length_cons,List.length_nil]

theorem compound_settlement :
 GeneralRebaseSettle259.settle
   (observe GeneralRebaseSourceStrictFixture265.owners GeneralRebaseSourceStrictFixture265.pool (edges compoundPath))
   GeneralRebaseSourceStrictFixture265.first = .ok GeneralRebaseSourceStrictFixture265.last :=
 GeneralRebaseCertifiedPathSettle266.settles _ _ compoundPath

end Yulang.GeneralRebaseCertifiedPathCount266
