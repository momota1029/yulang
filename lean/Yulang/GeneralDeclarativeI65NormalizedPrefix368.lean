import Yulang.GeneralDeclarativeI65NormalSupport368
import Yulang.GeneralDeclarativeI65ReleaseErasure368

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeInspect321 (Visit PatternK2)
open GeneralDeclarativeK2Alias321 (AliasCycle cycle_in_alias_graph)
open GeneralDeclarativeGraphRows321 (observed pending_nominal_self_cycle)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeWitnessOrigins350 (Table Attached support)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarations (Declaration)

/-- Literal candidate/argument/pattern slot in the current authored
registry, with normalized bounds rooted in the same independent
release table. No successful full candidate read is required. -/
structure NormalizedSourcePrefix (s : State) (q : Request) (row : Declaration) where
  visibleRow : row ∈ visible s q
  index : Nat
  input : Capture
  atInput : q.demand.arguments[index]? = some input
  pattern : Pattern
  atPattern : row.head[index]? = some pattern
  code : Expr
  written : translate (authoredRegistry s.current).constructors
    (interpretation s.current.environment.source.snapshot) (normalize pattern) = some code
  table : Table
  ordinary : Attached s.current.ordinary table
  normalized : TaggedNormal
  normActual : NormalAttached s.current.ordinary.normal normalized
  seenRoot : ∃ ctor, verifiedSourceView ordinary normalized input.lower ctor
  site : Nat
  visited : Visit (verifiedSourceView ordinary normalized) input.lower code site

theorem normalized_actual_prefix_k2 {s : State} {q : Request} {r : Declaration}
    (read : NormalizedSourcePrefix s q r)
    (cycles : AliasCycle s.current.ordinary (observed s.current.ordinary) read.site) :
    PatternK2 s.current.ordinary read.input.lower read.code :=
  ⟨read.site,lift_prefix_visit (fun _ _ x => verified_source_view_to_ordinary read.normActual x) read.visited,cycles⟩

theorem normalized_pending_row_changes_k2_without_support {s : State} {q : Request} {r : Declaration}
    (read : NormalizedSourcePrefix s q r) (tag owner : Nat)
    (letRow : ((⟨read.site,.nominal tag [.variable read.site]⟩ : Equation),owner) ∈ read.table.produced)
    (notAuthored : (⟨read.site,.nominal tag [.variable read.site]⟩ : Equation) ∉ read.table.authored)
    (notReleased : ∀ n ∈ read.table.released,
      ((⟨read.site,.nominal tag [.variable read.site]⟩ : Equation),n) ∉ read.table.produced) :
    (⟨read.site,.nominal tag [.variable read.site]⟩ : Equation) ∉
      (restriction (support read.ordinary)).equations ∧
        PatternK2 s.current.ordinary read.input.lower read.code := by
  obtain ⟨_,notRead,_⟩ := exact_ready_differs_on_unchanged_current read.ordinary letRow notAuthored notReleased
  exact ⟨notRead,normalized_actual_prefix_k2 read
    (cycle_in_alias_graph (pending_nominal_self_cycle (support read.ordinary) owner letRow))⟩

end Yulang.GeneralDeclarativeI65
