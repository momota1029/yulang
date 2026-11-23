import Yulang.GeneralDeclarativeI65Lowering365

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂)
open GeneralDeclarativeAssembly320 (Prepared Head)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessClassifyVariance357 (JoinedLocal roleView roleView_span)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWhere319 (Capture)

theorem ordinary_head_adapter {s : State} {cap : Nat → Capture} {args : List Capture} {ps : List Pattern}
    (h : All₂ (Head s.current.ordinary (authoredRegistry s.current).constructors
      (interpretation s.current.environment.source.snapshot) cap) args ps) :
    All₂ (ReadsHead s cap) args ps := by
  induction h with
  | nil => exact .nil
  | cons head _ rest => exact .cons (.ordinary head) rest

/-- Existing ordinary primitive/invariant readings are cases of the
common source-node meaning; they do not reclassify a declared native
constructor through the old primitive/invariant carrier. -/
def ordinary_node {s : State} {q : Request} {row : Declaration} {kids : List Request}
    {cap : Nat → Capture} (actual : BodyFacts s q row kids)
    (seen : Prepared s.current.ordinary (authoredRegistry s.current)
      (interpretation s.current.environment.source.snapshot) row q.demand cap actual.demands)
    (covered : DeclarationCovered s.current.environment row)
    (written : row.Signature (authoredRegistry s.current).roles)
    (readback : ∀ n ∈ row.inputNames,
      ((actual.spans.find? fun entry => entry.1 == n).map Prod.snd) = some (cap n)) : SourceNode s q row kids :=
  ⟨(visible_exact ..).mpr ⟨seen.visible,seen.role⟩,covered,written,actual,
    .ordered cap seen.captures readback (ordinary_head_adapter seen.head)⟩

def joined_node {s : State} {q : Request} {row : Declaration} {ds}
    (source : JoinedLocal s.current q.demand row ds)
    (covered : DeclarationCovered s.current.environment row)
    (written : row.Signature (authoredRegistry s.current).roles) :
    SourceNode s q row (children q ds) := by
  have only : row ∈ (roleView s.current q.demand.role).declarations := by
    rw [source.single]
    exact List.mem_cons_self
  exact ⟨(visible_exact ..).mpr ((roleView_span ..).mp only),covered,written,
    ⟨_,ds,source.body,rfl⟩,.joined source.head rfl⟩

theorem ordinary_and_joined_share_model {s : State} {q₁ q₂ : Request} {r₁ r₂ : Declaration}
    {kids₁ kids₂ : List Request} (a : SourceNode s q₁ r₁ kids₁) (b : SourceNode s q₂ r₂ kids₂)
    (m : Model) (fit : Fits s m) :
    SourceNodeMeaning a m ∧ SourceNodeMeaning b m :=
  ⟨source_node_sound a m fit,source_node_sound b m fit⟩

end Yulang.GeneralDeclarativeI65
