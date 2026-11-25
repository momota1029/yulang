import Yulang.GeneralDeclarativeI65I74X6AmbiguousConservative417
import Yulang.GeneralDictionaryInspectionHeads215

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RigidRival418
open GeneralDeclarativeI65
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr translate translateMany application)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeInspect321 (Visit PatternK2)
open GeneralDeclarativeK2Graph321 (View)
open GeneralDeclarativeGraphRows321 (structural observed literal_head)
open CommonNominalFullCarrier (Subtype Equivalent)
open GeneralDictionaryInspectionHeads215 (tag_subtype tagged_scalar tagged_equivalent)
open PlainMerged416 (PlainRows)
open X6Ambiguous417 (Candidate IntegerOrigin PlainHit Visits exact_capture_port417)

def rivalHead418 (tag str : Nat) : Pattern := .variant tag (.app str [])
def rivalCode418 (tag : Nat) : Expr := .variant tag (.primitive (.scalar .str) [])

structure Rival {s q} (rows : PlainRows s q) where
  candidate : Candidate s q
  strName : Nat
  literal : candidate.decl.head = [rivalHead418 rows.tag strName]
  kind : application (authoredRegistry s.core.current).constructors
    (interpretation s.core.current.environment.source.snapshot) strName [] =
      some (.primitive (.scalar .str) [])

structure RigidMismatch {s q} (rows : PlainRows s q) where
  rival : Rival rows
  source : IntegerOrigin rows
  originalOnly : (s.core.origins.filter (fun o => o.slot == rows.payload)).length = 1

theorem normalized_rival_is_literal_str418 {s q} {r : PlainRows s q} (a : Rival r) :
    a.candidate.decl.head.map (fun pattern => translate (authoredRegistry s.core.current).constructors
      (interpretation s.core.current.environment.source.snapshot) (normalize pattern)) =
      [some (rivalCode418 r.tag)] := by
  rw [a.literal]
  have fixed : normalize (rivalHead418 r.tag a.strName) = rivalHead418 r.tag a.strName := rfl
  simp only [List.map_cons,List.map_nil,fixed]
  simp [rivalHead418,rivalCode418,translate,translateMany,a.kind]

theorem original_int_point_cannot_fit_str418 {s q} {r : PlainRows s q} (a : RigidMismatch r)
    (m : I72.Model) (fit : Fits s m) :
    m.nativeSyntax r.payload = some X6Ambiguous417.integerOriginSyntax ∧
    ¬ Subtype (m.assignment r.payload).1 (.base .str) := by
  refine ⟨X6Ambiguous417.original_integer_typing_in_every_fit417 a.source m fit,?_⟩
  intro subtype
  have t := tagged_equivalent (PlainMerged416.actual_integer_payload_is_int_in_every_fit416 r m fit)
    (tagged_scalar .int)
  have different := tag_subtype t (tagged_scalar .str) subtype
  cases different

theorem rival_visits_exact_root_and_original_payload418 {s q} {r : PlainRows s q}
    (v : Visits r) :
    Visit (structural s.core.current.ordinary) r.root (rivalCode418 r.tag) r.root ∧
    Visit (structural s.core.current.ordinary) r.root (rivalCode418 r.tag) r.payload ∧
    ∀ site, Visit (structural s.core.current.ordinary) r.root (rivalCode418 r.tag) site →
      site = r.root ∨ site = r.payload := by
  refine ⟨.here .variant,.variant (literal_head r.rootRow rfl) (.here .primitive),?_⟩
  intro site seen
  change Visit (structural _) r.root (.variant r.tag (.primitive (.scalar .str) [])) site at seen
  cases seen with
  | here => exact .inl rfl
  | variant look inner =>
    rename_i child
    have same : site = child := by
      cases inner with
      | here => rfl
      | primitive _ impossible _ _ => simp at impossible
    exact .inr (same.trans (v.exactPort _ look))

theorem rigid_mismatch_does_not_hide_K2418 {s q} {r : PlainRows s q} (v : Visits r) :
    ¬ PatternK2 s.core.current.ordinary r.root (rivalCode418 r.tag) := by
  rintro ⟨site,path,cycle⟩
  rcases (rival_visits_exact_root_and_original_payload418 v).2.2 site path with same|same
  · exact v.rootSafe (same ▸ cycle)
  · exact v.payloadSafe (same ▸ cycle)

end Yulang.GeneralDeclarativeI65.I72.RigidRival418
