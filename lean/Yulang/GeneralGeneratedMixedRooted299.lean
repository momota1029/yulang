import Yulang.GeneralGeneratedMixedCurrentNodes299
import Yulang.GeneralGeneratedDictionaryAcc299

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralGeneratedMixedRooted299
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedMixedCurrentCandidate235 (source_installable)
open GeneralGeneratedDictionaryRun299
open GeneralGeneratedDictionaryScope299
open GeneralGeneratedDictionaryNodes299 (Nodes)
open GeneralGeneratedDictionaryAcc299 (Edge)
open GeneralGeneratedMixedCurrentNodes299 (Providers)
open B4TargetV8

variable {roles : Roles.RoleDecls} {registry : Registry} {s : State roles} {root : Occurrence roles}
abbrev B (roles : Roles.RoleDecls) := boundary roles

def Rooted (read : Read) (initial : Nat) : Prop :=
  ∀ i e, read i = some e → i = initial ∨ Relation.TransGen (Edge read) i initial

theorem child_generated (read : Read) (decode : Nat → Occurrence roles)
    (route : Reachable (B roles) registry root s)
    (faith : Faithful (b:=B roles) (r:=registry) (s:=s) read decode)
    (available : Providers registry s read decode)
    (inhabited : ∃ m, Models s m)
    (stable : ∀ x, (x = root ∨ (B roles).Generated registry s root x) → (B roles).Stable registry s x)
    (c x : Nat) (edge : Edge read c x)
    (reached : decode x = root ∨ (B roles).Generated registry s root (decode x)) :
    (B roles).Generated registry s root (decode c) := by
  obtain ⟨row,hit,mem⟩ := edge
  obtain ⟨effect,current⟩ := available x row hit inhabited
  have chosen := faith x row hit
  exact GeneralNominalVersionedMixedStableEvidence235.selected_generated_children
    (stable (decode x) reached) (source_installable current route chosen) current.occurrence_eq
    (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp chosen) reached
    (List.mem_map.mpr ⟨c,mem,rfl⟩)

theorem along (read : Read) (decode : Nat → Occurrence roles)
    (route : Reachable (B roles) registry root s)
    (faith : Faithful (b:=B roles) (r:=registry) (s:=s) read decode)
    (available : Providers registry s read decode)
    (inhabited : ∃ m, Models s m)
    (stable : ∀ x, (x = root ∨ (B roles).Generated registry s root x) → (B roles).Stable registry s x)
    {c x : Nat} (down : Relation.TransGen (Edge read) c x) :
    (decode x = root ∨ (B roles).Generated registry s root (decode x)) →
    (B roles).Generated registry s root (decode c) := by
  induction down with
  | single e => exact child_generated read decode route faith available inhabited stable _ _ e
  | tail _ e ih =>
    intro reached
    exact ih (.inr (child_generated read decode route faith available inhabited stable _ _ e reached))

theorem scope_after_halt (read : Read) (decode : Nat → Occurrence roles) (i : Nat)
    (origin : decode i = root) (rooted : Rooted read i)
    (route : Reachable (B roles) registry root s)
    (faith : Faithful (b:=B roles) (r:=registry) (s:=s) read decode)
    (available : Providers registry s read decode) (inhabited : ∃ m, Models s m)
    (halted : ∀ next, ¬ (B roles).Step registry root s next) :
    InScope (B roles) registry s root read decode := by
  have closure := GeneralNominalVersionedMixedSourceBoundary234.closure halted
  have stable (x) (h : x = root ∨ (B roles).Generated registry s root x) : (B roles).Stable registry s x := by
    rcases h with rfl | generated
    · exact closure.1
    · exact closure.2 x generated
  intro x row hit
  have reached : decode x = root ∨ (B roles).Generated registry s root (decode x) := by
    rcases rooted x row hit with rfl|desc
    · exact .inl origin
    · exact .inr (along read decode route faith available inhabited stable desc (.inl origin))
  exact ⟨reached,stable _ reached⟩

theorem after_halt (read : Read) (decode : Nat → Occurrence roles) (i : Nat)
    (origin : decode i = root) (rooted : Rooted read i)
    (route : Reachable (B roles) registry root s)
    (faith : Faithful (b:=B roles) (r:=registry) (s:=s) read decode)
    (available : Providers registry s read decode)
    (halted : ∀ next, ¬ (B roles).Step registry root s next)
    (fuel : Nat) (payload : CommonRoleOutermostResolver.Dictionary)
    (runOk : run read fuel i = some payload) :
    Classify (B roles) registry s root (.selected payload) ∧
    ∀ m, Models s m → (B roles).Evidence registry s m root payload := by
  constructor
  · exact origin ▸ classifies (b:=B roles) (r:=registry) (s:=s) read decode faith _ _ _ runOk
  · intro m valid
    have scope := scope_after_halt read decode i origin rooted route faith available ⟨m,valid⟩ halted
    have nodes := GeneralGeneratedMixedCurrentNodes299.scoped_nodes read decode route faith scope available
    exact origin ▸ GeneralGeneratedDictionaryNodes299.same_model (b:=B roles) (r:=registry) (s:=s) read decode nodes m valid _ _ _ runOk

end Yulang.GeneralGeneratedMixedRooted299
