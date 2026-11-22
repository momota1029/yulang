import Yulang.GeneralDeclarativeWhereBoth346

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWhereRelease346
open GeneralNominalCenters (Plan Site)
open GeneralWhereVersionInstall317 (Journal)
open GeneralWhereOriginDelta318 (Cell)
open GeneralVersionedEndpointAddress315 (Side)
open GeneralDeclarativeWhereEndpoint346 (At)
open GeneralDeclarativeWhereAttributed346 (literal)
open GeneralDeclarativeOrigins321 (Origin Supported Backed Available backed_iff restriction)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeSubstitution320 (EquationRead)
open GeneralDeclarativeRawCapture344 (rawCap)

/-- Optional availability evidence is indexed by the *actual* released
writer/version and child position, in addition to the completed-owner
predicate. This is an adapter for a supplied witness, not an added
selection rule or a proof that any runtime returns such witnesses. -/
abbrev Released (rs : Roles.RoleDecls) :=
  Plan rs → Nat → Nat → Nat → Side → Prop

def attach {s : State} (orig : Supported s done) {before after : Journal rs} {p : Plan rs}
    {c : Cell p} {ord : Nat} {site : Site rs} (_confirmed : At before after p c ord site)
    (release : Released rs) : Supported (appendFacts s [literal c]) done where
  derivesFrom row origin := orig.derivesFrom row origin ∨
    row = literal c ∧ origin = .output p.packet.site.occurrence.identity ∧
      release p before.versionedWhere.length (before.mixed.core.sites.length+ord) c.index c.side
  ordinary := by
    intro row provenance h
    rcases h with old|⟨rfl,_,_⟩
    · exact List.mem_append_left _ (orig.ordinary old)
    · exact List.mem_append_right _ List.mem_cons_self

theorem backed {s : State} (orig : Supported s done) {before after : Journal rs}
    {p : Plan rs} {c : Cell p} {ord : Nat} {site : Site rs} (confirmed : At before after p c ord site)
    (release : Released rs) :
    row ∈ (restriction (attach orig confirmed release)).equations ↔
      Backed orig row ∨ row = literal c ∧ done p.packet.site.occurrence.identity ∧
        release p before.versionedWhere.length (before.mixed.core.sites.length+ord) c.index c.side := by
  rw [backed_iff]
  constructor
  · rintro ⟨origin,old|⟨rfl,rfl,released⟩,known⟩
    · exact .inl ⟨origin,old,known⟩
    · cases known with
      | completed finished => exact .inr ⟨rfl,finished,released⟩
  · rintro (⟨origin,old,known⟩|⟨rfl,finished,released⟩)
    · exact ⟨origin,.inl old,known⟩
    · exact ⟨_,.inr ⟨rfl,rfl,released⟩,.completed finished⟩

theorem archived_excluded {s : State} (orig : Supported s done) {before after : Journal rs}
    {p : Plan rs} {c : Cell p} {ord : Nat} {site : Site rs} (confirmed : At before after p c ord site)
    {release : Released rs} (earlier : ¬ Backed orig (literal c))
    (notReleased : ¬ release p before.versionedWhere.length (before.mixed.core.sites.length+ord) c.index c.side) :
    literal c ∉ (restriction (attach orig confirmed release)).equations := by
  intro h
  rcases (backed orig confirmed release).mp h with old|⟨_,_,found⟩
  · exact earlier old
  · exact notReleased found

theorem with_release {s : State} (orig : Supported s done) {before after : Journal rs}
    {p : Plan rs} {c : Cell p} {ord : Nat} {site : Site rs} (confirmed : At before after p c ord site)
    {release : Released rs} (finished : done p.packet.site.occurrence.identity)
    (now : release p before.versionedWhere.length (before.mixed.core.sites.length+ord) c.index c.side) :
    EquationRead (restriction (attach orig confirmed release)) (rawCap p) c.side.mode c.row.target c.expression := by
  apply EquationRead.whole
  exact (backed orig confirmed release).mpr (.inr ⟨rfl,finished,now⟩)

end Yulang.GeneralDeclarativeWhereRelease346
