import Yulang.GeneralDeclarativeObservedSupport347
import Yulang.GeneralDeclarativeWhereCurrent346
import Yulang.GeneralWherePhysicalEvidence319

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeJournalRelease347
open GeneralNominalCenters (Plan Site)
open GeneralWhereOriginDelta318 (Cell)
open GeneralWhereVersionInstall317 (Journal Models)
open GeneralWhereOriginTrace318 (rawOf)
open GeneralDeclarativeWhereEndpoint346 (At)
open GeneralDeclarativeWhereRelease346 (Released)
open GeneralDeclarativeWhereAttributed346 (literal)
open GeneralDeclarativeWhereBoth346 (polar)
open GeneralDeclarativeObservedSyntax347 (structural)
open GeneralDeclarativeObservedSupport347 (Record)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralNominalVersionedEffects231 (ClassEffects)
open GeneralNominalCommonBridge (Assignment)
open GeneralVersionedEndpointAddress315 (Side)

/-- A checked release at one explicitly registered current position,
derived from the current raw lookup and its exact compiler row. It
does not claim that an arbitrary installable row has been observed.
The parent must separately export completed evidence. -/
structure Current {rs : Roles.RoleDecls} (last : Journal rs) (p : Plan rs) (c : Cell p)
    (stamp position ord : Nat) (site : Site rs) : Prop where
  recorded : last.versionedWhere[stamp]? = some p
  physical : last.mixed.core.sites[position]? = some site
  ordered : (GeneralWhereVersionInstall317.emitted p)[ord]? = some site
  input : ∃ i : Fin (rs site.occurrence.demand.role).arity, i.val = c.index ∧
    GeneralWhereOriginSchema318.pick c.side (site.occurrence.demand.arguments i) = c.row.target
  observed : structural (rawOf last) c.row.target = some (literal c)

def release (last : Journal rs) : Released rs :=
  fun p stamp physical index side =>
    ∃ (c : Cell p) (ord : Nat) (site : Site rs), c.index = index ∧ c.side = side ∧ Current last p c stamp physical ord site

theorem at_committed {before last : Journal rs} {p : Plan rs} {c : Cell p} {ord : Nat} {site : Site rs}
    (event : At before last p c ord site)
    (seen : structural (rawOf last) c.row.target = some (literal c)) :
    Current last p c before.versionedWhere.length (before.mixed.core.sites.length+ord) ord site :=
  ⟨event.stamp,event.physical,event.emittedHere,event.inputHere,seen⟩

theorem actual_release {before last : Journal rs} {p : Plan rs} {c : Cell p} {ord : Nat} {site : Site rs}
    (event : At before last p c ord site)
    (seen : structural (rawOf last) c.row.target = some (literal c)) :
    release last p before.versionedWhere.length (before.mixed.core.sites.length+ord) c.index c.side :=
  ⟨c,ord,site,rfl,rfl,at_committed event seen⟩

theorem read_after_done {before last : Journal rs} {p : Plan rs} {c : Cell p} {ord : Nat} {site : Site rs}
    (p₀ : GeneralDeclarativeOrigins321.Supported s done) (event : At before last p c ord site)
    (seen : structural (rawOf last) c.row.target = some (literal c))
    (finished : done p.packet.site.occurrence.identity) :
    GeneralDeclarativeSubstitution320.EquationRead
      (GeneralDeclarativeOrigins321.restriction (GeneralDeclarativeWhereRelease346.attach p₀ event (release last)))
      (GeneralDeclarativeRawCapture344.rawCap p) c.side.mode c.row.target c.expression :=
  GeneralDeclarativeWhereRelease346.with_release p₀ event finished (actual_release event seen)

end Yulang.GeneralDeclarativeJournalRelease347
