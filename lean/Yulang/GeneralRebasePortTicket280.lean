import Yulang.GeneralRebasePortDecode280

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
namespace Yulang.GeneralRebasePortTicket280
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedChildren232 (emitted rawSites edges emitted_occurrences)
open GeneralRebaseChildPorts280 (fixedSite)
open GeneralRebasePortCopy280 (Write)
open GeneralRebasePortDecode280 (writes decodeSite site_exact)

structure Ticket (roles : Roles.RoleDecls) where
  canonical : Site roles
  lookupTable : List Write

def Ticket.read (t : Ticket roles) : Site roles :=
  decodeSite t.lookupTable t.canonical

def compile (p : Plan roles) (c : Clause) (ok : c.Signature roles) : Ticket roles :=
  ⟨fixedSite p c ok,writes p.packet c ok⟩

theorem exact_site (p : Plan roles) (c : Clause) (ok : c.Signature roles) :
    (compile p c ok).read = GeneralNominalVersionedFrame231.childSite p c ok :=
  site_exact p c ok

def issue (p : Plan roles) : List (Ticket roles) :=
  (GeneralCanonicalChildOrder.canonicalRequirements p.packet.declaration.requirements).attach.map fun c =>
    compile p c.val
      (p.packet.checked.signature.2.2.2 c.val ((GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr c.property))

def readChildren (p : Plan roles) : List (Occurrence roles) :=
  (issue p).map fun t => t.read.occurrence

def readRaw (p : Plan roles) : List (GeneralNominalDemandMerging.Site roles) :=
  (issue p).map fun t => t.read.observed

def readEdges (p : Plan roles) : List (Occurrence roles × Occurrence roles) :=
  (readChildren p).map fun t => (p.packet.site.occurrence,t)

theorem read_sites (p : Plan roles) : (issue p).map Ticket.read = emitted p := by
  unfold issue emitted
  rw [List.map_map]
  apply List.map_congr_left
  intro c _
  exact exact_site ..

theorem read_raw (p : Plan roles) : readRaw p = rawSites p := by
  change (issue p).map (Site.observed ∘ Ticket.read) = (emitted p).map Site.observed
  rw [← List.map_map,read_sites]

theorem read_children (p : Plan roles) : readChildren p = GeneralNominalVersionedFrame231.children p.packet := by
  change (issue p).map (Site.occurrence ∘ Ticket.read) = _
  rw [← List.map_map,read_sites,emitted_occurrences]

theorem read_edges (p : Plan roles) : readEdges p = edges p := by
  unfold readEdges edges
  rw [read_children]

theorem ordered_size (p : Plan roles) : (issue p).length = p.packet.declaration.requirements.length := by
  rw [← GeneralNominalVersionedChildren232.emitted_length p,← read_sites,List.length_map]

end Yulang.GeneralRebasePortTicket280
