import Yulang.GeneralRebasePortDecode280
import Yulang.GeneralRebasePortProjection280

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebasePortBatch280
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalSaturationState (Packet)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebasePortDecode280 (pair writes bare written_iff target_formula target_unique)
open GeneralRebasePortCopy280 (Write Copy PairWrites Unambiguous Apart Isolated interval_copy)
open GeneralRebasePortMeaning280 (SiteMatches matches_refl)
open GeneralRebasePortProjection280 (Extension Supported Project Conditions project_extension)

def batch (p : Packet roles) : List Write :=
  p.declaration.requirements.attach.flatMap fun c =>
    writes p c.val (p.checked.signature.2.2.2 c.val c.property)

private theorem list_key {A : Type} (items : List A) (key : A → Nat) (unique : (items.map key).Nodup)
    {a b : A} (first : a ∈ items) (last : b ∈ items) (same : key a = key b) : a = b := by
  induction items with
  | nil => cases first
  | cons head rest ih =>
    have sep := List.nodup_cons.mp unique
    rcases List.mem_cons.mp first with rfl|one
    · rcases List.mem_cons.mp last with rfl|two
      · rfl
      · exact False.elim (sep.1 (List.mem_map.mpr ⟨b,two,same.symm⟩))
    · rcases List.mem_cons.mp last with rfl|two
      · exact False.elim (sep.1 (List.mem_map.mpr ⟨a,one,same⟩))
      · exact ih sep.2 one two

theorem cross_target {p : Packet roles} {c d : Clause}
    (a : c ∈ p.declaration.requirements) (b : d ∈ p.declaration.requirements)
    {ok₁ : c.Signature roles} {ok₂ : d.Signature roles}
    {i : Fin (roles c.role).arity} {j : Fin (roles d.role).arity}
    (eq : (pair p c ok₁ i high).1 = (pair p d ok₂ j low).1) :
    c = d := by
  rw [target_formula,target_formula] at eq
  have keys := (GeneralNominalIdentities.source_identity p.context.state.seed _ _).mp eq
  have ids : c.id = d.id := congrArg (fun key : GeneralNominalIdentities.Origin => key.2.2.2.1) keys
  exact list_key _ _ p.checked.identified.1 a b ids

theorem batch_iff {p : Packet roles} {w : Write} :
    w ∈ batch p ↔ ∃ c, ∃ member : c ∈ p.declaration.requirements,
      w ∈ writes p c (p.checked.signature.2.2.2 c member) := by
  constructor
  · intro had
    obtain ⟨c,_,recorded⟩ := List.mem_flatMap.mp had
    exact ⟨c.val,c.property,recorded⟩
  · rintro ⟨c,member,localWrite⟩
    exact List.mem_flatMap.mpr ⟨⟨c,member⟩,List.mem_attach ..,localWrite⟩

theorem local_in {p : Packet roles} {c : Clause} {ok : c.Signature roles}
    (recorded : c ∈ p.declaration.requirements) : writes p c ok ⊆ batch p :=
  fun _ used => batch_iff.mpr ⟨c,recorded,used⟩

theorem batch_unique (p : Packet roles) : Unambiguous (batch p) := by
  intro a occurs b repeated eq
  obtain ⟨c,cm,localC⟩ := batch_iff.mp occurs
  obtain ⟨d,dm,localD⟩ := batch_iff.mp repeated
  obtain ⟨i,high,_,rfl⟩ := written_iff.mp localC
  obtain ⟨j,low,_,rfl⟩ := written_iff.mp localD
  have same := cross_target cm dm eq
  subst d
  obtain ⟨rfl,rfl⟩ := target_unique p c _ eq
  rfl

theorem lookup_batch {p : Packet roles} {c : Clause} {ok : c.Signature roles}
    (belongs : c ∈ p.declaration.requirements) (i : Fin (roles c.role).arity) (side : Bool) :
    GeneralRebasePortCopy280.lookup (batch p) (pair p c ok i side).1 =
      GeneralRebasePortCopy280.lookup (writes p c ok) (pair p c ok i side).1 := by
  by_cases active : bare p c ok i = true
  · have existsWrite := written_iff.mpr ⟨i,side,active,rfl⟩
    exact (GeneralRebasePortCopy280.lookup_exact (batch_unique p) (local_in belongs existsWrite)).trans
      (GeneralRebasePortCopy280.lookup_exact (GeneralRebasePortDecode280.unique p c ok) existsWrite).symm
  · have missing : GeneralRebasePortCopy280.lookup (batch p) (pair p c ok i side).1 = none := by
      apply GeneralRebasePortCopy280.lookup_absent
      intro other used eq
      obtain ⟨d,mentioned,defined⟩ := batch_iff.mp used
      obtain ⟨j,which,yes,rfl⟩ := written_iff.mp defined
      have same := cross_target mentioned belongs eq
      subst d
      obtain ⟨rfl,_⟩ := target_unique p c ok eq
      exact active yes
    rw [missing]
    symm
    apply GeneralRebasePortCopy280.lookup_absent
    intro other has eq
    have found := GeneralRebasePortCopy280.lookup_exact (batch_unique p) (local_in belongs has)
    rw [eq,missing] at found
    cases found

theorem endpoint_batch {p : Packet roles} {c : Clause} {ok : c.Signature roles}
    (belongs : c ∈ p.declaration.requirements) (i : Fin (roles c.role).arity) (side : Bool) :
    GeneralRebasePortDecode280.endpoint (batch p) (pair p c ok i side).1 =
      (pair p c ok i side).2 := by
  change (GeneralRebasePortCopy280.lookup (batch p) _).getD _ = _
  rw [lookup_batch belongs]
  exact GeneralRebasePortDecode280.endpoint_exact p c ok i side

theorem decode_batch {p : Packet roles} {c : Clause} {ok : c.Signature roles}
    (belongs : c ∈ p.declaration.requirements) :
    GeneralRebasePortDecode280.decode (batch p) (GeneralRebaseChildPorts280.fixed p c ok) =
      GeneralNominalVersionedFrame231.clauseChild p c ok := by
  apply GeneralRebaseOccurrenceCode279.occurrenceCode_injective
  have eq : (GeneralRebasePortDecode280.decode (batch p)
      (GeneralRebaseChildPorts280.fixed p c ok)).demand.arguments =
      (GeneralNominalVersionedFrame231.clauseChild p c ok).demand.arguments := by
    funext i
    exact Prod.ext (endpoint_batch belongs i false) (endpoint_batch belongs i true)
  exact congrArg (fun args : Fin (roles c.role).arity → GeneralSourceState.Interval =>
    GeneralRebaseOccurrenceCode279.OccurrenceCode.mk
      (GeneralNominalVersionedFrame231.clauseChild p c ok).identity
      ⟨c.role,List.ofFn args,(GeneralNominalVersionedFrame231.clauseChild p c ok).demand.outputs.map
        GeneralRebaseOccurrenceCode279.outputCode⟩) eq

theorem copied_all {p : Plan roles} (isolated : Isolated (batch p.packet)) (m : Assignment)
    (c : Clause) (recorded : c ∈ p.packet.declaration.requirements) (ok : c.Signature roles) :
    SiteMatches (Copy (batch p.packet) m) p c ok := by
  intro i
  by_cases site : bare p.packet c ok i = true
  · apply interval_copy (batch_unique _) isolated _ m
    intro w mem
    apply local_in recorded
    rcases (List.mem_cons.mp mem) with h|h
    · subst w
      exact written_iff.mpr ⟨i,false,site,rfl⟩
    · cases List.mem_singleton.mp h
      exact written_iff.mpr ⟨i,true,site,rfl⟩
  · have no := GeneralRebasePortDecode280.bare_false (Bool.eq_false_iff.mpr site)
    change GeneralRebasePortMeaning280.Matches _
      ((GeneralRebaseChildPorts280.fixed p.packet c ok).demand.arguments i)
      ((GeneralNominalVersionedFrame231.clauseChild p.packet c ok).demand.arguments i)
    rw [GeneralRebaseChildPorts280.nonvariable_unchanged _ _ _ _ no]
    exact matches_refl _ _

theorem all_alias_atoms {p : Plan roles} (isolated : Isolated (batch p.packet))
    (m : Assignment) (c : Clause) (recorded : c ∈ p.packet.declaration.requirements) (ok : c.Signature roles) :
    PresenceNormalForm.All CommonNominalFullCarrier.model (Copy (batch p.packet) m)
      (GeneralRebasePortMeaning280.clauseAtoms p c ok) :=
  (GeneralRebasePortMeaning280.clause_atoms ..).mpr (copied_all isolated m c recorded ok)

theorem batch_public (p : Packet roles) (supports : Supported assumption models)
    (fresh : Apart (batch p) assumption) (hide : Apart (batch p) names)
    (isolated : Isolated (batch p)) (m : Assignment) :
    Project names (Extension models (batch p)) m ↔ Project names models m :=
  project_extension supports fresh hide (batch_unique p) isolated m

end Yulang.GeneralRebasePortBatch280
