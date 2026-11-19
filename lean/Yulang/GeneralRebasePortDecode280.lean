import Yulang.GeneralRebasePortCopy280
import Yulang.GeneralRebaseRawGraph280

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebasePortDecode280
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalSaturationState (Packet)
open GeneralSourceState (Interval)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalVersionedFrame231 (clauseChild childSite)
open GeneralRebaseChildPorts280 (fixed fixedSite ports nonvariable_unchanged)
open GeneralRebasePortCopy280 (Write lookup PairWrites Unambiguous lookup_exact lookup_absent)

def coordinate (bounds : Interval) (high : Bool) : Nat := if high then bounds.2 else bounds.1

def bare (_p : Packet roles) (c : Clause) (ok : c.Signature roles) (i : Fin (roles c.role).arity) : Bool :=
  match normalize (c.arguments[i.val]'(by rw [ok.1]; exact i.isLt)) with
  | .var _ => true
  | _ => false

theorem bare_false {p : Packet roles} {c : Clause} {ok : c.Signature roles}
    {i : Fin (roles c.role).arity} (h : bare p c ok i = false) :
    ∀ name, normalize (c.arguments[i.val]'(by rw [ok.1]; exact i.isLt)) ≠ .var name := by
  intro name eq
  simp [bare,eq] at h

def pair (p : Packet roles) (c : Clause) (ok : c.Signature roles) (i : Fin (roles c.role).arity)
    (high : Bool) : Write :=
  (coordinate ((fixed p c ok).demand.arguments i) high,
    coordinate ((clauseChild p c ok).demand.arguments i) high)

def argWrites (p : Packet roles) (c : Clause) (ok : c.Signature roles)
    (i : Fin (roles c.role).arity) : List Write :=
  if bare p c ok i then [pair p c ok i false,pair p c ok i true] else []

def writes (p : Packet roles) (c : Clause) (ok : c.Signature roles) : List Write :=
  (List.finRange (roles c.role).arity).flatMap (argWrites p c ok)

theorem target_formula (p : Packet roles) (c : Clause) (ok : c.Signature roles)
    (i : Fin (roles c.role).arity) (high : Bool) :
    (pair p c ok i high).1 = GeneralNominalIdentities.source p.context.state.seed
      (GeneralNominalAllocation.origin p.site.occurrence.identity p.declaration.id
        (if high then 4 else 3) c.id i.val) := by
  cases high <;> rfl

theorem target_unique (p : Packet roles) (c : Clause) (ok : c.Signature roles)
    {i j : Fin (roles c.role).arity} {side other : Bool}
    (eq : (pair p c ok i side).1 = (pair p c ok j other).1) :
    i = j ∧ side = other := by
  rw [target_formula,target_formula] at eq
  have keys := (GeneralNominalIdentities.source_identity p.context.state.seed _ _).mp eq
  have index : i.val = j.val := congrArg (fun k : GeneralNominalIdentities.Origin => k.2.2.2.2) keys
  have direction : (if side then (4:Nat) else 3) = (if other then 4 else 3) :=
    congrArg (fun k : GeneralNominalIdentities.Origin => k.2.2.1) keys
  exact ⟨Fin.ext index,by cases side <;> cases other <;> simp_all⟩

theorem written_iff {p : Packet roles} {c : Clause} {ok : c.Signature roles} {w : Write} :
    w ∈ writes p c ok ↔ ∃ i high, bare p c ok i = true ∧ pair p c ok i high = w := by
  constructor
  · intro member
    obtain ⟨i,_,recorded⟩ := List.mem_flatMap.mp member
    by_cases writesHere : bare p c ok i = true
    · simp only [argWrites,writesHere,ite_true,List.mem_cons,List.not_mem_nil,or_false] at recorded
      exact recorded.elim (fun low => ⟨i,false,writesHere,low.symm⟩)
        (fun high => ⟨i,true,writesHere,high.symm⟩)
    · simp [argWrites,writesHere] at recorded
  · rintro ⟨i,high,selected,rfl⟩
    apply List.mem_flatMap.mpr
    refine ⟨i,List.mem_finRange _,?_⟩
    cases high <;> simp [argWrites,selected]

theorem unique (p : Packet roles) (c : Clause) (ok : c.Signature roles) :
    Unambiguous (writes p c ok) := by
  intro a left b right eq
  obtain ⟨i,iSide,_,rfl⟩ := written_iff.mp left
  obtain ⟨j,jSide,_,rfl⟩ := written_iff.mp right
  obtain ⟨rfl,rfl⟩ := target_unique p c ok eq
  rfl

def endpoint (table : List Write) (id : Nat) : Nat := (lookup table id).getD id

def interval (table : List Write) (bounds : Interval) : Interval :=
  (endpoint table bounds.1,endpoint table bounds.2)

def decode (table : List Write) (cached : Occurrence roles) : Occurrence roles :=
  let args := fun i : Fin (roles cached.demand.role).arity => interval table (cached.demand.arguments i)
  { cached with demand := { cached.demand with arguments := args } }

theorem endpoint_exact (p : Packet roles) (c : Clause) (ok : c.Signature roles)
    (i : Fin (roles c.role).arity) (high : Bool) :
    endpoint (writes p c ok) (pair p c ok i high).1 = (pair p c ok i high).2 := by
  by_cases yes : bare p c ok i = true
  · have listed := written_iff.mpr ⟨i,high,yes,rfl⟩
    exact congrArg (fun o => Option.getD o _) (lookup_exact (unique p c ok) listed)
  · have no : bare p c ok i = false := Bool.eq_false_iff.mpr yes
    have blank : lookup (writes p c ok) (pair p c ok i high).1 = none := by
      apply lookup_absent
      intro found mem same
      obtain ⟨j,side,active,rfl⟩ := written_iff.mp mem
      obtain ⟨rfl,_⟩ := target_unique p c ok same
      rw [no] at active
      cases active
    have eq : (pair p c ok i high).1 = (pair p c ok i high).2 :=
      congrArg (fun bounds => coordinate bounds high) (nonvariable_unchanged p c ok i (bare_false no))
    unfold endpoint
    rw [blank]
    exact eq

theorem interval_exact (p : Packet roles) (c : Clause) (ok : c.Signature roles)
    (i : Fin (roles c.role).arity) :
    interval (writes p c ok) ((fixed p c ok).demand.arguments i) = (clauseChild p c ok).demand.arguments i :=
  Prod.ext (endpoint_exact p c ok i false) (endpoint_exact p c ok i true)

theorem occurrence_exact (p : Packet roles) (c : Clause) (ok : c.Signature roles) :
    decode (writes p c ok) (fixed p c ok) = clauseChild p c ok := by
  have eq : (decode (writes p c ok) (fixed p c ok)).demand.arguments =
      (clauseChild p c ok).demand.arguments := funext (interval_exact p c ok)
  apply GeneralRebaseOccurrenceCode279.occurrenceCode_injective
  change GeneralRebaseOccurrenceCode279.OccurrenceCode.mk _ ⟨c.role,List.ofFn _,_⟩ =
    GeneralRebaseOccurrenceCode279.OccurrenceCode.mk _ ⟨c.role,List.ofFn _,_⟩
  exact congrArg (fun args : Fin (roles c.role).arity → Interval =>
    GeneralRebaseOccurrenceCode279.OccurrenceCode.mk (clauseChild p c ok).identity
      ⟨c.role,List.ofFn args,(clauseChild p c ok).demand.outputs.map GeneralRebaseOccurrenceCode279.outputCode⟩) eq

def decodeSite (table : List Write) (site : Site roles) : Site roles :=
  ⟨decode table site.occurrence,site.center⟩

theorem site_exact (p : Plan roles) (c : Clause) (ok : c.Signature roles) :
    decodeSite (writes p.packet c ok) (fixedSite p c ok) = childSite p c ok := by
  have eq := funext (interval_exact p.packet c ok)
  let original := childSite p c ok
  exact congrArg (fun args : Fin (roles c.role).arity → Interval =>
    ({ original with occurrence := { original.occurrence with
          demand := {original.occurrence.demand with arguments := args} } } : Site roles)) eq

end Yulang.GeneralRebasePortDecode280
