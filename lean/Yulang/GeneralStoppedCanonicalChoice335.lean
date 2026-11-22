import Yulang.GeneralStoppedCanonical335

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralStoppedCanonicalChoice335
open GeneralDeclarations (Registry Declaration)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralNominalInspection (Interpretation)
open GeneralCanonicalChildOrder (canonicalDeclaration)
open GeneralStoppedCanonical335 (sourceCanonical)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativePriority321 (Blocked Survives Recurs)
open GeneralDeclarativeStableAttempt329 (Elected)

def SameWait (waiting : Demand → Declaration → Prop) : Prop :=
  ∀ d impl, waiting d (canonicalDeclaration impl) ↔ waiting d impl

theorem same_probe {s : State} {p : Supported s done} (r : Registry) (i : Interpretation)
    (wait : Demand → Declaration → Prop) (d : Demand) (impl : Declaration) :
    (candidates p (sourceCanonical r) i wait).viable d (canonicalDeclaration impl) ↔
      (candidates p r i wait).viable d impl := Iff.rfl

theorem survives_forward {s : State} {p : Supported s done}
    (got : Survives r (candidates p r i waiting) d impl) :
    Survives (sourceCanonical r) (candidates p (sourceCanonical r) i waiting) d (canonicalDeclaration impl) :=
  ⟨⟨List.mem_map.mpr ⟨impl,got.1.1,rfl⟩,got.1.2⟩,got.2⟩

theorem survives_prior {s : State} {p : Supported s done} {impl : Declaration}
    (seen : impl ∈ r.declarations)
    (got : Survives (sourceCanonical r) (candidates p (sourceCanonical r) i waiting) d (canonicalDeclaration impl)) :
    Survives r (candidates p r i waiting) d impl :=
  ⟨⟨seen,got.1.2⟩,got.2⟩

theorem blocked_iff {s : State} (p : Supported s done) (same : SameWait waiting) :
    Blocked (sourceCanonical r) (candidates p (sourceCanonical r) i waiting) d ↔
      Blocked r (candidates p r i waiting) d := by
  constructor
  · rintro ⟨q,⟨listed,role⟩,yes⟩
    obtain ⟨impl,visible,rfl⟩ := List.mem_map.mp listed
    exact ⟨impl,⟨visible,role⟩,(same _ _).mp yes⟩
  · rintro ⟨impl,⟨listed,role⟩,yes⟩
    exact ⟨canonicalDeclaration impl,⟨List.mem_map_of_mem listed,role⟩,(same _ _).mpr yes⟩

theorem recurs_iff {s : State} (p : Supported s done) :
    Recurs s (sourceCanonical r) i (candidates p (sourceCanonical r) i waiting) d ↔
      Recurs s r i (candidates p r i waiting) d := by
  constructor
  · rintro (root | ⟨sel,good,pos,arg,pat,code,sees,pattern,printed,cycle⟩)
    · exact .inl root
    · obtain ⟨old,placed,rfl⟩ := List.mem_map.mp good.1.1
      exact .inr ⟨old,survives_prior placed good,pos,arg,pat,code,sees,pattern,printed,cycle⟩
  · rintro (root | ⟨sel,good,pos,arg,pat,code,sees,pattern,printed,cycle⟩)
    · exact .inl root
    · exact .inr ⟨canonicalDeclaration sel,survives_forward good,pos,arg,pat,code,sees,pattern,printed,cycle⟩

/-- Normalizing clause enumeration in this opt-in view doesn't make
any previously unread candidate viable, change K2, or elect another
declaration. Candidate waiting status must be insensitive to the
enumeration, not inferred solely from semantic model equality. -/
theorem election_exact {s : State} {p : Supported s done}
    (written : impl ∈ r.declarations) (same : SameWait waiting) :
    Elected s r i p (candidates p r i waiting) d impl ↔
      Elected s (sourceCanonical r) i p (candidates p (sourceCanonical r) i waiting) d
        (canonicalDeclaration impl) := by
  constructor
  · intro old
    refine ⟨old.ready,(fun c => old.guarded ((recurs_iff (r := r) (i := i) (waiting := waiting) p).mp c)),?_,
      survives_forward old.viable,?_⟩
    · intro possible
      exact old.clear ((blocked_iff p same).mp possible)
    · intro another viable
      obtain ⟨original,oldly,rfl⟩ := List.mem_map.mp viable.1.1
      exact old.unique original (survives_prior oldly viable)
  · intro canonical
    refine ⟨canonical.ready,(fun c => canonical.guarded ((recurs_iff (r := r) (i := i) (waiting := waiting) p).mpr c)),?_,
      survives_prior written canonical.viable,?_⟩
    · intro possible
      exact canonical.clear ((blocked_iff p same).mpr possible)
    · intro another viable
      exact canonical.unique (canonicalDeclaration another) (survives_forward viable)

end Yulang.GeneralStoppedCanonicalChoice335
