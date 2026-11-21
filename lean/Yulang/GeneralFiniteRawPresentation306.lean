import Yulang.GeneralFiniteColoredCertificate306

namespace Yulang.GeneralFiniteRawPresentation306
open GeneralFiniteColoredRounds306 (Closed On)
open GeneralFiniteColoredQuotient306 (fastQuotient fast_exact projection_total projection_sound in_domain
  projection_respects projection_minimal exact_edges)
variable {Raw α β : Type} [DecidableEq α] [DecidableEq β]

/-- The lists are abstract successors. Raw successors need not be finite. -/
structure Presentation (admitted : Raw → Prop) (step : Raw → Raw → Prop)
    (project : Raw → α) (color : Raw → β) (edges : α → List α)
    (abstractColor : α → β) (nodes : List α) : Prop where
  closed : Closed edges nodes
  inside : ∀ s, admitted s → project s ∈ nodes
  keepRaw : ∀ s t, admitted s → step s t → admitted t
  color_exact : ∀ s, admitted s → abstractColor (project s) = color s
  transitions : ∀ s, admitted s → ∀ p, p ∈ edges (project s) ↔ ∃ t, step s t ∧ project t = p

def StrongRaw (admitted : Raw → Prop) (step : Raw → Raw → Prop) (color : Raw → β)
    (rel : Raw → Raw → Prop) : Prop :=
  ∀ a b, admitted a → admitted b → rel a b →
    color a = color b ∧
      (∀ t, step a t → ∃ u, step b u ∧ rel t u) ∧
      (∀ u, step b u → ∃ t, step a t ∧ rel t u)

variable {admitted : Raw → Prop} {step : Raw → Raw → Prop} {project : Raw → α}
  {color : Raw → β} {edges : α → List α} {abstractColor : α → β} {nodes : List α}
local notation "Q" => fastQuotient edges abstractColor nodes
local notation "P" => Presentation admitted step project color edges abstractColor nodes

theorem base_total (v : P) {s : Raw} (live : admitted s) :
    ∃ q, (Q).project (project s) = some q := by
  rw [fast_exact]
  exact projection_total v.closed (v.inside s live)

theorem raw_edges (v : P) {s : Raw} (live : admitted s) {r q : α}
    (chosen : (Q).project (project s) = some r) :
    q ∈ (Q).edges r ↔ ∃ t, step s t ∧ (Q).project (project t) = some q := by
  rw [fast_exact] at chosen ⊢
  rw [exact_edges v.closed (v.inside s live) chosen]
  constructor
  · rintro ⟨y,listed,found⟩
    obtain ⟨t,act,eq⟩ := (v.transitions s live y).mp listed
    exact ⟨t,act,eq.symm ▸ found⟩
  · rintro ⟨t,act,found⟩
    exact ⟨project t,(v.transitions s live _).mpr ⟨t,act,rfl⟩,found⟩

omit [DecidableEq α] [DecidableEq β] in
theorem abstract_rel {rel : Raw → Raw → Prop} (v : P) (b : StrongRaw admitted step color rel) :
    On edges abstractColor nodes (fun x y =>
      ∃ s t, admitted s ∧ admitted t ∧ rel s t ∧ project s = x ∧ project t = y) := by
  rintro x _ y _ ⟨s,t,admS,admT,holds,rfl,rfl⟩
  obtain ⟨observed,forward,back⟩ := b s t admS admT holds
  refine ⟨(v.color_exact s admS).trans (observed.trans (v.color_exact t admT).symm),?_,?_⟩
  · intro a edge
    obtain ⟨s',raw,yes⟩ := (v.transitions s admS a).mp edge
    obtain ⟨t',copied,matched⟩ := forward s' raw
    exact ⟨project t',(v.transitions t admT _).mpr ⟨t',copied,rfl⟩,
      s',t',v.keepRaw s s' admS raw,v.keepRaw t t' admT copied,matched,yes,rfl⟩
  · intro a edge
    obtain ⟨t',raw,yes⟩ := (v.transitions t admT a).mp edge
    obtain ⟨s',copied,matched⟩ := back t' raw
    exact ⟨project s',(v.transitions s admS _).mpr ⟨s',copied,rfl⟩,
      s',t',v.keepRaw s s' admS copied,v.keepRaw t t' admT raw,matched,rfl,yes⟩

theorem minimal {rel : Raw → Raw → Prop} (v : P) (b : StrongRaw admitted step color rel)
    {s t : Raw} (admS : admitted s) (admT : admitted t) (h : rel s t) :
    (Q).project (project s) = (Q).project (project t) := by
  rw [fast_exact]
  exact projection_minimal v.closed (abstract_rel v b) (v.inside s admS) (v.inside t admT)
    ⟨s,t,admS,admT,h,rfl,rfl⟩

theorem color_preserved (v : P) {s t : Raw} (admS : admitted s) (admT : admitted t)
    (same : (Q).project (project s) = (Q).project (project t)) : color s = color t := by
  rw [fast_exact] at same
  have related := (projection_respects v.closed (v.inside s admS) (v.inside t admT)).mp same
  obtain ⟨_,b,h⟩ := (GeneralFiniteColoredEquivalence306.test_exact v.closed
    (v.inside s admS) (v.inside t admT)).mp related
  exact (v.color_exact s admS).symm.trans ((b _ (v.inside s admS) _ (v.inside t admT) h).1.trans
    (v.color_exact t admT))

theorem stable (v : P) :
    StrongRaw admitted step color (fun s t => (Q).project (project s) = (Q).project (project t)) := by
  intro s t admS admT same
  obtain ⟨r,atS⟩ := base_total v admS
  have atT : (Q).project (project t) = some r := same ▸ atS
  refine ⟨color_preserved v admS admT same,?_,?_⟩
  · intro u edge
    obtain ⟨q,uq⟩ := base_total v (v.keepRaw s u admS edge)
    have e := (raw_edges v admS atS).mpr ⟨u,edge,uq⟩
    obtain ⟨w,step',same'⟩ := (raw_edges v admT atT).mp e
    exact ⟨w,step',uq.trans same'.symm⟩
  · intro w edge
    obtain ⟨q,wq⟩ := base_total v (v.keepRaw t w admT edge)
    have e := (raw_edges v admT atT).mpr ⟨w,edge,wq⟩
    obtain ⟨u,step',same'⟩ := (raw_edges v admS atS).mp e
    exact ⟨u,step',same'.trans wq.symm⟩

end Yulang.GeneralFiniteRawPresentation306
