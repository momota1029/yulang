import Yulang.GeneralFiniteQuotientRepresentatives306
import Yulang.GeneralFiniteColoredEarlyStop306

namespace Yulang.GeneralFiniteColoredQuotient306
open GeneralFiniteColoredRounds306 (On Closed)
open GeneralFiniteColoredEquivalence306 (test test_exact refl_on symm_on trans_on)
open GeneralFiniteQuotientRepresentatives306 (representatives sublist distinct no_two select selected select_exists)
variable {α β : Type} [DecidableEq α] [DecidableEq β]

structure QuotientGraph (α : Type) where
  representatives : List α
  project : α → Option α
  edges : α → List α

def assemble (edges : α → List α) (rel : α → α → Bool) (nodes : List α) : QuotientGraph α :=
  let reps := representatives rel nodes
  let pin := fun x => reps.find? (rel x)
  ⟨reps,pin,fun r => (edges r).filterMap pin⟩

def quotient (edges : α → List α) (observe : α → β) (nodes : List α) : QuotientGraph α :=
  let memo := GeneralFiniteColoredTable306.compile edges observe nodes
  assemble edges (GeneralFiniteColoredTable306.lookup memo) nodes

def fastQuotient (edges : α → List α) (observe : α → β) (nodes : List α) : QuotientGraph α :=
  let memo := GeneralFiniteColoredEarlyStop306.fastCompile edges observe nodes
  assemble edges (GeneralFiniteColoredTable306.lookup memo) nodes

theorem fast_exact (edges : α → List α) (observe : α → β) (nodes : List α) :
    fastQuotient edges observe nodes = quotient edges observe nodes := by
  unfold fastQuotient quotient
  rw [GeneralFiniteColoredEarlyStop306.exact_fast]

variable {edges : α → List α} {observe : α → β} {nodes : List α}
local notation "Q" => quotient edges observe nodes
local notation "T" => test edges observe nodes

theorem in_domain {r : α} (h : r ∈ (Q).representatives) : r ∈ nodes :=
  (sublist T nodes).subset h

theorem projection_total (closed : Closed edges nodes) {x : α} (xm : x ∈ nodes) :
    ∃ r, (Q).project x = some r :=
  select_exists (fun _ found => refl_on closed found) xm

theorem projection_sound {x r : α} (found : (Q).project x = some r) :
    r ∈ (Q).representatives ∧ T x r = true :=
  selected found

theorem projection_respects (closed : Closed edges nodes) {x y : α} (xm : x ∈ nodes) (ym : y ∈ nodes) :
    (Q).project x = (Q).project y ↔ T x y = true := by
  obtain ⟨a,left⟩ := projection_total (observe := observe) closed xm
  obtain ⟨b,right⟩ := projection_total (observe := observe) closed ym
  rw [left,right]
  have first := projection_sound left
  have second := projection_sound right
  have am := in_domain first.1
  have bm := in_domain second.1
  constructor
  · intro code
    cases Option.some.inj code
    exact trans_on closed xm am ym first.2 (symm_on closed ym am second.2)
  · intro same
    have pair : T a b = true :=
      trans_on closed am ym bm (trans_on closed am xm ym (symm_on closed xm am first.2) same) second.2
    have eq := no_two T (Q).representatives
      (fun _ pm _ qm h => symm_on closed (in_domain pm) (in_domain qm) h)
      (distinct T nodes) a b first.1 second.1 pair
    exact congrArg some eq

theorem representative_fixed (closed : Closed edges nodes) {r : α} (atRep : r ∈ (Q).representatives) :
    (Q).project r = some r := by
  obtain ⟨q,chosen⟩ := projection_total (observe := observe) closed (in_domain atRep)
  have good := projection_sound chosen
  have identical := no_two T (Q).representatives
    (fun _ pm _ qm h => symm_on closed (in_domain pm) (in_domain qm) h)
    (distinct T nodes) r q atRep good.1 good.2
  exact identical.symm ▸ chosen

theorem exact_edges (closed : Closed edges nodes) {x r q : α}
    (xm : x ∈ nodes) (chosen : (Q).project x = some r) :
    q ∈ (Q).edges r ↔ ∃ y ∈ edges x, (Q).project y = some q := by
  have sound := projection_sound chosen
  have rm := in_domain sound.1
  obtain ⟨_,bisim,matched⟩ := (test_exact closed xm rm).mp sound.2
  have both := bisim x xm r rm matched
  change q ∈ (edges r).filterMap (Q).project ↔ _
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨y,yListed,yOut⟩
    obtain ⟨z,zListed,rel⟩ := both.2.2 y yListed
    have zm := closed x xm z zListed
    have ym := closed r rm y yListed
    have same := (projection_respects closed zm ym).mpr ((test_exact closed zm ym).mpr ⟨_,bisim,rel⟩)
    exact ⟨z,zListed,same.trans yOut⟩
  · rintro ⟨z,zListed,zOut⟩
    obtain ⟨y,yListed,rel⟩ := both.2.1 z zListed
    have zm := closed x xm z zListed
    have ym := closed r rm y yListed
    have same := (projection_respects closed zm ym).mpr ((test_exact closed zm ym).mpr ⟨_,bisim,rel⟩)
    exact ⟨y,yListed,same.symm.trans zOut⟩

theorem quotient_closed {r q : α} (edge : q ∈ (Q).edges r) :
    q ∈ (Q).representatives := by
  change q ∈ (edges r).filterMap (Q).project at edge
  obtain ⟨x,_,found⟩ := List.mem_filterMap.mp edge
  exact (projection_sound found).1

theorem projection_minimal (closed : Closed edges nodes) {rel : α → α → Prop}
    (bisim : On edges observe nodes rel) {x y : α} (xm : x ∈ nodes) (ym : y ∈ nodes)
    (same : rel x y) : (Q).project x = (Q).project y :=
  (projection_respects closed xm ym).mpr ((test_exact closed xm ym).mpr ⟨_,bisim,same⟩)

end Yulang.GeneralFiniteColoredQuotient306
