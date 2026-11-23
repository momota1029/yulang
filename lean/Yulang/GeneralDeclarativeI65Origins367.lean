import Yulang.GeneralDeclarativeI65State365

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open CommonRecursiveNominalIntervals (Endpoint)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarations (Declaration)

/-- This enumeration reads only actual stored origins and exact
owner-indexed routes. It keeps multiple certifying paths visible if
they point at different physical positions. -/
def routeMember (s : State) (logical : Nat) (origin : Origin) : Bool :=
  (origin.slot == logical) ||
  s.routes.any (fun row => (row.logical == logical) && (row.physical == origin.slot) &&
    (row.issuer == origin.issuer))

def physicalSources (s : State) (logical : Nat) : List Nat :=
  (s.origins.filter (routeMember s logical)).map Origin.slot

theorem actual_route_iff {s : State} {logical : Nat} {origin : Origin} :
    routeMember s logical origin = true ↔ OriginRoute s origin logical := by
  unfold routeMember
  simp only [Bool.or_eq_true,beq_iff_eq,List.any_eq_true,Bool.and_eq_true]
  constructor
  · rintro (rfl | ⟨row,recorded,⟨l,p⟩,i⟩)
    · exact .direct
    · rcases row with ⟨logical',physical,issuer⟩
      change logical' = logical at l
      change physical = origin.slot at p
      change issuer = origin.issuer at i
      subst logical'
      subst physical
      subst issuer
      exact .authored recorded
  · intro route
    cases route with
    | direct => exact .inl rfl
    | authored h => exact .inr ⟨_,h,⟨rfl,rfl⟩,rfl⟩

theorem physical_sources_exact {s : State} {logical slot : Nat} :
    slot ∈ physicalSources s logical ↔
      ∃ original ∈ s.origins, OriginRoute s original logical ∧ original.slot = slot := by
  simp only [physicalSources,List.mem_map,List.mem_filter,actual_route_iff]
  constructor
  · rintro ⟨a,⟨b,c⟩,d⟩
    exact ⟨a,b,c,d⟩
  · rintro ⟨a,b,c,d⟩
    exact ⟨a,⟨b,c⟩,d⟩

def SinglePhysical (s : State) (logical : Nat) : Prop :=
  ∀ a ∈ physicalSources s logical, ∀ b ∈ physicalSources s logical, a = b

theorem physical_origin_is_not_logical_equality {s : State} {logical : Nat} {a b : Origin}
    (unique : SinglePhysical s logical)
    (aIn : a ∈ s.origins) (bIn : b ∈ s.origins)
    (aFrom : OriginRoute s a logical) (bFrom : OriginRoute s b logical) :
    a.slot = b.slot :=
  unique _ (physical_sources_exact.mpr ⟨a,aIn,aFrom,rfl⟩)
    _ (physical_sources_exact.mpr ⟨b,bIn,bFrom,rfl⟩)

theorem same_native_slot_same_endpoint {s : State} {a b : Origin}
    (aIn : a ∈ s.origins) (bIn : b ∈ s.origins) (slot : a.slot = b.slot)
    (m : Model) (fit : Fits s m) : a.endpoint = b.endpoint := by
  have earlier := fit.2 _ aIn
  have later := fit.2 _ bIn
  rw [slot] at earlier
  exact Option.some.inj (earlier.symm.trans later)

/-- Exact one-position mismatch in the declared native lane. Other
representations require their own source rule; absence of a positive
certificate is never used here as rejection. -/
structure RigidMismatch (s : State) (arg : Capture) (pat : Pattern) where
  source : Origin
  authoritative : source ∈ s.origins
  atLower : OriginRoute s source arg.lower
  unique : SinglePhysical s arg.lower
  observed : Nat
  observedArguments : List (CommonRecursiveNominalIntervals.Argument Nat)
  observedHead : source.endpoint = .nominal observed observedArguments
  wanted : Nat
  wantedArguments : List Pattern
  wantedHead : normalize pat = .app wanted wantedArguments
  clash : wanted ≠ observed

theorem rigid_mismatch_excludes_same_lane {s : State} {arg : Capture} {pat : Pattern}
    (conflict : RigidMismatch s arg pat) (other : ModeWindow s arg pat)
    (m : Model) (fit : Fits s m) : False := by
  have physical := physical_origin_is_not_logical_equality conflict.unique conflict.authoritative
    other.lowerAuthored conflict.atLower other.lo
  have equal := same_native_slot_same_endpoint conflict.authoritative other.lowerAuthored physical m fit
  rw [conflict.observedHead,other.firstHead] at equal
  have same := (Endpoint.nominal.inj equal).1
  have authored := (Pattern.app.inj (conflict.wantedHead.symm.trans other.syntaxHead)).1
  exact conflict.clash (authored.trans same.symm)

end Yulang.GeneralDeclarativeI65
