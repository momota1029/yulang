import YulangClosure.SimpleSubRegularPublication

/-!
Construct finite terminal evidence for the existing regular interpretation.

Starting with all well-indexed comparisons of the fixed finite graph, remove
comparisons whose actual structural expansion is not supported. Every strict
round shortens the finite list, and a stable round is precisely an accepted
postfixed certificate. All independently defined `RegularSub` comparisons
survive every round. The resulting certificate is therefore sound and complete
for that interpretation; it is no longer an externally supplied input.

This is a reference certificate construction on an already fixed graph, not a
replacement Simple-sub inference algorithm or an added production check. It
does not search over typings. Faithful native graph/history construction,
lattice/alias and open-row semantics, and original Call/source reconstruction
remain independent obligations. The elementary list algorithm makes no native
performance claim: it stores n_value^2 + n_effect^2 pairs, with at most that
many strict deletion rounds and linear-list membership in each child check.
-/
namespace YulangClosure.SimpleSub.RegularDecision
open Regular RegularPublication

def pruneStep (graph : Graph) (certificate : Regular.Certificate) : Regular.Certificate :=
  certificate.filter (checkPair graph certificate)

/-- Bounded deletion, with immediate exit at an actual fixed point. -/
def prune (graph : Graph) : Nat → Regular.Certificate → Regular.Certificate
  | 0, certificate => certificate
  | fuel + 1, certificate =>
      let next := pruneStep graph certificate
      if next = certificate then certificate else prune graph fuel next

theorem pruneStep_strict {graph : Graph} {certificate : Regular.Certificate}
    (changed : pruneStep graph certificate ≠ certificate) :
    (pruneStep graph certificate).length < certificate.length := by
  have le := List.length_filter_le (checkPair graph certificate) certificate
  have ne : (pruneStep graph certificate).length ≠ certificate.length := by
    intro same
    apply changed
    exact List.filter_eq_self.mpr (List.length_filter_eq_length_iff.mp same)
  change (pruneStep graph certificate).length ≤ certificate.length at le
  omega

theorem pruneStep_fixed_checked {graph : Graph} {certificate : Regular.Certificate}
    (fixed : pruneStep graph certificate = certificate) :
    checkCertificate graph certificate = true := by
  change certificate.filter (checkPair graph certificate) = certificate at fixed
  simpa only [checkCertificate, List.all_eq_true] using List.filter_eq_self.mp fixed

/-- A budget equal to the initial list length suffices, including the empty
case. No supplied stabilization or termination premise is used. -/
theorem prune_checked (graph : Graph) (fuel : Nat) (certificate : Regular.Certificate)
    (enough : certificate.length ≤ fuel) :
    checkCertificate graph (prune graph fuel certificate) = true := by
  induction fuel generalizing certificate with
  | zero =>
      have empty : certificate = [] := List.length_eq_zero_iff.mp (by omega)
      subst certificate
      rfl
  | succ fuel ih =>
      simp only [prune]
      split
      · exact pruneStep_fixed_checked ‹_›
      · apply ih
        have strict := pruneStep_strict ‹_›
        omega

def CoversRegular (graph : Graph) (certificate : Regular.Certificate) : Prop :=
  ∀ pair, RegularSub graph pair → pair ∈ certificate

theorem pruneStep_covers {graph : Graph} {certificate : Regular.Certificate}
    (covers : CoversRegular graph certificate) : CoversRegular graph (pruneStep graph certificate) := by
  intro pair regular
  apply List.mem_filter.mpr
  refine ⟨covers pair regular, (checkPair_iff graph certificate pair).mpr ?_⟩
  exact Layer.mono covers (regular_unfold.mp regular)

theorem prune_covers (graph : Graph) (fuel : Nat) (certificate : Regular.Certificate)
    (covers : CoversRegular graph certificate) : CoversRegular graph (prune graph fuel certificate) := by
  induction fuel generalizing certificate with
  | zero => exact covers
  | succ fuel ih =>
      simp only [prune]
      split
      · exact covers
      · exact ih _ (pruneStep_covers covers)

theorem prune_subset (graph : Graph) (fuel : Nat) (certificate : Regular.Certificate) :
    ∀ pair, pair ∈ prune graph fuel certificate → pair ∈ certificate := by
  induction fuel generalizing certificate with
  | zero => exact fun _ member => member
  | succ fuel ih =>
      simp only [prune]
      split
      · exact fun _ member => member
      · intro pair member
        exact (List.mem_filter.mp (ih _ pair member)).1

def kindPairs (kind : Kind) (size : Nat) : List Comparison :=
  (List.range size).flatMap (fun lower =>
    (List.range size).map (fun upper => ⟨kind, lower, upper⟩))

def allPairs (graph : Graph) : Regular.Certificate :=
  kindPairs .value (graph .value).length ++ kindPairs .effect (graph .effect).length

theorem mem_kindPairs (kind : Kind) (size : Nat) (pair : Comparison) :
    pair ∈ kindPairs kind size ↔
      pair.kind = kind ∧ pair.lower < size ∧ pair.upper < size := by
  constructor
  · intro member
    rcases List.mem_flatMap.mp member with ⟨lower, hlower, member⟩
    rcases List.mem_map.mp member with ⟨upper, hupper, same⟩
    subst pair
    exact ⟨rfl, List.mem_range.mp hlower, List.mem_range.mp hupper⟩
  · rcases pair with ⟨pairKind, lower, upper⟩
    rintro ⟨same, hlower, hupper⟩
    cases same
    exact List.mem_flatMap.mpr ⟨lower, List.mem_range.mpr hlower,
      List.mem_map.mpr ⟨upper, List.mem_range.mpr hupper, rfl⟩⟩

theorem mem_allPairs (graph : Graph) (pair : Comparison) :
    pair ∈ allPairs graph ↔
      pair.lower < (graph pair.kind).length ∧ pair.upper < (graph pair.kind).length := by
  rcases pair with ⟨kind, lower, upper⟩
  cases kind <;> simp [allPairs, mem_kindPairs]

theorem lookupList_index_lt {α : Type} {items : List α} {index : Nat} {item : α}
    (found : lookupList items index = some item) : index < items.length := by
  induction items generalizing index with
  | nil => cases found
  | cons head tail ih =>
      cases index with
      | zero => simp
      | succ index => exact Nat.succ_lt_succ (ih found)

theorem universe_covers (graph : Graph) : CoversRegular graph (allPairs graph) := by
  intro pair regular
  rcases regular_unfold.mp regular with ⟨children, expanded, _⟩
  rcases expand_endpoints_exist expanded with ⟨⟨lower, hlower⟩, ⟨upper, hupper⟩⟩
  exact (mem_allPairs graph pair).mpr ⟨lookupList_index_lt hlower, lookupList_index_lt hupper⟩

/-- Actual finite evidence, determined solely by the graph. -/
def constructCertificate (graph : Graph) : Regular.Certificate :=
  prune graph (allPairs graph).length (allPairs graph)

theorem constructed_checked (graph : Graph) :
    checkCertificate graph (constructCertificate graph) = true :=
  prune_checked graph _ _ (Nat.le_refl _)

theorem constructed_exact (graph : Graph) (pair : Comparison) :
    pair ∈ constructCertificate graph ↔ RegularSub graph pair := by
  constructor
  · exact certificate_sound (constructed_checked graph) pair
  · exact prune_covers graph _ _ (universe_covers graph) pair

/-- Graph validation is computed, even for empty demands. -/
def decideDemands (graph : Graph) (demands : List Comparison) : Bool :=
  accepts graph (constructCertificate graph) demands

theorem decideDemands_exact (graph : Graph) (demands : List Comparison) :
    decideDemands graph demands = true ↔ graph.Valid ∧ Holds graph demands := by
  simp only [decideDemands, accepts_iff, constructed_checked, true_and,
    constructed_exact, Holds]

theorem decideDemands_rejects_iff (graph : Graph) (demands : List Comparison) :
    decideDemands graph demands = false ↔ ¬ (graph.Valid ∧ Holds graph demands) := by
  rw [← decideDemands_exact]
  cases decideDemands graph demands <;> simp

theorem decided_original_demands {graph ref birth first last}
    (history : ConstraintHistory graph ref birth first last)
    (decided : decideDemands graph last.obligations = true) :
    graph.Valid ∧ Holds graph first.obligations :=
  accepted_original_demands history decided

theorem decided_store_history {graph refs store pairs events ref birth last}
    (decoded : decodeStore graph refs store = some pairs)
    (history : ConstraintHistory graph ref birth ⟨pairs, events⟩ last)
    (decided : decideDemands graph last.obligations = true) :
    graph.Valid ∧ StoreSatisfied graph refs store :=
  history_store_sound decoded history decided

/-- Application to the existing scoped publication theorem: there is no
certificate parameter or existential evidence-generation hypothesis. -/
theorem decided_publication_with_clients
    {n count bounds beforeCap afterCap beforeUse afterUse roots uses q graph refs}
    {inventory clients : Store} {pairs events ref birth last}
    (bounded : ScopedPublication.BoundsBounded n bounds)
    (images : ScopedPublication.InactiveImages n beforeUse afterUse q)
    (closed : ScopedPublication.StoppedClosed (bounds.map (ScopedPublication.Bound.rename q)) afterCap)
    (stops : ∀ k i, afterCap k i = false → afterUse k i = false)
    (useBounds : ∀ use, use ∈ uses → use < count)
    (coverage : ∀ clause,
      ScopedPublication.Published n (bounds.map (ScopedPublication.Bound.rename q)) afterCap afterUse
        (roots.map (ScopedPublication.Row.rename q)) uses clause → clause ∈ inventory)
    (decoded : decodeStore graph refs
      (inventory ++ clients.map (Constraint.rename (publicationTransport n count afterUse q))) = some pairs)
    (history : ConstraintHistory graph ref birth ⟨pairs,events⟩ last)
    (decided : decideDemands graph last.obligations = true) :
    graph.Valid ∧
      PublishedSatisfied graph (fun k i => refs k (publicationTransport n count afterUse q k i))
        n bounds beforeCap beforeUse roots uses ∧
      StoreSatisfied graph (fun k i => refs k (publicationTransport n count afterUse q k i)) clients :=
  publication_history_with_clients bounded images closed stops useBounds coverage decoded history decided

/-- Cycles are checked without providing a pair table or unfolding bound. -/
def twoCycles : Graph
  | .value => [.function 0 0 0 0, .function 1 0 0 1]
  | .effect => [.atom 7]

theorem two_cycles_decided : decideDemands twoCycles [⟨.value, 0, 1⟩] = true := by decide

theorem two_cycles_regular : RegularSub twoCycles ⟨.value, 0, 1⟩ :=
  ((decideDemands_exact _ _).mp two_cycles_decided).2 _ (by simp)

/-- The first expansion matches, but its result comparison fails. That failure
must propagate through the deletion rounds to reject the recursive roots. -/
def delayedMismatch : Graph
  | .value => [.function 0 0 0 2, .function 1 0 0 3, .atom 0, .atom 1]
  | .effect => [.atom 7]

theorem delayed_mismatch_decided :
    decideDemands delayedMismatch [⟨.value, 0, 1⟩] = false := by decide

theorem optional_mismatch_decided :
    decideDemands optionalMismatchGraph [⟨.value, 0, 1⟩] = false := by decide

theorem dangling_graph_decided :
    decideDemands danglingGraph [⟨.value, 0, 1⟩] = false := by decide

theorem dangling_empty_demands_decided : decideDemands danglingGraph [] = false := by decide

end YulangClosure.SimpleSub.RegularDecision
