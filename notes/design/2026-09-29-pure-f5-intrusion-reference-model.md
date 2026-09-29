# Pure F5 intrusion reference model

Status: Reviewed
Classification: historical research protocol; withdrawn as active gate on 2026-09-29
Scope: finite pure-Function characterization of SCC-preserving intrusion against current F5
Approved-by: none
Approved-at: none
Drafted-by: primary agent
Reviewed-by: architect, compiler_referee, spec_auditor
Supersedes: none
Implementation authority: none

This note defines the first research gate for the intrusion proposal. It does
not decide that parent variables are sound, replace F5, change a scheme
representation, or authorize compiler changes. It defines what a bounded
paper proof or test-only executable characterization must compare.

**Disposition:** the user later directed that F5 be abolished as the target of
the redesign. This protocol's F5-equivalence checks are historical review
evidence and are not a pass condition. The active direction is recorded in
`2026-09-29-scc-intrusion-redesign-charter.md`.

## 1. Authority and question

The reference behavior is the Authoritative F5 design, especially §§8–9, 23,
25, and 33. The 2026-09-29 intrusion notes are hypotheses only. The question
is:

> Given the same pure-F5 input before bound insertion, does candidate
> intrusion preserve the resulting live state, each member's F5 closed scheme,
> and every consuming use, while retaining internal SCC uses as open roots?

Two claims must be kept separate:

1. **Constraint equivalence:** both paths admit the same relevant live
   constraints.
2. **F5 observation equivalence:** each member has the same closed scheme up
   to alpha-equivalence, including Q/R ownership and both recursive bounds;
   independent incoming-use and internal-use behavior also agrees.

Constraint equivalence alone does not establish the second claim. No compact
output or complexity claim follows from either claim.

## 2. Input, transitions, and frozen draft state

Distinguish pre-insertion input `I` from post-insertion draft state `S`. `I`
records the typed graph, levels, ordered bound-insertion recipes with exact
endpoint and cause identities, the component and enclosing environment, and
each `DefinitionUse` with its consuming `use_level`. Reference transition
`T_F5(I)` admits these recipes in F5 order, including insertion-time extrusion
of reachable younger variables. A candidate transition `T_P(I)` would apply
intrusion and edge transport to the same input. Its algorithm and parent
relation remain unresolved; this note does not select them. Compare resulting
levels, exact bounds, causes/provenance, and later generalization and use
observations. Current F5 `extrude` is level aging during insertion. A
post-state-only comparison proves per-member generalization/projection
equivalence only; replacement of extrusion requires the paired transitions.

Use a finite state `S = (G, L, B, E, C)` at the existing F5 component draft
barrier after either transition:

- `G` is the typed live graph. Every live value variable has its exact lower
  and upper bound rows, including direct variable edges, structural
  constructors, and the original endpoint/cause identity needed by the
  reference path. Pure F5 effect rows remain fixed at the approved pure
  subset; this gate adds no effect generalization.
- `L(v)` is the level of each live value variable.
- `B` is the target generalization boundary for the member draft.
- `E` is the pre-component enclosing environment, including rigid closed
  binders and variables marked non-generic before this component.
- `C` identifies the definition SCC, its ordered members and roots, and its
  exact internal and incoming uses, including consuming `use_level`. It does
  not define graph reachability.

The state is copied/frozen for each side of a comparison. Bound rows cannot
change during either member-drafting pass. A candidate may not mutate the
reference snapshot or publish partial member results.

Generalization reachability is computed from the post-insertion state, without restricting to
`C`. For each member root, start in positive polarity, follow every exact bound
and structural edge under F5's polarity rules, and continue until the finite
`(variable, polarity)` worklist is closed. Record outside-SCC descendants and
enclosing non-generic endpoints explicitly. Opposite-polarity states remain
distinct unless a proof establishes a valid identification.

## 3. Reference semantics

For every component member independently, the reference path applies F5
generalization to its live root from `S`:

1. Expand exact polarized bounds and guarded active-path re-entry.
2. Compute non-generic closure from `E`; compute eligibility before
   elimination using the target boundary `B`.
3. Classify retained guarded R owners before one-sided elimination.
4. Eliminate only eligible positive-only variables to Bottom and negative-only
   variables to Top; assign Q only to remaining eligible bipolar non-R
   variables.
5. Keep the member's Q/R namespace, active path, pruning, ordering, and closed
   mapping local to that root.
6. Validate closure and compare the canonical finalized scheme, including
   predicate, Q binders, ordered R records, and each R lower and upper side.

The reference retains F5's atomic component publication rule: all member
schemes are prepared before any incoming use can observe them.

## 4. Candidate relation under investigation

Do not assume one parent per source variable. Model the candidate initially as
a partial relation over boundary-facing polarized states:

```text
P : (source variable, polarity, boundary, enclosing environment)
      -> candidate parent identity
```

This key is a research parameter, not an approved representation. Experiments
may test whether adding a component discriminator is necessary, but must show
the corresponding states remain observationally equivalent. The candidate must
state which reachable states receive parents and which remain rigid or
component-local. It must transport exact lower/upper rows and structural edges
through the relation without silently lowering a level, merging opposite
polarities, quantifying an enclosing non-generic endpoint, or inventing a
missing bound.

Per-member closed projection remains F5-shaped in this gate. If an immutable
shared intruded graph is used internally, each member gets its own Q/R map and
projection. Every incoming use gets a separate overlay:

```text
sigma(member, use) : that member's local Q/R -> fresh live identities
```

Repeated occurrences of one binder within one use map to one identity;
different uses do not share fresh identities. Internal SCC uses bypass this
overlay and continue to connect to the target's open live root. The candidate
graph is immutable after publication; a use-site substitution cannot write
back into it. Fresh Q/R identities are allocated at each consuming
`DefinitionUse.use_level`; compare their levels and later generalization
behavior. Clone each reachable closed node at most once per use, preserving
sharing, and restore both lower and upper R sides before routing the predicate.
Preserve the exact use cause and instantiation provenance. Allocation,
validation, or finalization failure publishes no partial component or
`SolvedModule`. All member schemes must be installed before an incoming use.

These requirements make the comparison meaningful. They do not prove a parent
construction exists.

## 5. Finite comparison procedure

For each fixture:

1. Construct one finite `I`, run both transitions, and compare post-insertion
   levels, bounds, causes, and provenance. If only frozen `S` is available,
   label the result projection-only evidence.
2. Record the per-root polarized closure as `(variable, polarity)` states,
   including levels, boundary eligibility, non-generic membership, exact lower
   and upper edges, and Function-field transitions.
3. Run the F5 reference path independently for each member and canonicalize
   each closed scheme by binder identity/order rather than arena handles.
4. Run the candidate parent relation and edge transport, then perform the
   candidate's per-member projection and canonicalization.
5. Compare both constraint consequences and exact per-member schemes by
   structural alpha-equivalence, including recursive lower/upper records.
   Separately compare canonical Q ordinals and encounter order, and canonical
   R ordinals and order; alpha-equivalence alone cannot establish these.
6. Instantiate the same member twice with incompatible incoming constraints,
   then interleave a use of another member, a repeated occurrence within one
   use, and an internal SCC use. Compare fresh identities, consuming levels,
   later generalization behavior, admitted constraints, per-use closed-node
   sharing, use cause/provenance, and the unchanged published graph. Inject
   allocation and finalization failures and check atomic publication and
   all-member installation before incoming use.
7. Draft members in forward, reverse, and rotated orders. Canonical schemes,
   diagnostics, and per-use behavior must be invariant under root order.

A paper derivation can discharge a fixture if it lists all transitions and
identities. An executable characterization must use an independent, small
reference model; it must not call the production candidate algorithm to
compute expected values. Finite fixtures establish only those witnesses. A
universal extrusion-replacement claim requires a simulation relation and
induction invariant for insertion, generalization, publication, and use.

## 6. Minimum discriminating fixtures

The first finite set is:

1. **Identity and constant:** ordinary Q creation and one-sided Bottom/Top
   simplification.
2. **Shared polarity-changing Function:** one variable occurs through both
   argument and result paths, has nontrivial lower and upper bounds, and
   reaches an enclosing non-generic endpoint outside the definition SCC.
3. **Shared diamond / outside-SCC descendant:** multiple paths converge on a
   shared variable, with a younger reachable node that is not an SCC member.
4. **Boundary equality:** contrast `L(v) = B` with `L(v) > B`; test elimination
   at equality and prohibit Q quantification there.
5. **Unguarded cycle:** direct variable/bound aggregation cycle with no
   Function step; no guarded R may appear.
6. **Guarded self and mutual recursion:** retain R and compare both completed
   lower and upper sides, with one R owner across polarity re-entry.
7. **Root-local binders and order:** two SCC members with distinct Q/R
   ownership, drafted forward/reverse/rotated. Add two asymmetric retained Q
   occurrences whose swapped ordinals leave alpha-equivalence intact but
   violate F5's normalized first-occurrence order.
8. **Independent uses:** instantiate one member twice with incompatible
   incoming constraints, then interleave uses of the other member; prove
   separate fresh overlays even for repeated uses of one member,
   repeated-binder sharing within each use, per-use closed-node sharing,
   consuming levels, later generalization, cause/provenance, and no
   mutation/leakage between uses.
9. **Internal use:** after the incoming-use sequence, connect an internal use
   to the open live root without freshening.
10. **Failure and publication:** fail allocation and finalization after an
    earlier member draft, check no partial publication, then verify every
    member is installed before the first incoming use.

The guarded-cycle scale family is not a first-gate measurement. Do not repeat
the consumed F5c resource captures. First establish semantics on finite small
graphs; only then may a separately approved question address compact output or
cost.

## 7. Stop conditions

Stop and revise the candidate on any of these observations:

- positive and negative approximations collapse without a proof;
- an outer/non-generic endpoint is captured, quantified, or rewritten;
- a boundary-equal variable becomes Q;
- Bottom/Top elimination changes;
- guarded R ownership, order, or either bound side changes;
- member-local Q/R identities merge or depend on root traversal order;
- incoming uses share fresh state, or mutate published component state;
- fresh identities have the wrong consuming level or change later
  generalization; use cause/provenance or per-use closed-node sharing differs;
- either R bound side is missing after restoration, or failure publishes a
  partial component or `SolvedModule`;
- an incoming use is admitted before every member scheme is installed;
- canonical Q ordinals/order differ despite structural alpha-equivalence;
- internal SCC uses are freshened;
- any member's closed scheme fails structural alpha-equivalence;
- closure validation finds a free or misclassified live variable.

Failure of exact F5 observation equivalence does not by itself refute every
compact representation. It does refute an implementation that claims to
preserve the current F5 contract. Any intentional contract or scheme-shape
change needs a separate reviewed design and explicit user approval.

## 8. Current implementation locators

The characterization can be test-only; this note authorizes no such edit yet.
Useful current locations are:

- `crates/yu-solver/src/lib.rs`: `VariableBounds` near 3697;
  `InferenceSession` near 7198; `extrude_value_endpoint` / `extrude` near
  10656–10668; live-bound admission near 11048; closed-scheme instantiation
  near 14525; per-component member drafting near 15160.
- `crates/yu-solver/src/f5c_generalization.rs`: per-root non-generic closure
  near 9149; eligibility in `build_inner_work` near 11349–11547; root-local
  post-R/Q assignment near 10802–11015.
- `crates/yu-solver/src/f5c_binder_substitution.rs`: per-root Q/R binder
  substitution.
- `crates/yu-types/src/lib.rs`: `ClosedValueSchemeView::alpha_eq` near 684
  provides closed-scheme structural alpha-equivalence.

The current `extrude` operation ages reachable variables during bound
insertion; it is not a fresh-parent implementation. A candidate for replacing
that operation needs the paired pre-insertion transition comparison in §2.
The frozen-state comparison separately examines per-member generalization and
projection, without establishing transition equivalence.

## 9. Gate sequence

1. **This note:** fix the finite reference state and comparison contract;
   independent semantic and F5-conformance review; no implementation.
2. **Characterization:** manually derive the minimum witnesses or build a
   private test-only reference model, then record the first equivalence or
   counterexample. No public API or F5 behavior changes.
3. **Representation decision:** only if the evidence supports a candidate,
   specify whether it can preserve exact F5 schemes or requires a new internal
   or public scheme contract. Independent review and explicit user approval
   precede implementation of any new durable decision.
4. **Separate future gate:** effect hygiene transport, including binder
   ownership, freshness, path-sensitive boundary evidence, and handler
   semantics. It is excluded from the pure-F5 characterization.
