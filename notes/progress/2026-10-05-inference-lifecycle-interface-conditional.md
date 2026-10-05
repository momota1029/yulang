# Conditional lifecycle theorem at a rebuilt inference boundary

Date: 2026-10-05
Status: Reviewed conditional mathematical derivation; research-only, no implementation authority
Baseline: `33bf4522b77587cdcdc5fab9c21f0da5b12e723b`
Scope: sufficient conditions for downstream inference reuse after component rebuild, including SCC repartition
Implementation authority: none
Independent review: compiler_referee and spec_auditor; both found no BLOCKING, major, or minor findings within their stated scopes
Supersedes: none

## 1. Result and authority boundary

There is a useful conditional result beyond repeating the
[Authoritative rebuild addendum](../design/2026-10-04-scc-intrusion-cross-edit-rebuild-addendum.md):
**a simultaneous complete boundary interface can be substituted across a
changed SCC partition, provided the enclosing inputs, dependency cut, use
incidence, scope correspondence, and publication conditions below hold.**
The proof is a substitution argument. It does not construct a complete
interface, its canonical form, or a decidable equality algorithm.

The [redesign charter](../design/2026-09-29-scc-intrusion-redesign-charter.md)
§§1–5 governs the research target: retain meaningful source constraints,
enclosing non-generic sharing, fresh independent incoming uses, open live
internal uses, and sound/principal publication. The addendum permits rebuild
instead of reverse update; its remaining representation obligations are open.

The existing [F4 lifecycle](../design/2026-09-21-oracle-aligned-f4-int-scheme-scc-draft.md)
§§1, 7 provides the all-member draft visibility and incoming-use ordering only
for its Integer/resolved-Name scope. Here these are explicit lifecycle
hypotheses for a successor, not an extension of F4 authority to Function or
effects. The draft/generalization representation is deliberately unspecified.

The [source-generated theorem package](../design/2026-10-04-source-generated-callback-structural-theorems.md)
Theorem C §2.4 and the
[source-indexed realization](../design/2026-10-04-source-indexed-callback-realization.md)
§§2, 3.3 illustrate joint hiding and retained scope/dependency correspondence.
Their finite decorated immutable, monomorphic-recursion envelope does not prove
general polymorphic generalization or this lifecycle's premises. Theorem S
§8.3 explicitly distinguishes one regular witness from the principal relation.

## 2. Abstract objects and assumptions

Let versions `v=0,1` be source snapshots before and after an edit. Let `R_v`
be a rebuild region consisting of complete SCCs of that version's dependency
graph. Its boundary exports have a fixed logical correspondence `B` between
versions. This correspondence names the same downstream-visible roles; it
does not require equal arena addresses, internal members, or SCC numbers.

Write `Gamma` for all enclosing non-generic inputs and other dependencies of
the comparison. Equality of their meaning includes their sharing and scope;
equal printed types of distinct enclosing variables do not establish this.
An interface can include `Gamma` or be parameterized by it. A consumer also
has its unchanged source, imports and checking configuration, denoted `Delta`.

A **complete generalized interface** `I_v` is abstractly an interface whose
equality preserves every downstream-inference-observable generalized
constraint, coupled effect, scope relationship and required evidence. This
includes observations of independent use instantiation and jointly dependent
views, not just a root's displayed value. Define equality relative to the
same `Gamma` and to the complete boundary correspondence, including use and
scope incidence. No concrete list of fields is selected here.

The sufficient hypotheses are:

1. **Valid rebuild.** Each version's region is inferred/generalized by a valid
   implementation of the same supported semantics. The new region is solved
   from current inputs; old level, intrusion and bound state is not a required
   input. Soundness/principality of that implementation is a premise.
2. **Complete factorization.** All interactions by an unchanged downstream
   consumer with `R_v` factor through `I_v`, `Gamma` and the boundary/use
   correspondence. There is no hidden dependence on an old live root, internal
   arena layout, source body or version-specific solver state. This is a real
   obligation, not something interface naming establishes.
3. **Unchanged other inputs.** `Gamma` and each reused consumer's `Delta` have
   the same meaning. The interface comparison and consumers use one consistent
   snapshot of those inputs.
4. **Complete equality.** `I_0 = I_1` in the above sense, including all joint
   relations required by surviving downstream views. The equality witness is
   scope preserving. A consistent renaming may change local names, but cannot
   capture an enclosing variable or change a rigid binder's quantifier order.
5. **Lifecycle/transport validity.** Inside a component, internal uses retain
   the current attempt's live roots. All member drafts are available before
   cross-member finalization; no incoming use observes that component before
   its complete generalized result is available. Distinct incoming uses get
   fresh independent substitutions for generalized local identities; imported
   non-generic identities remain shared. All constraint, effect and evidence
   incidences use those same identity maps. Aliases of a single use are not
   silently turned into independent uses.
6. **Publication and cached-result validity.** No partial or mixed-version
   result is exposed as a successful new result. A cached result is interpreted
   through the boundary correspondence, with valid retained references or an
   adequate transport of them. The same observation includes acceptance,
   residual/principal solution information and required inference evidence.

An equality comparison made only after projecting away these hypotheses is
outside the theorem. If a consumer's evidence has source-location or diagnostic
dependencies, those must either be included in the specified inference
observation/inputs or be invalidated separately; this note does not classify
the compiler's diagnostics artifacts.

## 3. Theorem and proof

**Conditional boundary substitution theorem.** Under §2's hypotheses,
replacing the old region with the successfully rebuilt region preserves every
specified inference observation of an unchanged downstream consumer. Therefore
that consumer's valid cached inference result may be reused, after the required
scope/reference correspondence. This holds even if the region's internal SCC
partition splits or merges. It also applies successively to an unchanged
downstream dependency region whose other inputs remain unchanged.

**Proof.** By factorization, the consumer's inference observations have the
form `ObsInfer(Delta, Gamma, I_v, use-correspondence)`. Complete interface
equality makes the two argument tuples indistinguishable under every permitted
consumer inference observation. The other inputs are equal by hypothesis.
Thus the consumer's acceptance and full residual/evidence observations agree.
Cached-reference validity then permits reuse of that result rather than just
asserting existence of an equivalent result.

For a concrete sufficient proof pattern, a proposed semantic interface may
denote an open joint relation `J_v(B; Gamma)`, with binders retained at their
original scopes. Assume its equality witness transports the full relations,
not only separate port projections. A consumer formula `H(Delta,Gamma,B,W)`
then sees the same joint formula in both versions:

```text
J_0(B; Gamma) = J_1(B; Gamma)

J_0(B; Gamma) and H(Delta,Gamma,B,W)
  = J_1(B; Gamma) and H(Delta,Gamma,B,W).
```

Applying the same scope-preserving hiding and observation map preserves this
equality. This is substitution of the same relation; it exchanges no binders
and composes no successful concrete Function inequalities. The displayed
relation is a sufficient mathematical model, not a chosen solver carrier.

For incoming uses, apply the matching freshening map for each use occurrence
in both versions. Since all incident constraints/evidence are transported
together, equality is preserved. Fresh generalized locals of distinct uses
are disjoint, and the maps fix the shared enclosing inputs. Internal uses
are already accounted for by the solved region and are not freshened as
incoming uses while their component remains open.

The proof refers only to the complete boundary interface, not its internal
partition. Hence it is unchanged by a split or merge satisfying the boundary
hypotheses. Apply the same argument in dependency order to further unchanged
consumers; a cyclic group of such consumers must be treated jointly rather
than by a circular induction. Publication supplies a complete snapshot at
each observation. QED.

The first paragraph is an abstract substitutivity corollary of completeness.
The added reusable content is the simultaneous cut, use/scope transport and
partition argument, plus the explicit conditions distinguishing a semantic
equivalence proof from permission to reuse actual cached artifacts. It is not
a new proof of source soundness or principal inference.

## 4. Edit, partition and failure cases

| Event | What the theorem permits or requires |
| --- | --- |
| Body edit; unchanged complete interface | Rebuild the affected component; reuse inference consumers satisfying all other hypotheses. Body-sensitive artifacts remain separate. |
| Changed complete interface | This theorem gives no reuse permission. A particular consumer may still be insensitive, but needs a separate proof. |
| SCC split | Solve the new components in their valid dependency order. An old internal use may now become an incoming use. Its freshening/scope behavior must be justified by the resulting joint interface and correspondence; equality of old member displays is insufficient. |
| SCC merge | Enlarge the rebuild region to contain the new complete SCC. Previously incoming uses that become internal must connect to current live roots while solving. The merged generalization must justify the same outward interface before reuse. |
| Dependency edge crosses the proposed cut | Recheck factorization and inputs; expand the region if necessary. Old SCC identifiers do not certify the new cut. |
| Changed enclosing non-generic state or dependencies | The unchanged-input premise fails even if a rendered interface is identical. Reestablish complete contextual equality or invalidate affected inference results. |
| Rebuild/generalization/transport failure | Do not publish any partial new successful result. The reuse theorem's successful-rebuild premise fails. A retained old snapshot is not certified as the new edit's inference result. |

For split/merge, `J_v` must represent the **simultaneous** export interface at
the chosen cut. It need not be the product of per-component or per-member
marginals. Relations and dependencies between exports can survive even when
the SCC partition changes. How to construct that interface is open.

The all-member visibility barrier and atomic public result are different
conditions. Member slots may be installed sequentially in an inaccessible
candidate, as F4 allows; consumers must observe complete results. The theorem
requires a consistent boundary snapshot but selects no transaction mechanism,
atomic multi-component storage operation, failure recovery policy, or physical
installation granularity. In particular, it does not copy the superseded R2
Failed/Blocked executor policy or extend F4's error behavior.

## 5. Small falsifiers of weaker comparison

These are mathematical witnesses and a pinned owner observation. None is a
new assertion about acceptance of untested raw Yulang syntax.

### Joint relationship erased by per-port printing/projection

In the pure structural grammar of Theorem S §5, take two exported endpoints:

```text
J_same(x,y) = exists a.   x=a and y=a
J_free(x,y) = exists a b. x=a and y=b.
```

Every individual endpoint projection permits every structural type in both
relations. A printer which renders only those separate projections therefore
prints identical interfaces. One joint consumer distinguishes them:

```text
H(x,y) = (x=Int and y=Function(Int,Int)).
```

`J_free and H` has a witness; `J_same and H` does not, since an atom and a
Function have different heads. Two endpoints are enough to expose a lost
sharing relation. This is not a claim that ordinary polymorphic member
schemes must share one quantified variable; it refutes any proposal which
erases a joint relationship that its own complete interface needs to retain.
Likewise, it refutes projection-only printing, not every possible complete
canonical textual serialization.

### `root_value_for` projection

At the baseline,
[the solver owner](../../crates/yu-solver/src/lib.rs) `root_value_for` maps
every `PositiveValueView::Function` to `SolvedValue::Unknown` (also mapping
Quantified, Recursive and Union to Unknown). Thus it is visibly a coarse
projection rather than a complete Function interface.

The theorem-scoped structural interfaces `Function(Int,Int)` and
`Function(Int,Function(Int,Int))` have the same root constructor, while a
consumer requiring the first interface distinguishes them by the result
head under the pure structural comparison. If both are represented as
Function predicates through that owner, its public projection is Unknown in
both cases. This establishes the missing information in the projection; no
source-to-production construction of these predicates was executed here.

### Arena identity

A bare local root index, such as index zero, can name Int in one rebuilt
arena and Function(Int,Int) in another. The above head-checking context
distinguishes them. Equality of a container arena identity also does not
identify which of its roots or export relations is compared. These are
representation-level falsifiers of using insufficient identity keys, not a
claim that the current immutable arenas mutate their referents.

An identity that names an immutable **complete** interface with matching
environment and dependency context could be a sufficient equality witness;
that stronger invariant would need proof. Fresh arena identities can also
differ for equivalent interfaces, so identity inequality alone does not prove
semantic interface change.

## 6. Remaining obligations and proposed shared-record delta

The representation gate still needs an actual complete published interface,
its generalization/instantiation semantics, scope and evidence transport,
effective canonical equality, graph/dependency cut construction, and cache
reference validity. It must establish these for the actual supported source
envelope and production observations, including general Function/effects.
No finite source graph, Theorem C containment, or Theorem S regular witness
supplies these premises automatically.

The conditional result does not choose the inference component granularity,
reverse-update algorithm, dependency representation, resource limit or cache.
It certifies no reuse of code generation, runtime behavior, source maps or
other non-inference artifacts. A body edit can change those dependencies
despite an identical generalized inference interface.

Proposed primary-owned record delta: add this artifact as a **reviewed
conditional boundary substitution result** under the existing lifecycle gate;
retain the gate as open, with complete interface construction, joint equality,
dependency/environment correspondence, and split/merge witness obligations.
At artifact freeze, `tasks/current.md`, the theorem map and the design index
were not edited.

## 7. Method, checks, budget and frozen dependencies

Method: scope-limited committed-source audit, abstract relational substitution
proof, and hand-checked two-endpoint/head-distinguishing witnesses. Only the
leased note was created. No compiler changes, checker, tests, builds,
performance experiments, children, Git mutations or approval questions.
Resource budget: one lightweight local command at a time; no parallel local
compute. Performance budget consumed: zero samples, zero measurement processes.
Verification: local Markdown file-link existence and trailing-whitespace check
on the completed note; dependency hashes computed from committed baseline
blobs. No tests, builds or measurements were run because this is a conditional
research derivation with no executable implementation change.

Direct dependency SHA-256 values (complete committed blobs, not live files):

| Dependency | SHA-256 |
| --- | --- |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-10-04-scc-intrusion-cross-edit-rebuild-addendum.md` | `e8abb68f0d1dc656e3e303a82d8b7ffb4254bb1a8be99b51ad9593c5a7b85e29` |
| `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` | `568bb4649ba278519f3ad01af2091dd1baaca42850cd19e3b5734b3c47c2eefe` |
| `notes/design/2026-10-04-source-indexed-callback-realization.md` | `76874a219ac86068027b1f08a5bc27a12d93a0169a52cebd896a6ff6f2c6b671` |
| `notes/design/2026-09-21-oracle-aligned-f4-int-scheme-scc-draft.md` | `7ec6ae3b8ea4048d0407388b23665092a121a3720f8658055dfb5e1046a09c25` |
| `crates/yu-solver/src/lib.rs` | `a2103c6735d7a4efad00231f973544dda59d42219dbf83439fffc17889168e59` |

The last two dependencies support only the scoped F4 ordering and existing
root-projection observation. The theorem is conditional on successor lifecycle
premises, not on this production owner implementing the successor. Baseline
HEAD was verified before research. Integration must recheck the semantic
dependencies if HEAD moves; unrelated commits alone do not invalidate them.

## 8. Independent review and integration status

The `compiler_referee` reviewed the full frozen note and the narrow cited
semantic sources. It found no blocking, major or minor correctness issue in
the conditional proof, SCC partition argument, lifecycle/fresh-use conditions,
or stated falsifiers. Its uninspected scope includes the full theorem-source
proofs, broader compiler call sites, production generalization/cache design,
and test execution.

The `spec_auditor` checked the full note against the design-authority rule,
redesign charter §§1–5, and Authoritative cross-edit rebuild addendum. It found
no blocking, major or minor conformance issue. It confirmed that interface
construction/equality, SCC repartition policy and transaction mechanics remain
open, and that the note adds no implementation authority. It did not certify
mathematical validity beyond scope/conformance review.

The two reviews independently agree that this is only a conditional
substitutivity result. Neither proves complete interface construction,
production soundness/principality, an effective equality test, or current
cache correctness. The lifecycle gate remains open.

Commit packet: sole leased path
`notes/progress/2026-10-05-inference-lifecycle-interface-conditional.md`;
reviewed conditional research-only status; proposed message
`research: record reviewed conditional inference lifecycle theorem`.
