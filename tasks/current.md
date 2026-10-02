# Current task: prove and implement SCC-intrusion Function inference

Updated: 2026-10-03. Branch: `research/simple-sub-intrusion`.

Execution state: source work resumed after the user's explicit A decision in
`2026-10-02-source-result-synthesis-choice.md`. The former result-synthesis
blocker is resolved. The full proof-and-implementation objective is unchanged.

## Objective and authority

Prove that the successor plan in `notes/design/2026-09-29-scc-intrusion-generalization-sketch.md` and `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` can preserve soundness and principality while matching Oracle's final well-typed-program capability on the supported envelope, then implement the reviewed and approved inference machine. The full objective remains active.

The redesign charter governs. F5 Function generalization is comparison/rollback material, not the target. User-approved source decisions govern their declared scope; the remaining source theory and implementation require their respective gates. No compiler implementation is authorized yet.

## User-selected invariants

- Soundness and principality outrank Oracle compatibility. A deliberate difference needs a concrete conflict, the dropped Oracle behavior, the successor behavior, and final-acceptance impact.
- Final well-typed-program acceptance matters; inference-stage scheme formatting/acceptance parity does not. Preserve meaningful source constraints; polarity-only `q` erasure is not required.
- Exact traces are a soundness reference. Do not require linear/affine continuation typing merely to infer exact trace support; define principality relative to the chosen sound effect abstraction.
- Keep typed-family constraints symbolic through solve, residualization, generalization, freshening, and intrusion. Prefer one compositional relation over site-specific selectors/obligations. Oracle weight routing is characterization evidence, not authority.
- Callback capture is receiver-activation scoped and preserved through nested transitions. Escaped closures retain latent effects, origins, symbolic `K,D`, and required runtime lineage. Fresh caller handling follows the current source relation; no persistent maker mask without an independent source principle.
- Method selection, roles, and implementation resolution are a mandatory later gate after ordinary effects/handlers settle, unless a dependency appears sooner.
- Shallow handling is primitive; selection, patterns/guards and arms execute outside the candidate. Deep behavior is explicit shallow reapplication to resumed computation; optimizations must preserve that source expansion.
- The user clarified the source reference: every function is a handler/computation receiver. An ordinary value parameter forces and rebinds its input at the start of that same activation; force-before-invocation is a separate optimization obligation.
- Computations are first-class data. Their introduction is inert; after obtaining the callee, application reifies the whole argument with no pre-entry construction prefix. Execution starts only at explicit receiver elimination/handling under the known interface; lookup, transport and latent result shape do not themselves force a computation. Charter §17 closes scheduling choice A as the originally intended source semantics.
- Result synthesis forwards known interfaces: `Result(Value(A))=Comp(empty,A)` and `Result(Computation(E,A))=Comp(E,A)`. Synthesis is inert; an additional pure result layer requires explicit introduction/lifting. Result interpretation is not polymorphic (charter §18).
- Parameter roles are syntax-directed (charter §21): omitted `x` and ordinary `x:A` use value entry, forcing/rebinding once at the same receiver activation even when unused; explicit outer `x:[_] A` / `x:[E] A` retain. Body usage, empty solved rows and latent value shapes do not change roles.

## Milestone state

| Milestone | State | Exit evidence |
|---|---|---|
| 1. Coherent ordinary computation semantics for calls, closures, `Force`, requests, callback visibility, and shallow handlers | Candidate source semantics uses the user's rule: concrete typed callback boundaries govern direct and Force-exposed request visibility; origin/identity/`K,D` remain distinct and `Force` creates no authority | Preserve this boundary rule in Milestone 2; no callback micro-cases without a counterexample |
| 2. Source-to-complete-interface adequacy/simulation | Closed for the candidate ordinary machine: exact embedding covers initial `R`, primitive source-rule images, latent future use, and typed resumptions; bind lifting separately reviewed | This proves the candidate machine embeds in its exact complete interface, not that current Yulang typing derives the candidate binder ownership or has a finite presentation |
| 3. Finite symbolic presentation | Generic finite carrier/certificate theorem and decorated-kernel typed transport, emission-context routing, and position-indexed symbolic basis reviewed; raw-source instantiation remains open | Construct source executable view decorations, close abstract refinement and uniform future interaction, and prove the intended typing/acceptance bridge before selecting the abstraction |
| 4. Generalization, fresh instantiation, SCC intrusion | Waiting on a Milestone-3 presentation | Prove lifecycle transport for that presentation, including external uses, internal SCC sharing, parent ports, and symbolic effects |
| 5. Implementation feasibility | Deferred until milestone 4 determines required surfaces | Targeted architecture/resource audit of the reviewed semantics and representation |
| 6. Implementation | Not authorized | Explicit user-approved design, completed required gates, implementation and verification |

## Milestone-3 finiteness classification

The user directed separate classification of (1) finite but unbounded principal
presentations, (2) infinite unfolding with a finite SCC/regular graph, and (3)
genuinely non-finite presentations proven by a concrete counterexample. Current
evidence now includes a finite heap carrier and principal symbolic interface
for a declared abstract safety-certificate judgment, with fixed finite
program, symbolic basis, and observations. It does not yet establish that
judgment for the complete Yulang source interface. Recursive back-edge graphs and regular stacks are candidate
representations, not yet preservation theorems. A stack-only quotient has a
candidate-machine counterexample from captured-reference aliasing and handler
selection; this does not refute richer finite relational graphs. The full
capture/resumption quotient remains unclassified, and no class-3 impossibility
result exists.

If a later representation is finite per source but unbounded across sources,
an explicitly budgeted structural metric may yield a deterministic inference-
complexity failure, never an `ill-typed` result. Its metric, threshold, check
point, no-truncation behavior, and atomic publication belong to the later
resource design gate; no numerical limit is selected now.

The exact-acceptance quotient inquiry rejects stack-only and independent marginal-store
abstractions that forget captured/caller alias incidence without an exact
selection witness. Investigate a joint rooted capture/store/continuation graph
with shared symbolic `K,D`; this is a candidate, not an established finite or
regular representation. Prove source-image closure preserving actual ordered
selection, latent/resumption future use, existential identities, and shared-`ν`
fibers, then prove least representable projection. Class 1/2/3 remain
unclassified for the complete interface, with no class-3 witness.

A conditional lower bound rules out requiring a total effective quotient
with decidable exact selected-event reachability over an envelope encoding
arbitrary Turing-machine runs: a designated event iff halt would decide the
halting problem. Frozen Yulang features make the encoding plausible, but the
candidate machine lacks recursive/list/enum typing rules, and a resource-
bounded envelope may exclude it. This does not obstruct conservative
principality and is not a class-3 result. Next derive an effective
conservative effect abstraction that retains soundness and principal
projection without requiring exact trace/event reachability. The new
`2026-10-02-finite-abstract-safety-presentation.md` constructs that generic
alternative: finite address/store graphs and a maximal safe assignment domain
with minimal joint observations. Its source refinement, finite symbolic basis,
modular future-use coverage, and acceptance bridge remain open. Possible
spurious rejections are disclosed, not approved.

## Current work

The milestone-1 candidate is `notes/design/2026-10-02-ordinary-computation-semantics-package.md`. It defines one state-threaded `Run` relation, concrete closure-frame re-entry under the current caller store/activations, latent `Force`, per-event origins and symbolic `K,D`, event-relevant ordered visibility, and shallow handler images. The user selected preservation of existing callback incidence while its receiver is active, ordinary current-handler search after escape, and concrete typed-boundary visibility for both direct and Force-exposed requests. `Force` exposes latent computation but creates no authority; origin and `K,D` remain event-specific.

The ordinary-computation package received a bundled architect/compiler-referee/spec-auditor review and a focused closure delta review. It repaired event-specific callback relevance, ordinary receiver-body handling, actual post-application `C_h` and current-boundary checks, closure re-entry, and the suspended invocation wrapper across handler unwind. The user selected concrete typed-boundary visibility for direct and Force-exposed requests; its delta review found no major issue. The exact semantic embedding has been package-reviewed: initial `R`, primitive source-rule images, latent future-use, and typed resumptions are covered; finite-resumption bind lifting was separately reviewed. Milestone 2 is closed for the candidate machine, not for the current Yulang typing relation.

For Milestone 3, the earlier conditional finite guarded-saturation theorem
and exact-acceptance route remain valid. On that route, invented selected
arms cannot be counted as actual source obligations. The new conservative
certificate package instead declares its abstract derivation judgment and
proves its principal interface. It supplies a generic finite heap construction,
not yet the complete source refinement or a selected successor acceptance
policy. Package review repaired the safety theorem's error-reflection
quantifiers; independent delta review is clean.

The source-realization package now constructs the predicate basis from a
finite monomorphic ownership/descriptor graph, with all query-schema endpoint
products retained symbolically. Its operational kernel gives conditional
heap simulation; explicit selected-pair observations give universal
selected-incompatibility reflection. Independent semantic and conformance
package reviews are clean within that conditional envelope. This does not
construct elaboration from raw source. The source gaps at that checkpoint were
inductive callback-boundary relevance/visibility and effective checking/conversion
descriptors; neither may be hidden in an oracle primitive. The typed-boundary
package now constructs at most `|T|²` recursive adapter descriptors for fixed
resolved Function/Thunk graphs, with operational simulation and a finite
symbolic label-equality variant. General source equivalence, admitted
conversions and assignment-dependent outer shapes remain open. Independent
reviews found no blocking/major issue; a minor formula-equality clarification
uses truth tables, not syntactic convergence.

The user resolved both source scope choices: typed-value transport preserves
callback boundary/protection through captured environments/store and through
corresponding latent result paths after CallView completion while the receiver
remains active. Outer annotations must not be copied to unrelated nested
positions. Charter §13 records this decision. Typed-boundary draft §6 gives
the common relational image, receiving-owner incidence, local grant/protection
query, composition/expiry laws and conditional concrete realization. Package
review repaired exact-handler expiry and retention of both actual result-view
evidence and matching callee-result evidence. A further delta review required
the typed correspondence domain to include all typed dependency paths while
restricting boundary profiles to effect paths; it also made route invariance
hold for the same tagged inputs, assignment, receipt, candidate and current
configuration. The resulting conditional theorem is clean. Persistent source
profiles are not cached handler grants. Raw-source profiles, path
correspondences and exact resumption owner mapping remain source-realization
obligations; no implementation approval has been inferred.

The user's latest instruction reaffirmed this shared transport rule. The
source theorem now states capture incidence through `Inc_C`, so its `Path`
witness includes receipt of the same typed view by the candidate owner as well
as matching `Flow` and event-specific `Observe`. This closes a wording gap
that had tied an event too narrowly to the original complete CallView. A
later latent request instead uses its own observation of the returned view
and a profile transported only along the signature's corresponding result
path; the original CallView is not kept executing. The same result follows by
relational-image composition as environment/store transport. Semantic and
conformance delta reviews found no remaining finding in this conditional
theorem. The subsequent decorated-context construction below addresses
routing and view suspension/re-entry; raw-source ownership, finite identity
correlation and source typing/acceptance remain open.

The fixed-shape adapter graph does not itself identify complete-`CallView`
execution positions. `Flow` transports value paths; `Observe` relates an
event to a currently executing view, including a force whose output is Unit.
A milestone-level control attack refuted the attempted definition by outward
request exposure. A live receiver's saved continuation can be resumed inside
its callback and install a receiver-owned handler there. The owner-span rule
borrows the still-live receiver, so receipt ownership does not imply that the
callback's outward boundary precedes that handler. Waiting for outward
exposure loses the callback protection needed for the first dispatch. The
counterexample is in the decorated candidate machine; raw-source acceptance
is not claimed. Architect and independent semantic searches agree on this
failure. It is not a non-finiteness result.

Typed-boundary §4 now proposes one correction: project every request emission
onto the marked current positions of its executing typed view context before
handler filtering. Outward support remains the handler image's separate
projection. Saved contexts retain exactly the view delimiters crossed at the
shallow capture boundary; raw resume plugs those into the resumer's current
context, with fresh execution occurrences and unchanged boundary evidence.
Executable owner borrowing does not erase the ambient callback view. A
package theorem derives this observation relation by a finite linked-frame
walk and proves control/visibility preservation for the decorated kernel.
Independent semantic/conformance package review and semantic repair closure
are clean. Review found that admission must retain the original annotation
position: `Admit_b,p,o` uses finite `Slots(b)`, preserving independently
symbolic call and returned-latent contracts under one `ν`. The original
owner-fragment proof was also scoped to include the new `View` constructor.
Routing needs no additional symbolic predicate once those positions and
profile slots are supplied. Arbitrary
source elaboration of these positions, abstract identity correlation,
uniform clients and the source typing/acceptance bridge remain open. Do not
equate the constructor-only adapter graph with those executable decorations.

The next Milestone-3 package is raw-source construction of those finite
executable typed views and original profile slots. The reviewed
`2026-10-02-source-computation-role-elaboration.md` now establishes two
obstacles to shortcuts: executing an outer computation cannot be replaced by
value adaptation to its result type when that result is itself latent; and
`Adapt(Unit,α)` can construct arbitrarily nested target positions absent from
the initial source producer inventory. Neither is a source non-finiteness
result. The common `Execute(Comp(E,A)) = Force` theorem preserves an arbitrary
result `A` without adding descendant demand; admitted result conversion is
a separate composition. It does not yet derive the role from raw syntax.

The user's source-reference clarification now supplies one invocation:
receive a computation, execute entry code, then the body. A value parameter
expands to force/rebind inside that same activation after boundary/receipt
entry. A computation parameter remains retained. Ordinary-computation §3 and
source-computation-role §10 give the expansion law, including the pending
rebind/body/return suffix on shallow resumption, typed result transport and
expiry. Operation function values use the same entry to obtain their declared
payload, then an internal constructor returns the latent request. The common
boundary invents no arms or capture grants. The prior §8 pre-call value-force
candidate is historical, not current source authority.
Semantic/conformance package review covered this user-premise delta; a missing
operation payload-acquisition clause was repaired in one documentary pass and
closed by an independent semantic reviewer. The exact-interface image table
now includes the same entry/body suffix. Full raw-source inference remains
outside that expansion theorem.

The frozen scheduling map is corrected to the public `specialize2` path;
older `solve/expr_solver` and `lib_support` locators describe alternate
machinery. Strict local `Let` executes when its containing block executes;
production can delay that whole block, including the prelude. Pure-expression
lifting can delay its code, whereas an already equivalent operation carrier
retains its operand evaluation before construction. A pure divergent producer
refutes universally moving construction inside a delay. This is a kernel
counterexample and exact emitted-code characterization, not certified source
acceptance or non-finiteness. The inference `evaluation` field records value
restriction, not an extra effect phase. Independent reviews checked the key
corrected production paths. No runtime `Ready/Susp` mechanism is adopted.

The immediate gate is source producer/annotation elaboration and its
scheduling-preserving representation **under this common invocation**.
The user closed `2026-10-02-source-call-scheduling-choice.md` with A and
clarified its first-class-data basis: computation introduction is inert,
execution requires explicit receiver elimination. The former scheduling
blocker is resolved; this is the originally intended source semantics, not
a choice inferred from frozen code. The kernel divergence discriminator
still rules out blanket prefix hoisting; complete frozen source acceptance
of the discriminator remains unverified.

Source-computation-role §12 now gives the conditional introduction/elimination
and common-call realization package: initial related computation values,
primitive forward steps, future use and raw resumption preserve current
state, typed boundary references and joint symbolic `K,D`. It adds no
automatic computation-name or result-carrier force. The exact-interface
image includes inert introduction; argument/code consumer derivation remains
a premise, not a completed raw-source theorem. The next construction must
derive explicit consumer positions and known-interface demand compositionally
from source typing, together with the existing annotation/path correspondence.
M3 semantic and conformance delta reviews found no findings in this package.
Only design/progress records changed; no compiler tests, builds or performance
experiments were run, and the measurement budget was zero.

The subsequent constructive package is
`2026-10-02-typed-computation-core-elaboration.md`. A concrete source-port
attack found that copying native operation producer code into an argument
delay returns a request carrier to a known `Int` parameter instead of `Int`.
The completed callable execution view now consumes the explicitly designated
operation interface after native return, inside the delayed argument and
its current complete view. No force comes from result shape or ordinary data
lookup. A finite declarative Value/Comp derivation now generates all core
code, including callee/argument execution, closure/operation entry, bindings,
handler guard/arm subcode and explicit consumers. Its whole-core simulation
carries initial relatedness, current state, typed paths and symbolic `K,D`
through future use and raw resumption. Static templates are `O(n+m)` in the
supplied derivation/profile size; this is not solved-type/query finiteness.
M3 semantic/conformance reviews found no major issue; the semantic review's
minor handler-subcode clarification was incorporated. The next source gate
is a coherent derivation of these ports from raw syntax/annotations/inference,
including recursive role overlap and admitted conversions. No arbitrary
executable `ArgumentCode` premise remains for the displayed core, but the
input declarative port derivation is still an explicit assumption.

The result-synthesis choice in
`2026-10-02-source-result-synthesis-choice.md` is closed by the user's explicit
A decision. Frozen evidence shows
parameter outer annotations select effect-slot policy before solving:
omitted/value annotations have pure slots; outer effectful annotations retain
their computation slot. This is evidence for source parameter derivation,
not authority to adopt Oracle routing. The user now specifies that the exact
forwarding form `h(x:[handled; 'e]'a)=x` preserves its known computation
interface. Ordinary value results get `Comp(empty,A)`; already computational
results retain `Comp(E,A)`. No implicit pure layer or generalized result
interpretation is introduced. Construction, lookup, transport and synthesis
remain inert; only explicit known-interface consumption executes code.

Typed-computation-core §6 now constructs `(I,d,n)` for ordinary source forms:
the known source interface, inert data and the derivation for explicit
consumption of `Result(I)`. Names forward their interface; functions apply
`Result` to their bodies; calls, ordinary local bindings and shallow handlers
build reified computations; explicit introduction alone adds a data layer.
Unknown callee endpoints generate Function/boundary constraints, not guessed
entry modes. The same source-tag normalization commutes with endpoint
substitution preserving declaration/path premises, including latent/recursive
value shapes and empty effect rows. The core simulation therefore applies
to these source-generated result/consumer skeletons. Independent M3 semantic
and conformance reviews found no findings in this package. General checking,
annotation resolution, adapters and principal symbolic solving remain open;
finite code generation is not their proof. No new compiler implementation is
authorized by closing the source-result choice.

The independent non-collapse argument shows why an empty effect row cannot
turn a retained pure diverging computation into entry force; similarly,
recursive solved equality cannot choose between data return and an explicit
consumer. Original paths preserve a chosen derivation but alone do not prove
the raw selection. M3 semantic/conformance decision review found no major
issue; both requested the same minor normalization of ordinary value results
to `Comp(empty,A)`, now explicit in the candidate rule. No compiler changes,
tests, builds or measurements; zero measurement budget.
Frozen force-before-call placement requires a receiver/receipt/view
preservation proof; it is not automatically authority or an established bug.
Nested effectful annotation coverage, admitted adapters and inferred roles
remain open. Then establish a solution-complete regular normalization or
finite parametric adapter/query presentation, abstract identity correlation,
uniform clients and the acceptance bridge before lifecycle/implementation.
Finite syntax templates and the earlier fixed-role skeleton prove none of
those gates. Keep latent results and symbolic family incidence intact; do not
restart callback micro-cases without a concrete blocker.

`notes/design/2026-10-02-typed-source-owner-realization.md` now has a fresh
semantic delta review. It repaired owner-span completion so a child return
continues its captured parent suffix and only the root returns to the current
resumer. The review found no blocking/major finding in this repair or the
conditional outside-image selector relation. Two minor findings were fixed:
the E/P discriminator now supplies compatible Int answer types and identity
value arms; and the prior coupled-core text saying guard effects run in the
outer context is recorded as candidate evidence, not authority. Earlier
reviewer thread-limit errors are closed for this slice; the current gate has
M3 semantic review coverage.

The user selected **outside** selector extent on 2026-10-02; charter §14
records the decision. Pattern/default/guard evaluation, matching completion
and selected arms run outside the candidate, after the original request's
eligibility test. This discharges the reviewed outside-image control proof's
extent premise. New matching/arm events have their own current-context
dispatch; completing the original match neither reactivates its expired
candidate nor transfers authority. No selector source choice remains open.

The user's follow-up made shallow handling primitive and deep handling an
explicit derived expansion (charter §15). Ordinary-computation §5 now gives
that recursive expansion and its finite-prefix/future-use law. Reapplication
surrounds execution of the raw suffix, not its already evaluated return value;
continuation uses in guards, arms and retained closures use the same wrapper.
Source owners, typed contracts and fresh handler occurrences come from the
expansion, with no inherited grant or primitive deep mode. Independent M3
semantic/conformance review is clean. The law is definitional execution
equivalence, not recursive typing/principality or implementation approval.

The further interaction gap is uniformity: a finite presentation for every
separately linked finite client does not establish one component presentation for all
admissible future clients. Close those source and modular definitions before
the source typing/acceptance bridge and lifecycle theorem.

Finite presentation need not be uniformly small; resource overflow may be a
distinct deterministic inference-complexity failure. Full-source class 1/2
remain unproved, and no class-3 counterexample is established. The old rule
making `UnknownOrigin` independently block a drop is superseded: origin
uncertainty alone cannot veto a concrete capture contract when complete
`CallView`, exact operation coverage, and active receiver-local handling are
established. Do not begin lifecycle proof against an undefined representation.

Implementation feasibility evidence is recorded in `notes/progress/2026-10-02-successor-implementation-feasibility.md`: resolved HIR lacks calls/handlers/`Force`, effect views cannot carry nonempty symbolic payloads, and runtime execution surfaces are absent. Do not prototype before the semantic carrier and required compiler surfaces are established. Use Rust for any later executable characterization; do not use Python.

## Checking normalization checkpoint

Typed-computation-core §7 now separates source introduction/consumption,
proof-only checking of the same decorated interface, and executable admitted
casts. It proves that erasing only checking labels preserves the executable
consumer/entry skeleton, actual source contracts, typed evidence, symbolic
`K,D` and future/resumed execution. Semantic inclusion remains a premise,
not a new opaque solver instruction. The finite bound covers generated code
and constraint roots, not solved query closure or principal inference.

The old `Adapt(Unit,alpha)` tower and its dual are conditional counterexamples
to the old candidate adapter's producer-only inventory, not established
source obligations. Its `FunctionMap` can execute argument conversion before
receiver receipt and therefore is not automatically justified under the
selected source semantics. Bounded frozen source evidence requires outer
computation passage/execution, Function callbacks and ordinary registered
casts; the arbitrary nested-thunk assertions inspected use manual mono
inputs. This is not an absence proof or permission to remove acceptance.

The next milestone package must derive effective relational checking/query
closure for actual source contracts and normalize required conversions to
source introduction/consumption, checking, or admitted executable casts.
Cross-role Function assignments need complete invocation contracts; payload
variance alone cannot erase different receiver entry behavior. Registered
casts remain required; method/role/impl resolution stays in its mandatory
later gate unless a concrete ordinary-effect dependency requires it sooner.
No class-3 witness, complete finite principal presentation, lifecycle gate
or compiler implementation approval follows from this checkpoint.

## Parametric open-row presentation checkpoint

`2026-10-02-parametric-open-row-presentation.md` extends the previous closed
point-row theorem to open support variables. It constructs membership
circuits for union, intersection, relative difference, head filtering and
guarded alternatives, then generates exact inclusion/equality constraints.
Global alternative derivations remain whole blocks, never independently
chosen per request. Shared family endpoints and global `K` stay fixed.

Eligible local row variables have exact finite Boolean projection; a support
witness proves it works for finite rows as well as arbitrary sets. Variables
with surviving incidence or family-argument/guard dependencies cannot be
hidden by that theorem. Monotone recursive equations from the same
zero-preserving grammar admit at most one bit increase per recursive variable
per request, hence at most `n` simultaneous symbolic rounds. Least recursive
closure and the all-solutions relation of recursive constraints are distinct.

This is a concrete finite row-schema construction, not merely a name for
semantic inclusion. Boolean projection may grow exponentially but remains
finite. It supplies no complete source acceptance, contextual Function
checking or exact shallow-handler transformer. The current grounded `PΩ`
basis does not yet cover arbitrary new client endpoints merely because a
parametric membership schema can be applied to them. The next package must
connect those symbolic requests to the joint invocation/handler interface
with typed paths, current state, original contract slots, and future/resumed
use. Full Milestones 3–6 remain open.

## Correlated symbolic-request checkpoint

`2026-10-02-symbolic-request-register-quotient.md` constructs a finite graph
and predicate inventory for a finite-control kernel retaining boundedly many
request points. Equality partitions and unary-query colors preserve their
correlation. Capped existence-of-distinct-points formulas allow every graph
edge to lift from every concrete representative at the same static
assignment, rather than merely one possibly unreachable representative.
The bound includes all old registers and all simultaneous witness variables.

The existing certificate theorem then supplies kernel-relative principal
certificates and exact designated-fault reachability. New point inputs do
not require enumeration of new ground endpoint names. This is neither a
source runtime type-comparison feature nor a complete source theorem.
Dynamic events/activations remain distinct; all source symbolic `K,D`
dependencies must still be represented. Capacity formulas are nonpointwise,
so their row variables cannot use the prior pointwise hiding theorem.

The next owning gate is the typed modular interaction abstraction: derive
finite retained-point representation for arbitrary caller/continuation
behavior, normalize complete payload/response/interface `OpCompat`, and
establish effective interpretation of the resulting symbolic predicates.
None follows merely from the finite number of source sites. No source
counterexample, class-3 obstruction, acceptance restriction, lifecycle
completion or implementation readiness is claimed.

Frozen source gives a concrete compatibility dependency: parameterless
`std::testing::assertion` has an `assert_eq` operation with independent
`'a`, `'left_eff`, and `'right_eff` signature parameters. The declaration
and recorded generic-use fixture show family equality cannot determine
payload and callback interfaces. Normalize operation-local binder ownership
and substitutions before reducing complete compatibility queries. This
does not open method/role resolution; the witness's role constraints remain
outside the current proof gate.

## Operation-instance checkpoint

`2026-10-02-operation-instance-binding-package.md` refines complete
`OpCompat` without a new source choice. Each typed operation instantiation
has one declaration map, retained across payload, response, callback
interfaces, raw suffix and symbolic `K,D`. Family equality forgets local
coordinates. Opening an arm or resuming does not reinstantiate them;
captured endpoints remain shared across all selected events. Actual arm
demands are checked for every reachable selection. Charter §19 corrects the
earlier source-acceptance claim: an operation-local generic binder cannot be
narrowed from caller instances; rigid generic-arm checking must precede
request-specific instantiation. Selected compatibility alone is insufficient.

The reviewed result is local preservation under explicit body/store/typing
premises and finite signature transport with preserved sharing. A shallow
nested-resumption attack shows why this is not a theorem of unrestricted
effectful-let generalization. No frozen acceptance of that attack was
established, and no value restriction or other acceptance change is adopted.
The lifecycle proof must preserve or safely discharge dependent witnesses.

The follow-up architecture audit can generate finite body-demand locations
structurally, but those demands still include complete invocation checking.
For a callback call, ordinary domain/result variance and row inclusion have
not been proved to preserve its actual receiver/capture contract, current
store, ordered selection and future use. The next source package must
construct this common invocation simulation and its finite symbolic closure;
an opaque `CIncl` predicate or an operation/arm Cartesian inventory does not
discharge it. Keep this as one interaction/typing package rather than
proliferating callback fixtures. Live dependencies remain exposed to the
later generalization proof.
No class-3 obstruction, milestone-4 closure or implementation approval
follows from the local theorem. M3 semantic and conformance review found
no major issue; the minor graph-work accounting clarification is closed.

## Counting-aware row projection checkpoint

`2026-10-02-counting-aware-row-projection.md` constructs exact elimination
for joined membership/counting constraints, including the request-register
quotient's restricted `AtLeast` predicates. With maximum threshold `b` and
`h` hidden rows, retained capacity queries through `b 2^h` suffice. Distinct
named aliases are treated consistently; full color partitions construct one
simultaneous witness under the same type assignment. Finite-row and arbitrary
subset interpretations have separate exact feasibility rules; no source
row-domain choice is inferred.

This closes nonpointwise hiding for unary predicates built from row
membership, named equality, family heads and independent global guards.
It does not hide live external `K,D`, solve arbitrary type predicates, or
establish a finite complete invocation interface. The principal result is
an exact projected constraint relation, not source inference principality.
Full Milestones 3–6 and the later method/role gate remain open.
M3 semantic and conformance reviews found no major issue. The minor
decidability clarification is closed: eliminating every row can leave
domain-capacity conditions, so both row interpretations need those facts
to decide satisfiability. Tests/builds/measurements were not run for this
documentary construction.

## Fixed-domain certificate comparison checkpoint

Typed-computation-core §8 constructs the first comparison subcase without
an opaque inclusion leaf: fixed admissible interactions, unchanged actual
entry/contracts/complete evidence, and weaker guarantee support bounds.
Finite paired descriptors propagate assumption/guarantee bits; assumptions,
shared writable dependencies and routing remain invariant. Global row
constraints express only the permitted guarantee implications. Original
symbolic `K,D` and complete request instances stay in place.

The input-callback counterexample rules out treating this as uniformly
covariant Function subtyping: admitting an effectful callback while keeping
the receiver's formerly pure result can fail. No source acceptance rule is
changed. The reviewed raw-resumption counterexample also prohibits using
outward effect support to bound every pre-dispatch routing observation.

The §8 theorem assumes challenge/guarantee classification and an original
certificate; it does not generate either from arbitrary source. Its actual
entry and profile-preservation proof covers future use and raw resumption within the
unchanged domain. This closes one finite comparison kernel, not Milestone 3,
general Function inclusion, lifecycle or implementation readiness.

## Source-derived invocation-port checkpoint

Typed-computation-core §9 constructs whole-carrier and complete-call ports
for the resolved ordinary core and derives interaction directions from its
call, force, request and resumption primitives. Function carrier inputs and
operation responses reverse direction; results and payloads preserve it.
Shared read/write exposure retains both obligations. Finite sign propagation
uses graph back edges; it neither unfolds recursion nor drops `K,D` based
on polarity. §8's stronger whole-challenge freeze is preserved.

The incoming computation cannot be erased from the call interface: a value
receiver with pure body can expose argument effects at entry; a retained
receiver with constant body need not expose any. The complete source call
must include its actual entry, body and designated result consumer with
their existing delimiters. Body result synthesis alone is not its closed
effect bound. This is a consequence of the selected source semantics, not
a new argument-effect generalization or annotation rule.

The semantic containment law reverses inclusion of complete admissible
challenges and preserves inclusion of their joint observations, all under
one assignment. The remaining source gate is a finite presentation of this
input-dependent invocation image and higher-order/store interaction relation.
The direction-classification premise is discharged for resolved ordinary
graphs; arbitrary inferred graph shapes, alias worlds, general Function
inclusion, principality, lifecycle and implementation remain open.

## Heap-backed future-interaction checkpoint

`2026-10-02-heap-backed-client-interactions.md` constructs a command driver
for a supplied finite template-closed signature. Complete typed packets,
saved control and client knowledge use linked heap records. Repetition,
retaining arbitrarily many handles and later reuse need no bounded-register
premise or supplied finite client code. Source authority, operation-instance
maps, current handler context and joint `K,D` remain in those packets and
contexts; the pool itself creates no authority or access to private values.

Command-prefix coverage composes with the existing finite weak-store
simulation. This yields a finite conservative carrier for the declared
signature, not an exact alias/visibility quotient. Universal error reflection
and finite command refinement remain necessary for the principal safety
certificate theorem; existentially finding a compatible packet is insufficient.

The next source gate at this checkpoint was **interface encapsulation / template
closure**: derive a finite parametric or regular representation of arbitrary
admissible client operation-local maps, original boundary profiles and their
shared dependencies. A finite set of public family rows does not provide it.
This is an applicability gap, not a class-3 nonexistence witness. No source
acceptance loss, complete Milestone-3 closure, lifecycle theorem or compiler
implementation approval follows from this command-level construction.
M3 semantic and conformance package review found no findings. Only static
document/diff checks apply; no compiler tests, builds or measurements ran.

## Parametric linking and corrected finite-program target

`2026-10-02-parametric-component-linking.md` separates the charter's
per-finite-program target from the stronger optional goal of one fixed
grounded inventory for every future caller. The next source gate now follows
finite parameterized component summaries, linked before constructing the
program-specific descriptor/query inventory. This preserves a reusable
scheme obligation; keeping source code and re-elaborating it at each use is
insufficient.

Finite graph grafting preserves shared external ports, local binder scope,
operation substitutions, profiles and `K,D`, with graph-size construction
for a supplied finite instance graph. The joint projection/linking law is
exact when hidden witnesses are truly local and every shared dependency is
exposed or bound once jointly. Neither law proves source generalization,
finite instance generation, effective query solving or principal summaries.
Abstract runtime addresses must not identify symbolic binder identities.

Immediate next task: generate complete finite source constraint templates
and prove their instance completeness/query closure for finite linked
instances. Core §9 supplies complete invocation ports; the template must
include their input-dependent obligations and joint context, not just body
result rows or an opaque compatibility predicate. Milestone 4 subsequently
must prove that actual generalization/freshening/SCC use generates the
permitted instance graphs. The full objective and implementation gate remain
unchanged; uniform grounded client coverage is no longer a mandatory detour.

The user's `ints_only` correction also removes a false source requirement:
there is no need to infer a caller-restricted scheme that legitimizes an arm
narrowing a generic operation's local `'a` to Int. That declaration is an
error. Preserve the generic arm's rigid quantifier scope in source templates;
shared/captured existentials must not become independent witnesses under each
local universal binder. The complete scoped checking/solving theorem remains
open. This correction does not remove request maps or symbolic `K,D`.

## Uniform arm checking and scoped equality checkpoint

Operation-instance package §§7–9 constructs one generic checking template
with captured/shared witnesses outside the rigid operation-local scope and
body-local witnesses inside it. A fixed, substitution-stable body proof can
be instantiated at every admissible actual request map without caller
enumeration; the request's payload, response, raw suffix and symbolic `K,D`
remain correlated. Pointwise re-elaboration at each concrete type is not
such a template.

The constructive solver fragment is scoped unification for finite acyclic
free-constructor equality conjunctions. It propagates allowed-rigid-name
sets through variable bindings and produces a principal uniform syntactic
substitution, or a contradiction in that fragment. It does not implement
subtyping, recursive/equi-recursive equality, row equality, declaration
bounds or the full inference machine. A rigid parameter is not a concrete
type tag disjoint from Int; failing a uniform equality must never produce
that runtime exclusion.

Generic arm validity removes the false need for caller-restricted local
specialization. The outstanding execution template is the complete
invocation/shallow-handler image: entry effects, callback execution,
actual ordered selection and resumed suffix effects. Valid generic arms do
not justify unconditional family subtraction. Full source generation and
scoped solving still precede lifecycle and implementation gates.

A bounded frozen audit found ordinary fresh signature variables but no
explicit generic-arm universal checking step or narrowing-rejection fixture
in the inspected owners. This is an evidence gap, not a demonstrated Oracle
acceptance conflict: no synthetic source ran. Charter §19 remains authority.
Independent M3 semantic/conformance review found no findings in the scoped
template/equality package. A primary wording clarification makes the existing
raw-suffix/store assumptions explicit: operation-map instantiation alone
does not establish the suffix's effect bound. Static diff checks only; no
compiler tests, builds or measurements ran.

## Constructed ordinary query and execution image

Source-realization §7 expands the reviewed typed-boundary/owner relations
into finite-control heap routines for a finite linked resolved ordinary
template. Exact administrative scans use queues and visited lists of
concrete job tuples, with no user code during the query. Only afterward
does weak-store abstraction apply to all instructions and auxiliary records.
This removes the supplied `Visible`/routing-routine premise for that input.

Negative visibility is preserved by instruction simulation, not by negating
a may-path result. A collision of abstract addresses cannot establish exact
identity or that a concrete query job was visited. Concrete scans terminate;
some abstract scans may loop, while finite joint-state saturation still
terminates and covers each concrete finite scan result.

Search keeps original-event applicability from the yielding boundary, then
runs patterns/guards/finish/arms outside the candidate. New events use the
current outer context. Raw suffixes retain only the prescribed owner/view
and forwarding frames. Output observations occur when requests cross their
particular port delimiter, separately from predispatch observation. The
constructed graph feeds the existing joint reachability/safety/image equations;
generic arm validity does not justify whole-family subtraction.

Remaining source gate: resolved template generation, complete scoped
type/subtype predicates and checking, and reusable parametric summary
completeness. Unknown external callable code/responses still require a
linked provider or justified interaction summary. The graph is conservative;
its source-acceptance bridge and all-source-fault coverage remain open.
The full Milestone-3/lifecycle/implementation objective is unchanged.
M3 semantic/conformance package review found no findings within this resolved
input. Static diff checks only; no tests, builds or measurements ran.

## Essential existential request opening

Charter §20 records the user's source typing decision. A declaration/use
instantiates `forall beta_local`; the handler receives one existential
request package and opens it rigidly. Payload, response, raw suffix (when
dependent), profiles and symbolic `K,D` share the retained witness. Known
family coordinates are not hidden. Uniform checking follows from existential
elimination, and application of the checked proof follows by pack/unpack cut.
No surface existential syntax, runtime box or new execution is introduced.

Caller-private instance equations remain in the joint ledger but are not
assumptions available to the generic arm. Thus all actual callers choosing
Int still cannot justify `kappa = Int`. Aliasing, resumption and dependent
return/store transport must retain the same witness correspondence. Complete
scoped inference, lifecycle and implementation gates remain open.
Independent M3 semantic/conformance delta reviews found no findings in this
source rule and its conditional substitution consequences. Static diff and
reference inspection only; no compiler changes, tests, builds or measurements.

The separate omitted-parameter question was subsequently closed by the user
on 2026-10-03 in charter §21: `my ignore x = ()` has value entry and executes
its argument before its body. Explicit outer computation annotations retain.
Frozen initialization and caller-side `ForceThunk` remain characterization;
the user's source rule, not that placement, supplies authority.

## Executable linking before joint recertification

Parametric-component-linking §7 constructs the merged code/descriptor kernel
from finite generated open templates and supplied instance/link maps.
Whole carriers, actual receiver entry, native return/result-consumer phases,
latent handle code and shared store/context/evidence survive linking. Complete
existential request packets retain one witness through aliases and raw resume.

Query lowering and heap abstraction follow linking; the existing joint
`R_link,S_link,U_link` calculation then covers a changed supplied finite
interaction domain. An earlier closed component certificate or outward row
is not reused as a certificate for newly admitted inputs. The proof covers
every actual successor and finite future-use/resumption prefix under the
supplied interaction envelope. Its principal result remains relative to the
existing abstract certificate judgment.

This removes the supplied merged executable-kernel premise for resolved
finite instances. It does not establish general Function subtyping, arbitrary
client coverage, source-template generation or complete predicate solving.
Next in Milestone 3: derive effective complete checking and source summary
generation/instance completeness. The omitted-parameter default is now fixed
by charter §21. Milestone 4 and the implementation gates remain later.
M3 semantic/conformance reviews found no blocking/major issue; the primary
closed one minor translation-layer notation issue and clarified retained
runtime descriptor dispatch. Static diff/reference checks only; no tests,
builds or measurements.

## Guarded positive closure; emitted-predicate normalization next

Core §6 now generates the outer parameter role, body binding and entry
skeleton for omitted/value and explicit outer computation annotations.
Combining this with the existing result table gives coherent source role
skeletons without body-usage inference. Typed-path/annotation checking and
all ordinary endpoint obligations remain. M3 semantic/conformance delta
reviews found no findings; primary clarified the retained typed-path premise.

The emitted-query audit narrows the earlier blanket signed-subtype gate.
Ordinary routing uses identity/activity/path and original-slot admission;
compatibility is checked after selection. Source-realization §8 separates
operational guards from positive compatibility obligations under explicit
initialization/reachability factorization premises. Other faults and generic
arm `Base` obligations remain. Supplied predicates outside this grammar are
not automatically covered.

For the fixed finite pure fragment, Boolean-labelled Horn propagation closes
one joint bound graph. AND combines premise labels; OR joins derivations.
Pointwise evaluation at one assignment commutes with closure, giving finite
termination and fair-order independence. Retaining original clauses preserves
the joint solution relation under the existing pure carrier laws. Growing
labels reschedule dependents; once-only pair memoization is insufficient.
Occurrence/profile/`K,D` identities and rigid binder blocks remain retained.

The follow-up §9 below normalizes explicit concrete capture admission and
closes the named-query row-realization subcase. Complete checking predicates
and semantic endpoint equality remain. Independent satisfiability of marginal graphs
is still insufficient. This package proves neither full SAT completeness nor
source principality; pure Function decomposition does not handle complete
effectful contracts. No class-3 obstruction or source restriction follows.
Lifecycle and implementation remain later gates. Verification uses static
diff/reference inspection; no compiler changes, tests, builds or measurements.
M3 semantic review found no findings. Conformance review found one minor
omission of the referenced variable-rule side conditions; primary restored
distinct-variable/nonvariable cases and the no-new-bound self case. No new
rule or review round was required; no blocking/major finding remains.

## Concrete admission and joint row realization

Source-realization §9 expands an original explicit concrete capture list into
family-head and invariant tuple equalities. Original slots and protection
remain; wildcard/omitted/result-only annotations do not grant capture.
Handler operation coverage is separate. Broader source annotation forms,
including open-tail capture meaning, are not resolved or rejected here.

Guarded checks, row memberships and capacity constraints are joined into
whole constraint blocks under one assignment before any eligible projection.
In the no-counting named-query fragment, all local rows can be realized on
the finite named support. A finite membership-bit matrix, constrained to
agree on coincident request points, eliminates those rows exactly. This
works for finite and arbitrary-subset interpretations, including no named
points, without domain-capacity premises. Semantic type equalities and active
checks remain residual; no independent marginal type solutions are chosen.

Admission guard replacement preserves the query machine and `R/S/U`.
Certificate case expansion/projection is separate and retains all live
dependencies and complete observations. Projection never crosses a later
rigid scope or changes a uniform source arm into per-instance elaborations.
The package does not close full source principality or permit implementation.
M3 independent semantic and conformance reviewers both found no findings in
this package. Static diff/reference checks only; no compiler changes, tests,
builds or measurements. The separate new level proposal was outside review.

Next: effective semantic equality/disequality jointly with actual checking
obligations, and a proved decomposition of complete payload/response/Function
checks. The named-row subcase is no longer an opaque realizability premise;
general annotation generation and unknown client interfaces remain open.

### Existential scope: eager checks on all derived comparisons

Charter §22 records the user's generation/comparison-time level discipline.
An existential introduced at `l` rejects comparisons/unification with types
at level `<= l`; deeper internal generic constraints may propagate. The
user clarified that transitivity eventually produces the direct comparison
with `Int`, which is checked and rejected there. The primary withdrew the
rigid-versus-flexible question: the alias sequence was not a counterexample
to checking every derived comparison. There is no pending choice on that
question, and no exit-time checker or special quantified solver is mandated.

Operation-instance §8 specifies one guarded comparison entry, with dependency
changes invalidating and requeuing affected comparisons and opposite-bound
consequences. Under exhaustive coverage, its conditional invariant ensures
every recorded comparison has current guard evidence at successful quiescence.
Two independent M3 reviewers found no findings. The theorem does not supply
complete path coverage, semantic guard sufficiency or source principality.
Its proof quantifiers and the earlier equality kernel do not prescribe a
separate rigid node or authorize narrowing an operation-local witness.

The bounded frozen audit confirms levels belong to variables, not nullary
constructors such as `Int`. Existing extrusion lowers effective variable
levels and recursively visits both bound sides. An eager escape check must
therefore follow aliases and transitive structural/bound dependencies, not
birth levels alone. This is an implementation invariant to prove, not a
refutation of eager checking or permission to adopt frozen extrusion as
successor authority. No exit-time scan is proposed.

Charter §23 records the user's variable-only level direction. Constructors
carry no head-level metadata; ordinary structural comparison decomposes them.
The earlier fresh-Function-child argument did not account for original
extrusion and is withdrawn as evidence against that algorithm.

Operation-instance §8 gives a candidate variable-level representation for the
finite acyclic free-constructor equality kernel.
`Allowed(X)={kappa | intro(kappa)<cap(X)}` represents a prefix of the live
opening stack, and intersection is minimum cap. A lexical construction now
derives these prefixes under explicit ownership/restriction premises:
preallocate shared roots in their owning context, preserve captured endpoints,
and recursively restrict unsealed outward dependencies before linking them.
Sibling opening blocks retain distinct identities; deferred comparisons retain
their lexical context. A numeric depth detached from that context is insufficient.

The cap procedure reproduces the existing allowed-set algorithm, including
binding traversal, occurs checks and restriction propagation. Its finite
binding/cap/pair measures prove termination; correspondence transfers solution
preservation and principality for uniform syntactic constructor substitutions.
Consistent name transport and increasing level relabelling preserve these
checks. Neither result is a generalization/freshening/intrusion theorem.
Uniform equality failure is not a negative semantic `Eq_nu` guard result.

The pinned original-source reread distinguishes ordered one-sided variable
bound insertion from the frozen Yulang two-sided rule used by the finite
guarded closure. Their equivalence is not assumed. Original extrusion creates
fresh low-level representatives rather than lowering original immutable
levels. The opening extension must also cover bound insertion that skips
extrusion, retaining free-witness dependencies.

Independent M3 semantic and conformance reviews closed the variable-only and
lexical-frontier delta with no blocking/major findings; one source-line locator
was corrected. Verification: static diff/reference checks and `git diff --check`;
no tests, builds or measurements. Signed solution-relation preservation is
now supplied by the separate finite extrusion package below for unscoped
assignments. Sealed packets, nonprefix contexts, generative heads, recursive
equality and lifecycle remain outside this equality theorem. No source
capability is rejected to fit the fragment; full source principality and
compiler implementation remain later gates.

The next audit found a concrete coverage gap in verbatim Simple-sub extrusion:
extrude writes source links and copied bounds directly, outside `constrain`.
The trace `kappa_l <: X_(l+1)`, then `Record{f:X} <: Y_l`, can publish
`kappa_l <: R_l` through `R.lower` while the outer retry succeeds without
visiting that bound; the negative polarity has the dual `R_l <: kappa_l`.
This contradicts the claim that wrapping only `constrain`/retry enforces §22,
not the user's level semantics. The successor must route/stage every extrusion
edge through guarded comparison; scope safety then holds conditionally on
complete replay. Operation-instance §8 and the pinned audit record this gate;
the separate relation package now addresses exact unscoped preservation.
Independent M3 semantic and conformance reviewers found no blocking/major
issues. Two minor semantic precision points (the opening is at boundary level,
and the conditional invariant needs initially certified visible edges) were
repaired without changing the claim.

### Exact extrusion relation and remaining scoped extension

`2026-10-03-staged-extrusion-solution-relation.md` gives one candidate package:
exact source-order discovery in a private heap, with unchanged snapshots and
no replay feedback, conservatively extends the original unscoped constraint
relation. Assigning each parent the original variable's value proves the
reverse projection; signed source links and structural variance prove the
forward enclosing-retry direction. Literal retained relations over original
family/evidence coordinates are preserved jointly. Variable cycles remain
graph edges, with at most two representatives per input variable in one call.
Fixed-term, deduplicated consequence-only replay preserves the relation and
terminates; this is not a termination theorem for an allocating whole solver.

The diagonal extension can depend on a witness unavailable at the destination.
A conditional greatest-type model supplies an independent uniform upper
approximation despite guard rejection, so unscoped preservation cannot alone
prove scoped completeness/principality. The bounded source audit found frozen
`never` syntax and internal Top, but no admitted source obligation establishing
that countermodel as a Yulang acceptance conflict. No guard exception or source
capability restriction is adopted. Next derive the scoped extension criterion
from uniform source checking, admissible boundary approximations and declared
interfaces, rather than treating rejected graphs as semantically unsatisfiable.
Independent M3 semantic/conformance reviewers found no findings in this
package. Static diff/reference checks passed; tests, builds and measurements
were not run. Compiler implementation, effectful checking and lifecycle
remain open.

### Relative uniform-parent construction

The staged-extrusion package now constructs a witness-independent signed
parent tuple for a fixed original strategy over a nonempty joint hidden
domain, assuming a semantic complete lattice. A raw copied-bound operator is
not necessarily monotone: opposite-sign discovery can copy `N <= Q`.
Retained source links already entail those same-variable dynamic cross-links,
so omitting only those redundant terms from the operator gives a monotone
operator while leaving the full graph intact. Uniform extensions are exactly
its pre-fixed tuples. Their least tuple passes an original-root retry whenever
any extending tuple does, for the fixed original strategy and graph.

This is a relative semantic construction, not source/inference principality
or a finite-expression theorem. No finite syntax has been constructed for
the required joins/fixed point; no non-finiteness result follows. An unchanged
hidden anchor can still invalidate exported-root scope, and arbitrary new-port
invariant/evidence relations are outside the downward-closed retry result.
Next relate this criterion to source-generated interfaces, admissible roots
and the generation-time guard. No source exception or compiler approval is
selected. M3 uses one architect, one documentary producer and two independent
semantic/conformance reviewers; both reviews found no findings. Static
diff/reference checks and `git diff --check` passed; tests, builds and
measurements budget/consumption zero. Implementation and the full objective
remain open.

### Source width and finite regular scoped projection

The next source audit found a concrete local checking obligation that eager
exact-reference extrusion cannot handle completely. Under `x:kappa` and
`f:{} -> Unit`, `f {field:x}` is uniformly typable by record width, with no
comparison involving `kappa`. Eagerly extruding that record against an
unresolved captured outer domain instead creates a forbidden witness/parent
edge. Empty-record patterns and expected-field comparison are established
frozen source evidence; the illustrative full handler program is not an
executed or accepted fixture. The exact-reference theorem remains valid;
mandatory use of that algorithm for every scoped target is retired.

`2026-10-03-scoped-structural-projection.md` constructs partial least visible
supertypes and greatest visible subtypes for finite contractive regular
Primitive/Function/mandatory-Record graphs with opaque hidden atoms. A greatest
availability fixed point over signed nodes selects a shared projection;
coinductive factorization proves its bestness. Construction uses at most `2N`
nodes and `2E` edges, including recursive cycles. Record field omission follows
ordinary width, with no forbidden witness comparison or evidence erasure.

This is an exact finite regular result for the stated structural judgment.
It does not classify the whole source effect interface or reject excluded
types. Generic witnesses remain opaque during checking; concrete proof
substitution preserves soundness, not reflection of arbitrary concrete checks.
Next extend source constraint generation and solving to select such projections
for flexible bound graphs while preserving every original invariant/effect
relation. Declared bounds, lattice constructors, effectful Function checking,
typed-family lifecycle and implementation remain open.

M3 used one architect, one bounded source explorer, one documentary producer
and two independent semantic/conformance reviewers. Both reviews found no
findings. Static source/diff/link checks and `git diff --check` passed; tests,
builds and measurements budget/consumption zero. Task/index/progress records
are synchronized for the coherent research checkpoint.

### Symbolic projection and invariant coordinates

The projection package's §6 extends the structural theorem to declared
covariant, contravariant and invariant constructor positions. Invariant
positions retain the original coordinate when a visible equivalent exists;
having both upper/lower approximations is insufficient. Three availability
bits have at most five profiles, but those bits never decide type equality.
The original symbolic family equations, witnesses and joint `K,D/Phi` remain.

For an open regular template whose holes receive shared closed regular
graphs, a finite Boolean equation system computes exact projection control
and a shared graph recipe supplies the resulting roots. Imports and their
derived projections stay correlated; profiles are not free choices. This
constructs the transformation under shape-changing inputs without claiming
to solve unknown bounds. A predicate can be recovered from projected
coordinates only when constant on projection fibers; equality generally is
not, explaining why original invariant coordinates must survive symbolically.

Next close flexible-bound satisfiability and source-generated joint solving,
including aliases/recursive feedback, without treating the five profiles as
a type model. Effectful compatibility, declared bounds and full lifecycle
remain open. M3 used one architect, one documentary producer and two
independent semantic/conformance reviewers; both found no findings. Static
diff/link checks and `git diff --check` passed. Tests, builds and measurements
budget/consumption zero; no compiler changes or implementation approval.
Task/index/progress are synchronized; the full goal remains active.

## Main records

- `notes/design/2026-10-03-scoped-structural-projection.md` — finite regular best visible comparators, invariant-coordinate support and substitution-parametric projection with closed imports; full flexible source constraints remain open.

- `notes/design/2026-10-03-staged-extrusion-solution-relation.md` — exact unscoped graph projection, signed retry, finite consequence replay and relative uniform-parent construction; source-scoped extension criterion remains open.

- `notes/design/2026-10-02-parametric-component-linking.md` — finite grafting and exact joint linking; revised per-program proof target, source summary construction still open.

- `notes/design/2026-10-02-heap-backed-client-interactions.md` — heap-backed command-driver coverage for a template-closed signature; arbitrary-client source encapsulation remains open.

- `notes/design/2026-10-02-counting-aware-row-projection.md` — exact counting-aware row elimination with bounded residual thresholds; complete invocation checking remains the source dependency.

- `notes/design/2026-10-02-operation-instance-binding-package.md` — shared operation-local witnesses, local preservation and generalization interference obligation.

- `notes/design/2026-10-02-symbolic-request-register-quotient.md` — finite equality/unary request-point quotient and uniform lifting; modular source applicability remains open.

- `notes/design/2026-10-02-parametric-open-row-presentation.md` — finite open point-row schema, exact eligible projection and positive recursion; full source interaction remains open.

- `notes/design/2026-10-02-source-result-synthesis-choice.md` — authoritative A: source result synthesis preserves known computation interfaces; explicit introduction alone adds a pure layer; result interpretation is not polymorphic.
- `notes/design/2026-10-02-typed-computation-core-elaboration.md` — constructive source translation, result coherence and fixed-domain certificate comparison; changing interaction domains and finite principal inference remain open.
- `notes/design/2026-10-02-source-call-scheduling-choice.md` — authoritative A: first-class computation introduction is inert, whole-argument reification precedes receiver elimination; conditional discriminator and exact acceptance-evidence limits retained.
- `notes/design/2026-10-02-source-computation-role-elaboration.md` — corrected active source map, producer-placement obstruction and common invocation entry expansion; raw-source scheduling/typing and finite solved/parametric presentation remain open.
- `notes/design/2026-10-02-typed-source-owner-realization.md` — reviewed owner-span/control and typed-view context construction; user-selected outside-image equation.
- `notes/design/2026-10-02-typed-boundary-realization-draft.md` — selected common typed-value transport and reviewed conditional transport/lifetime theorem package; reviewed fixed-shape cyclic adapter construction and symbolic equality; full realization open.
- `notes/design/2026-10-02-source-realization-and-symbolic-basis.md` — finite ownership inventory, conditional operational realization, selected-fault reflection, and exact remaining source definitions.
- `notes/design/2026-10-02-finite-abstract-safety-presentation.md` — reviewed generic finite carrier and principal certificate theorem; source application open.
- `notes/progress/2026-10-02-finite-interface-obstruction.md` — classification, lower bound, construction progress, and review record.
- `notes/design/2026-10-02-ordinary-computation-semantics-package.md` — current milestone-1 theorem package.
- `notes/design/2026-10-01-coupled-effect-interface-core-draft.md` — relational carrier and prior derivations.
- `notes/progress/2026-10-02-callback-scope-transition.md` — callback/escape evidence and decisions.
- `notes/progress/2026-10-02-successor-implementation-feasibility.md` — alternating feasibility audits.
- `notes/design/INDEX.md` — design status and authority map.
