# Current task: prove and implement SCC-intrusion Function inference

Updated: 2026-10-02. Branch: `research/simple-sub-intrusion`.

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
demands are checked for every reachable selection; a uniformly generic arm
is sufficient but is not mandatory by this package.

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

## Main records

- `notes/design/2026-10-02-counting-aware-row-projection.md` — exact counting-aware row elimination with bounded residual thresholds; complete invocation checking remains the source dependency.

- `notes/design/2026-10-02-operation-instance-binding-package.md` — shared operation-local witnesses, local preservation and generalization interference obligation.

- `notes/design/2026-10-02-symbolic-request-register-quotient.md` — finite equality/unary request-point quotient and uniform lifting; modular source applicability remains open.

- `notes/design/2026-10-02-parametric-open-row-presentation.md` — finite open point-row schema, exact eligible projection and positive recursion; full source interaction remains open.

- `notes/design/2026-10-02-source-result-synthesis-choice.md` — authoritative A: source result synthesis preserves known computation interfaces; explicit introduction alone adds a pure layer; result interpretation is not polymorphic.
- `notes/design/2026-10-02-typed-computation-core-elaboration.md` — reviewed constructive derivation-core translation/simulation; source consumer coherence and finite principal inference remain open.
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
