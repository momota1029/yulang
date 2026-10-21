# R242 — Direct-Name instance closure

Status: partial constructor-level result; unreviewed. Parent, R71 and R72
remain OPEN. The direct-terminal Name base is traced below; no induction or
whole-parent closure follows.

## Fixed obligation and result

The unchanged parent is
`notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1, 6–7
(SHA-256 `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`).
For a registered Computation formal with source effect entry `e_t`, a body
Name effect `e_n`, and Lambda return effect `e_R`, the direct-terminal source
constructor emits

```text
e_t <= e_n <= e_R
e_n <= e_t.
```

For one completed Local or incoming Module FreshUse of this direct-terminal
provider, the current constructors expose a single source-derived captured
graph and one FreshUse map. The direct Name bounds are reachable from the
Function's argument-effect port, and every captured bound is restored through
that same map with physical insertion/readback. Joined to the same source
Apply's actual argument-effect, callee, result, and application-effect
endpoints as in R241, the constructor-level candidate chain is

```text
e_A <= mu(e_t) <= mu(e_n) <= mu(e_R) <= e_C <= e_out
mu(e_n) <= mu(e_t).
```

This is conditional on successful source drains, capture, FreshUse restoration,
Apply admissions and the parent's unchanged typing hypotheses. It does not yet
establish that this retained FreshUse map is the parent's `mu_i` for the exact
original provider and actual use, close the replay-use-antecedent coverage gap,
or prove R71/R72 or the forwarding induction. A same-SCC internal Module live-root route is separate:
R241 establishes its route/Apply square without a FreshUse map; it is not
silently treated as either graph route here.

## Source action and constructor order

For a registered Computation formal, `candidate_source` schedules
`Action::FormalNameEffect` at the resolved Name occurrence. Its executor calls
`candidate_formal_effect_equal` at slots 1 and 2, emitting both directed
constraints between the formal entry row and that exact Name effect row.
Child visits finish before the Lambda action. `admit_lambda_fact` then drains
slot 4 (`body_effect <= returned`) before constructing the positive Function
and draining slot 2 (`Function <= root`). The Computation formal omits slot 3.
Thus, for a body that is exactly its registered Name, the three original
constraints above have completed before the provider Function root is
exposed.

`candidate_context_seed` creates a relation and pushes an Origin even when
`references.checking` has no event for that occurrence: in that case its
source set is absent, not its relation. `start_typed_drain` attaches a
`SourceDrainReceipt` to that exact relation/occurrence after enqueue succeeds;
the completion is recorded only after the drain and its replay acknowledgments
finish. Therefore the absence of an Apply checking event at Lambda slot 4 does
not imply the absence of its receipt. If completion evidence cannot be
retained, the capture helper excludes it; this result assumes the observed
successful completion path.

## Direct-Name capture and one-use map

The provider's positive Function shape contains its argument-effect row `e_t`
and return-effect row `e_R`. In the direct Name base, all three source rows are
at the Lambda/formal level. `candidate_apply_effect` stores an equal-level
row comparison on its lower row as a negative upper edge. The two formal/Name
comparisons therefore give `e_t` an upper edge to `e_n` and `e_n` an upper
edge to `e_t`; slot 4 gives `e_n` an upper edge to `e_R`. Starting capture at
the Function shape reaches `e_t`, then `e_n`, then `e_R`, so the original
required bounds enter the graph without relying on reverse-owner discovery.
`Capture::bound` retains each exact physical key, relation and evidence.

For an incoming Module use, source schedules complete before
`route_candidate_graph` captures and instantiates the provider graph. For a
retained Local use, publication follows initializer completion; the later
`Action::Local` enters `route_candidate_local_run`, captures that local's root,
boundary and frontier, then creates one `FreshUse`. These paths remain
separate. In both, `prepare_candidate_fresh_use` builds one canonical row map
for the graph. Each `Graph::Bound` maps both endpoints through that same map;
when a relation exists, restoration creates the FreshUse child for that mapped
pair, imports its captured evidence and records the use identity. Successful
restoration inserts the physical bound and checks the constructor readback.
No equality of endpoints, `RelationId`, or route position alone is used as the
map.

For the direct-terminal body, this establishes the mapped inequalities from
the reached original bounds. The Apply join is the same-occurrence join from
R241: its retained Apply record authenticates the callee, actual argument,
argument-effect, result and application-effect endpoints; typed Function
dispatch compares the provider ports against that Apply's demand, and the
Apply effect admissions connect the callee computation effect and invocation
effect to that same application effect. This yields the displayed chain for
one constructor route under the stated successful-admission premises.

## Boundaries and falsifiers

The historical R187 bridge/relay construction is not a direct-terminal
provider body: its relay body is an Apply and its suffix has additional
intermediate owners. R187's suggestion that slot 4 cannot receive a completion
receipt merely because its occurrence has no Apply checking event is refuted by
the seed/receipt path above. That does not adjudicate R187's full emitted-fiber
table or its candidate model: in particular, it does not establish capture of
every intermediate Apply-effect edge in that relay. Keep that candidate and
its source/native qualification open and separate.

R239 remains conditional on a needed bound having entered the exact provider
graph and records `ReplayUseAntecedentsNotRetained` plus unresolved source to
original-provider/use correspondence. This audit supplies the direct-terminal
bound reachability route, but not the original theorem's authentic per-use
correspondence for every `mu_i`, arbitrary chain, repetition, simultaneous entry,
shared assignment, or native behavior. R71 and R72 remain OPEN. No production,
implementation, test, build, sample, or semantic claim is made.

Contract and byte pins: `tasks/agent-loop/sprints/simple-sub-direct-name-instance-closure-20261021-r242.md`.
No code was changed. No tests, builds or samples were run.
