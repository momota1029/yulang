# SCC intrusion redesign charter

Status: Reviewed
Classification: research charter; replacement semantics remain unspecified
Scope: research direction for replacing Yulang3 F5 Function generalization and scheme architecture
Approved-by: none
Approved-at: none
Drafted-by: primary agent, following explicit user direction on 2026-09-29
Reviewed-by: architect, compiler_referee, spec_auditor
Reviewed-at: 2026-09-29
Supersedes: none
Research-gate disposition: withdraws the active-gate framing in the two 2026-09-29 intrusion drafts and the pure-F5 reference protocol
Implementation authority: none

## 1. User direction and correction

The user clarified on 2026-09-29 that the task is to **abolish the F5 portion**
of the type-inference design and proceed with a fresh SCC-intrusion design.
The prior research protocol incorrectly made exact F5 extrusion, Q/R,
per-member closed-scheme, ordering, and instantiation equivalence the pass
condition. That protocol is retained as a historical review record; it is no
longer the active gate.

For this research branch, F5's generalization and closed-scheme architecture
are legacy material to replace, not the semantic target. Do not require the new
design to preserve F5-specific Q/R shape, closed-scheme alpha-equivalence,
root-local numbering, or F5c resource/API contracts. Those may be recorded as
intentional differences or regression observations.

This direction does not authorize deleting code on `yulang3` or modifying
frozen `main`. The existing F5 branch remains intact as rollback and comparison
material until a replacement design is reviewed, approved, and implemented on
its own branch.

## 2. Semantic target

The semantic priority is soundness and principality before Oracle compatibility.
On 2026-09-30 the user clarified that Oracle inference-stage scheme formatting
and the phase at which a program is accepted are not successor requirements;
the compatibility target is the final acceptance capability for well-typed
programs. Meaningful source constraints must be retained when polarity-only
erasure would lose them. Use frozen Yulang2 `main` at commit `a58eefc3` as a
reference for existing behavior, but do not copy its implementation
mechanically. In particular, the audited Yulang2
`extrude_pos` / `extrude_neg` lower existing variable levels in place during
bound insertion; that code does not allocate the fresh boundary representatives
described in the 2026-09-29 sketch. The redesigned operation must be defined
from its own semantics and checked against observable Oracle behavior.

The Authoritative F4 SCC design remains in force only within its declared
Integer/resolved-Name scope. Its dependency-sink-first scheduling, open live
internal uses, and all-member visibility barrier before incoming use are
available as established infrastructure where applicable; F4 does not define
Function schemes, recursive Function bounds, or effect generalization. Its
publication wording does not require every member slot to be written in one
indivisible operation.

## 3. Research goal

Define a new type-inference architecture in which a definition SCC can be
generalized and instantiated while retaining graph sharing through an
intrusion/parent relation. The new design must state its own semantic objects
and observations before choosing data structures:

- what type constraints and polarized bound edges mean;
- which identities cross a generalization boundary and which remain local;
- how outer/non-generic variables remain shared without being captured;
- how recursive SCC sharing and productive guarded recursion are represented;
- how each incoming use receives independent substitutions while internal
  SCC uses remain open;
- when the generalized component freezes, publishes, and becomes visible;
- how failure avoids partial publication;
- which source forms and effects are in the first supported envelope.

Parent identity, polarity, boundary identity, recursive binder identity, and
handler-hygiene evidence must not be conflated without a proof. State the
soundness and principality theorem precisely, including the graph class,
boundary assumptions, and supported-input envelope. Effect-handler hygiene
remains a later gate after pure type/SCC behavior is characterized.

## 4. Research procedure

### Gate A — Oracle behavior ledger

For the smallest pure Function witnesses, record Yulang2 observable schemes,
constraints/use behavior, and recursive bounds. Fixtures include identity,
constant, shared diamond, nested polarity inversion, an enclosing non-generic
endpoint, guarded and unguarded cycles, mutually recursive definitions, and
two independent uses. Record which facts are observations and which are
inferences about the old implementation.

### Gate B — New abstract semantics

Specify an immutable finite polarized bound graph, levels/boundaries,
enclosing environment, SCC roots and uses, and the parent relation. Define
boundary closure and parent allocation independently of F5's closed-scheme
construction. State the principal-solution/soundness property and the
capture-avoidance rule for outer variables.

### Gate C — Intrusion characterization

Work the Gate A fixtures by hand or with an independent small model. Compare
the new semantics to Oracle observations, not to F5's internal representation.
For each incoming use, check fresh identity isolation and later constraints;
for internal uses, check live-root sharing. Add counterexamples before scaling
the fixture family. A finite set is characterization evidence, not by itself a
general soundness or principality proof. Before Gate D, prove the stated
theorem for the intended graph class, or narrow the supported envelope and
prove the theorem for that class. An independent semantic and specification
review must check the theorem, proof, and exact envelope before Gate D. A
failed or inconclusive proof review returns to Gate B/C; fixture agreement
alone cannot advance to representation selection.

### Gate D — Representation and resource design

Only after semantics are coherent, choose whether the generalized component
remains an SCC graph, how member roots project, and how use-site substitution
overlays work. Derive complexity from explicit graph dimensions and the
required observable output. Do not assume compact output merely because the
internal graph is shared.

### Gate E — Approval and implementation

Produce a narrow successor design that names the F5 sections/lifecycle being
superseded, intended Oracle behavior, compatibility deltas, rollback
conditions, and supported-input limits. Each limit must name the measured or
structural dimension, deterministic rejection point, and failure behavior;
inputs must not be silently truncated or partially published. Complete
independent M3 semantic, specification, and material performance review of
the successor design, then obtain explicit user approval before
implementation. Implement only on the redesign branch; keep the existing F5
branch available until a coherent replacement gate passes.

### Later gate — Method selection, roles, and implementation resolution

Method selection, role constraints, and implementation resolution are outside
the current ordinary effect/handler proof gate. They remain mandatory before
the successor semantics can be called complete or implementation-ready. Do
not begin this gate until ordinary effect and handler semantics are
sufficiently settled, unless the current proof discovers a dependency on
method selection, roles, or implementation resolution that must be handled
earlier. If such a dependency appears, record the concrete dependency and
narrow the early work to resolving it. The later gate must state the
supported source envelope and prove soundness, principality, and final
well-typed-program acceptance for the included selection/resolution behavior
before Gate E can close.

## 5. Stop conditions

Return to design if the parent relation captures an enclosing variable,
collapses meaningful polarity, merges independent uses, loses a recursive
bound, reduces final acceptance of well-typed programs in the supported
envelope, or fails the soundness/principality proof for its claimed envelope.
Differences in inference-stage formatting or acceptance phase are permitted
under the user's 2026-09-30 decision. Any other deliberate compatibility
difference needs a concrete conflict and an explicit decision rather than
being called equivalent.

Do not run the consumed F5c guarded-cycle captures. Any future resource
measurement needs a new design gate and budget based on the new representation.

## 6. Current boundary

This is a Reviewed research charter, not an implementation plan. It
records the user's direction to remove F5 as the target but does not yet define
the replacement semantics. No compiler code, F5 tests, public scheme APIs, or
frozen `main` files are authorized for deletion or modification by this
research document.

## 8. User-directed effect-semantics amendment (2026-09-30)

This section records the user's explicit decision after the charter review. It
supersedes the sentence in §3 that places effect-handler hygiene only after
pure type/SCC behavior has been characterized, and narrows the later-gate
wording in §4 as follows:

- Ordinary effect and handler semantics must be settled before the successor
  can be called complete or implementation-ready. Method selection, roles, and
  implementation resolution remain a later mandatory gate and must not begin
  before ordinary effects/handlers are sufficiently settled, unless the
  current proof demonstrates a concrete dependency.
- Frozen Oracle weight propagation and left/right routing are characterization
  evidence only. `StackWeight`, `SubtractId`, `All`, `AllExcept(...)`, and the
  routing algorithm are not presumed sound or semantically authoritative.
- Derive effect meaning from an independent declarative source semantics. If a
  weight representation is retained, define its meaning independently and prove
  each left/right transformation preserves that meaning. No weighted
  constraint may be erased, split, commuted, or transferred without a
  preservation proof.
- Counterexample search must include repeated pushes sharing one pop, nested
  frames, complete/incomplete handlers, and residual effects. If Oracle routing
  conflicts with soundness or principality, record the exact behavior dropped,
  successor rule, and final-acceptance compatibility impact.

This user-directed amendment does not select a trace/row model, establish a
routing counterexample, complete a proof, approve a representation, or authorize
compiler implementation. Those remain research obligations under the active
successor-design gate. The current status of the candidate semantics and
counterexample search is recorded in
`notes/progress/2026-09-30-intrusion-oracle-latent-effects.md`.

## 9. User-directed effect-abstraction amendment (2026-09-30)

The user clarified that exact continuation-sensitive trace support is a
semantic reference for soundness, not a mandatory precision target for
inference. The shallow one-request fixture shows Oracle effect rows can
over-approximate exact trace support; that observation alone is not a successor
principality failure.

- Do not require the successor to infer exact continuation-sensitive effects
  if doing so requires linear/affine continuation typing, usage tracking, or a
  substantially richer type system without independent language justification.
- A conservative sound effect abstraction is acceptable. State its expressive
  bounds and define principality relative to that abstraction.
- Keep exact trace semantics as the reference against which soundness is proved.
- If a coarser abstraction causes a concrete Oracle acceptance difference,
  record the exact behavior, the successor's bound/acceptance rule, and its
  final well-typed-program compatibility effect before treating the difference
  as intentional.

This amendment does not settle helper-boundary capture, provider ownership,
weight meaning, or left/right preservation. It does not authorize compiler
implementation. The active evidence and next proof step are in
`notes/progress/2026-09-30-intrusion-weight-routing-counterexample-search.md`.

## 10. User-directed typed-family constraint amendment (2026-10-01)

The user requires typed-family argument invariance to remain symbolic through
solving, residualization, generalization, fresh instantiation, and intrusion.
It must not be reconstructed only after concrete row materialization.

- A source rule that requires invariant family arguments must emit a symbolic
  obligation over the argument terms and retain its dependency/owner evidence
  while any dependent row, request, handler, residual, or scheme view remains
  live.
- Solving applies substitutions to the symbolic endpoints uniformly. It may
  discharge the formula only with retained proof/equivalence evidence when a
  later view depends on it.
- Row splitting, matching, subtraction, residualization, generalization,
  per-use freshening, and intrusion must transport the obligation and its
  ownership using the same type-identity maps as the corresponding arguments.
- This requirement does not assert that every same-head occurrence creates an
  obligation; source semantics must derive exactly which relation sites
  require it. It also does not select a final constraint representation or
  authorize compiler implementation.

The present conditional transport results and information-loss counterexample
are recorded in
`notes/progress/2026-10-01-intrusion-coarse-effect-abstraction-candidate.md`.
Source-rule derivation, actual solver/residual transitions, their solution
preservation proof, and parent-map construction remain open.

## 11. User-directed theory-economy amendment (2026-10-02)

Among sound candidates, prefer the smallest conceptually unified theory.
Soundness and principality remain mandatory; Oracle compatibility and inference
precision may be conservatively reduced when needed to retain them. The
successor should explain row splitting, filtering, handler subtraction,
callback boundaries, generalization, instantiation, and intrusion as
consequences or instances of a few source relations and common transport laws.

- Do not add a semantic construct, selector, obligation kind, or special case
  solely to fit an Oracle fixture. Require evidence that a distinction is
  fundamental to the source language before giving it a separate semantic
  role.
- Treat `Sel_s`, `Demand`, typed-family obligation objects, route evidence,
  and transport maps as candidate proof notation or implementation bookkeeping
  unless the source semantics proves that their distinctions are observable.
- Prefer deriving cases as lemmas from declarative relations; compare viable
  formulations by conceptual economy, compositionality, principality, and proof
  reuse. Keep implementation bookkeeping separate from the mathematical core
  wherever possible.
- Retain the already selected invariants: typed-family argument constraints
  remain symbolic through the full SCC lifecycle, dynamic handler visibility
  is defined by source machine behavior, and exact trace support is a
  soundness reference rather than a required inference language.

This amendment records a design preference and constrains the active research
gate; it does not select a complete effect calculus, prove the relational
candidate sound or principal, or authorize compiler implementation. The
candidate comparison and current factorization of proof vocabulary are in
`notes/design/2026-10-01-coupled-effect-interface-core-draft.md`.

## 12. User-directed finite-presentation classification (2026-10-02)

The user clarified that the successor need not guarantee a uniformly small
finite presentation for every well-typed program. Separate three cases before
calling an unresolved construction a principality or expressibility failure:

1. **Finite but unbounded.** Each finite source program has a finite principal
   presentation, while size or saturation work can grow across larger source
   inputs and has no fixed ceiling independent of their structural dimensions.
   This is an inference-resource issue, not an ill-typed result. A deterministic
   limit may report a distinct inference-complexity failure.
2. **Infinite unfolding, finite graph.** Recursive unfolding is infinite but
   its meaning admits a finite SCC, recursive-binder, or cyclic symbolic graph.
   Prefer proving and using that graph form over expanding it.
3. **Genuinely non-finite for the chosen abstraction.** Classify this only
   after a concrete counterexample shows that soundness or principality cannot
   be retained in any finite presentation of the chosen abstraction. A missing
   construction or an infinite concrete state space alone is not such a proof.

Any future inference-complexity limit must name its structural metric and
deterministic check point. Exceeding it must not be reported as a typing
failure, silently truncate constraints, or publish partial SCC results. The
particular metric and threshold belong to representation/resource design;
this amendment sets no numerical cap. SCCs and other finite cyclic graphs are
the preferred treatment for class-2 behavior where their preservation laws
can be proved.

Current evidence establishes a finite-saturation **resource component** for
pure endpoint constraints on each fixed finite input graph; it does not
establish a principal presentation even for the full pure source fragment.
The finite back-edge representation used for recursive bounds is a data
structure, not by itself a class-2 semantic result: whether its meaning is the
required regular unfolding and whether transport preserves it remain open. A
regular active-stack representation is another candidate class-2 component,
but stack words alone lose captured-environment and live-store aliasing
relevant to handler selection. That is a counterexample to the stack-only
quotient. The complete live capture/resumption graph remains unclassified:
classes 1 and 2 are candidate explanations, while class 3 is neither
established nor ruled out. The progress record
`notes/progress/2026-10-02-finite-interface-obstruction.md` tracks this
classification and its open quotient construction.

This amendment does not select a complete finite/regular quotient, set a
resource threshold, establish Oracle acceptance equivalence, or authorize
implementation. Those remain proof and representation gates.

## 13. User-selected typed-value boundary transport (2026-10-02)

The user resolved both remaining source scope choices in favor of typed-value
transport. This is a source semantic direction, not approval of a concrete
representation, proof completion, or compiler implementation.

- Capture/protection follows the corresponding source-level typed value path
  through arguments, lexical environments, stores, returns and structural
  adapters. Changing an argument route into a captured-value route must not
  let an inner handler without a contract capture the callback's effect.
- A callback's returned thunk/closure retains its boundary reference along
  the corresponding typed result path. A completed CallView does not remove
  that information while the receiver activation remains live.
- An outer effect annotation is not copied indiscriminately onto nested
  latent values. Only information belonging to the corresponding signature
  path is transported; positions without exposure/protection create no
  capture authority.
- Receiver/handler expiry disables its activation-scoped authority/protection.
  Origin, event identity, latent effects, symbolic family constraints and
  their `K,D` incidence remain.
- Define and prove one common typed-value transport relation; do not introduce
  independent argument/environment/return exception rules.

The current realization candidate and conditional theorem package are in
`notes/design/2026-10-02-typed-boundary-realization-draft.md`, §6. Existing
concrete-contract Force visibility, active-incidence preservation, ordinary
handling after expiry, and the soundness/principality priority remain binding.

## 14. User-selected outside selector extent (2026-10-02)

The user resolved the remaining selector-extent question in favor of outside
evaluation for the shallow handler. Pattern, default and guard computations
run outside the candidate handler, as do its selected operation/value arms.
The selected handler is not automatically reinstalled on raw resumption.
The source equation and reviewed control proof are in
`2026-10-02-typed-source-owner-realization.md`, §6.

Eligibility of the original body request is tested once at the actual
candidate boundary before exiting it. Ordered matching then composes with
its finish continuation by ordinary state-threaded bind in the outer context.
New requests from matching or an arm use that current outer context and their
own visibility/compatibility checks. Exhausted matching forwards the original
request, preserving its raw suffix with only the source-prescribed forwarding
wrapper. Completing that original match does not create a live capture grant
after the handler has exited.

Shallowness specifies raw-resumption reinstallation; selector evaluation
extent is recorded explicitly here so it is not left implicit in that word.
This selects the already-reviewed outside source equation. It does not
approve an inference representation, establish full source soundness or
principality, or authorize compiler implementation.

## 15. Shallow primitive and derived deep handling (2026-10-02)

The user fixed the primitive/derived boundary explicitly:

- Shallow handling is primitive. Handler selection, pattern/default/guard
  evaluation and arm execution occur outside the candidate handler.
- Deep handling is derived by explicitly reapplying a shallow handler to
  resumed computation. It is not an independent primitive handler mode.
- Implementations may recognize and optimize that derived pattern only when
  they preserve its source semantics.

The original request's typed applicability at the yielding handler boundary
is still an input to the outside selection relation. This is a fact about
that request boundary, not user computation executed under the candidate,
and not live authority for new requests produced by selection. Matching and
arm evaluation use the actual outer store and activation context; no saved
store or selected-handler activation is restored.

The derivation and optimization obligation are in ordinary-computation §5.
Explicit reapplication creates the handler occurrence and ownership required
by the source expansion, preserving typed-family constraints and value-path
evidence. It does not revive an expired occurrence, inherit a maker's capture
grant by family equality, or move selector/arm effects under that handler.
This declaration authorizes its source semantic direction, not a compiler
optimization or implementation gate.

## 16. User clarification: every function receives a computation (2026-10-02)

The user clarified the intended Oracle source semantics: every function is a
handler; an ordinary pure function forces its input at the very start of
function activation and rebinds the resulting value. Use this common
computation-receiving invocation as the source reference for the successor
proof, rather than taking force-before-invocation from emitted code as its
definition.

A value parameter is therefore entry-program sugar: receive the computation,
force it inside that same invocation, bind the resulting value, then execute
the body. A computation parameter retains the input for use by the body.
This does not require an additional wrapper invocation. A pure body does not
erase effects of its entry force, nor does entry forcing recursively demand
the returned value's latent descendants.

The common invocation boundary supplies no invented operation arms or capture
grant. Actual operation coverage, ordered shallow handling, explicit capture
contracts and corresponding typed paths retain their existing rules. Source
boundary/receipt evidence precedes entry execution; force/rebinding transports
the same origin, symbolic family constraints and dependent views. On shallow
resumption the pending entry/body suffix uses current state and the existing
owner protocol; expired boundary identities are not revived.

This records the user's intended source reference. It does not certify every
frozen implementation placement as equivalent to that reference. Moving an
entry force before invocation requires a complete preservation argument,
including receiver identity, typed receipt/visibility and divergence.
Section 17 settles argument carrier scheduling; source normalization remains
a proof gate.
The invocation expansion is specified in ordinary-computation §3 and proved
within the candidate source machine in source-computation-role §10. Compiler
implementation and optimization approval remain separate.

## 17. User clarification: whole-argument reification (2026-10-02)

The user selected A in `2026-10-02-source-call-scheduling-choice.md`, as the
source semantics intended from the original Oracle implementation:

Effectful computations are **first-class source data**. Their introduction is
inert; execution begins only at explicit receiver elimination (`Force` or
handling). Whole-argument reification follows from this introduction/elimination
distinction, not merely an interchangeable evaluation-order preference.
Executing a source-derived prefix while supposedly constructing the
computation value would already partially execute the represented computation.

- Obtain the callee, then reify the **entire argument expression** as a
  computation. No source construction prefix of that argument executes before
  receiver entry merely to produce a carrier.
- Enter the same receiver activation and apply only its statically known
  interface demand. A value parameter forces and rebinds at entry; a
  computation parameter remains retained and does not execute if unused.
- Force yields a value. A latent/thunk/function result alone does not justify
  another force. Unknown interface portions do not induce speculative demand.

This parallels handling only effects exposed by the current known interface.
Typed-value transport, activation-scoped authority, symbolic `K,D`, ordered
shallow selection and raw resumption retain their existing rules. Reification
captures lexical value references, not a snapshot of store or handler activity.

Frozen pre-entry construction and `ForceThunk` placement are characterization
evidence only. They may be lowering/optimization choices if observationally
equivalent to this source rule; unproved placements do not define the intended
Oracle semantics. This approval closes the source scheduling question, not
raw-source typing, result-role elaboration, finite principality, lifecycle
transport or compiler implementation. Those proofs must use A as their source
reference rather than infer a source rule from emitted code.

## 18. User decision: result synthesis forwards computation interfaces (2026-10-02)

The user selected A in `2026-10-02-source-result-synthesis-choice.md`:

```text
Result(Value(A))          = Comp(empty,A)
Result(Computation(E,A))  = Comp(E,A)
```

If `x : Computation(E,A)`, the result of `h(x) = x` preserves that computation
interface. Lookup, typed transport and result synthesis are inert. Synthesis
does not run `x`; execution still requires an explicit consumer (`Force`,
handling or known-interface demand).

No implicit `pure x` layer is inserted. Returning the computation itself as
ordinary data under another result layer requires explicit inert introduction
or lifting. Result interpretation is not generalized as a new public mode:
simple forwarding has one source meaning. Ordinary value/effect endpoint
polymorphism is unaffected by that exclusion.

This decision closes the result-synthesis blocker. Checking, symbolic solving,
principal effect abstraction and lifecycle proofs must derive from it; their
completion and compiler implementation are not implied by this source approval.

## 19. User correction: a generic operation arm cannot narrow its local type binder (2026-10-02)

The user explicitly rejected this source handler:

```yulang
act sink:
    our put: 'a -> ()

our ints_only(action: [sink] 'r): 'r = catch action:
    sink::put x, k ->
        my checked: int = x
        ints_only(k ())
    v -> v
```

The primary's preceding claim that this handler could be accepted when all
selected requests supplied Int was incorrect. Operation-local polymorphism
is not permission for the handler to constrain that binder to Int using its
call sites. Record this rejection as source authority; frozen acceptance or
rejection of the synthetic example has not been tested.

`ReachSel => OpCompat` remains necessary for preservation, but is not a
sufficient source arm-declaration rule. The derived checking formulation
fixes the handler's family instance, opens operation-local binders as rigid
names, checks the arm uniformly, and only then instantiates that checked
proof at the actual request's retained map. The arm cannot solve the rigid
name to Int. Captured/shared constraints remain shared; arm-local witnesses
retain their proper inner scope.

This correction does not forbid specialization of effect-family parameters,
concrete operation signatures, or using constraints explicitly provided by a
declaration. It does not alter ordered selection, shallow handling, callback
visibility, symbolic instance transport or raw-resumption rules. The complete
generic-arm inference rule, effective scoped solving and principal source
template theorem remain to be proved; implementation is not authorized.

## 20. User decision: existential request opening is essential source typing (2026-10-02)

The user selected existential request opening as an essential source typing
rule, not optional proof notation. A use instantiates the operation's
`forall beta_local` once. At an already fixed, known family instance `rho`,
the handler receives

```text
Req_p(rho) = exists beta_local.
  Packet(payload : A, raw_k : B => J, profiles/evidence,
         K,D, latent dependencies).
```

Every dependent field, including `J` when it depends on the local binder,
lies inside that package. `Pack_s` records the existing witness; it adds no
runtime box, source type syntax, execution or fresh instantiation. Elimination
opens fresh rigid names `kappa` and checks one uniform arm under the declared
interface and bounds with its captured environment fixed. A caller-private
equation `s = Int` remains jointly retained in the constraint ledger but is
not an arm-checking assumption `kappa = Int`, even when all actual calls use
Int. No `K,D` is erased or reflected into new checking authority.

The universal checking scope in operation-instance §7 follows from this
existential elimination. Its instantiation theorem is the pack/unpack proof
substitution (cut), subject to the existing primitive, store and raw-suffix
premises. Payload, continuation, profiles and dependent views travel together;
aliases and resumptions retain the same witness. Fresh proof names do not
create independently solvable instances.

Dependent returned or stored roots retain joint binder correspondence rather
than a free escaping skolem. This adds no value restriction or source escape
ban; lifecycle preservation remains a proof gate. The scoped equality kernel's
existential inference variables are distinct from hidden request binders.
This decision closes this source typing choice only; compiler implementation,
full checking completeness and lifecycle approval do not follow.
