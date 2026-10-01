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
