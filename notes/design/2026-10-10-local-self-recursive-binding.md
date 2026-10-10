# Local self-recursive function binding

Status: Authoritative
Scope: A single local function binding referring to itself during its initializer
Approved-by: user, via `questions/2026-10-10-local-recursive-binding-scope/approved-answer.md` (q1/a1; 2026-10-10)
Approved-at: 2026-10-10
Drafted-by: primary agent
Reviewed-by: independent compiler-referee semantic review and spec-conformance review; delta findings closed
Supersedes: only the undecided recursive-local-definition boundary in
`2026-10-06-nested-block-function-source-realization-addendum.md` §3

## Selected source behavior

A single local function binding may refer to itself while its initializer is
inferred. The binder is visible in its own initializer, and all recursive
occurrences constrain one open monomorphic value root. After initializer
constraints are formed, the existing live local root and boundary remain
available for later use-time capture and freshening.

Adjacent local bindings remain sequential. This decision does not add local
mutual-recursive groups, polymorphic recursion, general value self-initializing,
or a new annotation rule. It does not change parent-copy SCC intrusion, the
selected effect-annotation policy, initializer effect evaluation, complete
Call, soundness, or required principality.

## Proposed source-to-solver seam

HIR local identity formation owns the lexical self-reference: form the local
function binder before its parameters and body, so recursive references carry
the same `HirLocalId`; keep the existing restore-and-publish boundary afterward.
The temporary self-binding is visible only while forming its own initializer.
After ordinary publication, later sibling initializers see it under the
existing sequential visibility rule; earlier siblings cannot see a future
binding.

Candidate source scheduling already allocates initializer value components
before traversal and runs initializer actions before local installation. While
the initializer is active, a recursive occurrence should link directly to
that initializer's existing open value endpoint with ordinary provenance.
It must not route through a `LocalScheme`, because local-scheme routing captures
and freshens. A nested helper initializer that refers to an active outer
recursive binder uses that same open root.

Keep `Work::Install` after intrinsic initializer actions. For an unannotated
binding, publish the existing initializer root and boundary. For an annotated
binding, retain the existing whole-initializer check and positive exposure
path. Later references continue to use ordinary local capture/freshening.
Initializer evaluation effects continue along the single existing block effect
edge.

The current implementation packet is limited to the parameterized local
function-binding form already represented by the HIR carrier. This scope note
does not reject other function-valued initializer forms or make a language
decision about them.

## Required invariants and evidence

- Recursive occurrences and the initializer share one value root and remain
  monomorphic until the initializer's intrinsic constraints are formed.
- No local scheme is visible before installation, and no recursive occurrence
  is independently captured or freshened.
- An installed local remains live for later capture/freshening, including
  bounds arriving through outer uses and parent-copy SCC intrusion.
- One-shot initializer effects, annotation value/effect scope, and existing
  sequential sibling visibility are preserved.
- Source inference is atomic at the private candidate-session boundary: if an
  initializer action fails, `CandidateInference::solve` returns no candidate
  and drops that session. A source-level retry creates a new candidate session
  from the same HIR; this design does not replay the failed action stream in
  the same session.
- Existing route transactions remain responsible for failed later captures
  and use-time freshening. They restore changes made within the failing route
  transaction to links, bounds, aliases, provenance, fresh routes, and newly
  published local slots while preserving prior slots. Intrinsic recursive
  links formed earlier in the session are baseline state; a later source-action
  failure drops the entire session as described above.
- Do not claim same-session replay for recursive Apply actions: candidate Apply
  lowering stores a `NativeInterface` in `ApplySourceInput`, and route rollback
  does not restore that payload. If same-session source-action retry becomes a
  requirement, journal that payload and nested route effects before claiming
  retryability.

Focused evidence must cover HIR identity, parameter shadowing, same-name outer
shadowing, an earlier sibling's forward-reference rejection, later sibling
resolution to the published local identity, ordinary value self-initialization
controls, same-root recursive calls, nested-helper capture, later independent
integer/Function uses, captured lower bounds, annotations, effects, route
rollback/retry, failed source-session discard and reconstruction, failed
publication, existing local polymorphism, and module recursion. Reject the
design if the direct open-root link loses a constraint needed by later
generalization, or if internal references freshen.

No local mutual-group planner, initializer freeze/saturation, early
`LocalScheme` publication, second recursive solver, or broad SCC redesign is
introduced. Exact source/runtime acceptance and the full inference-replacement
soundness/principality obligations remain open.

## Review boundary

The user's q1/a1 answer selects this source behavior, and the proposed
direct-link scheduling seam has passed independent semantic and conformance
review. The source carrier's explicit lambda-valued zero-header-parameter
forms were not part of the reviewed feasibility trace; this packet changes no
admission behavior for them.

## Implementation checkpoint (2026-10-10)

The parameterized local function form now temporarily binds its own `HirLocalId`
while forming the initializer. Candidate scheduling tracks active initializer
roots and emits ordinary `Link` actions for recursive occurrences, including
references from nested helper initializers. Installation remains after the
initializer actions; later uses retain ordinary local capture and freshening.
No source admission rule or public/default inference route changed.

Focused HIR and solver tests cover lexical identity and shadowing, sequential
visibility, direct and nested same-root recursive links, monomorphic
recursive constraints, later independent uses, annotation/effect boundaries,
and failed-session discard/reconstruction. Existing rollback, live captured
lower-bound, independent local-use and module-recursion tests were also run.
The implementation delta passed independent semantic and conformance review;
the conformance review's same-root evidence gap was repaired and delta-reviewed.
The all-target/all-feature check for `yu-hir` and `yu-solver` passed.

This closes only the reviewed parameterized local self-recursion slice in the
private candidate route. Zero-header lambda-valued initializers, local mutual
recursion, complete Call, effect hygiene, soundness/principality, public/default
migration and F5 replacement remain open.
