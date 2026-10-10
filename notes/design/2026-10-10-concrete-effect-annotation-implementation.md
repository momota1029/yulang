# Concrete covariant annotation implementation gate

Status: Authoritative within the existing user-selected annotation policy
Scope: Private executable representation and the first source/consumer slice
Authority: user-authorized integration; annotation-effect-hygiene-integration §1, §4
Reviewed-by: architect and independent compiler-referee, 2026-10-10
Supersedes: no language contract or theorem
Implementation: private covariant concrete checks cover nested Function ports and explicit whole-binding computation rows; variable-only root tails retain direct flow through capture/freshening; source subtraction, full hygiene and public cutover remain open

This implements the [selected policy](2026-10-10-annotation-effect-hygiene-integration.md),
not a new interpretation. The first coupled slice forms actual nullary `act E;`
identities, retains complete binding annotations, checks the generated whole
binding value against the annotation, and executes covariant concrete allowance
checks through ordinary propagation and live scheme use. A declared allowance
does not manufacture an effect contribution. Symbolic annotation variables
retain their flow and current/future concrete checks.

Nominal operands come from declaration-owned module/source identity, not spelling
or value definition IDs. Allowance ownership remains its annotation position.
Keep the public TermView/Leaf algebra unchanged using private effect operands
and executable relations at ordinary effect-row Function ports. Capture,
freshening, extrusion, canonical equality and rollback preserve those relations
and identities. Unsupported declarations/annotation structure must remain
explicitly unavailable rather than be silently ignored. Nullary support is the
first implementation slice, not a permanent effect-language restriction.

Concrete atoms and contributions are distinct. Any subtraction implementation
must preserve independently attached siblings at the same nominal point. Source
contravariant subtraction remains open until actual attachment formation supplies
its genuine inputs; pending Call metadata cannot manufacture them. No registry
adoption is a prerequisite to basic annotation constraint generation.

The source below is a whole-binding boundary witness. Actual parser inspection
found no diagnostics or recoveries for this newline-separated form. The Act
declaration owns its semicolon; placing the binding on the same line produces
a root recovery and is not an admissible fixture.

```yulang
act E
my id x: int -> [E] int = x
```

Tests must validate the annotation attachment rather than infer a result-only
annotation. This gate preserves the bare parameter's Value
role. Parameterized effect comparison remains a separate genuine semantic issue;
the approved row answer does not select universal argument variance.

Verification covers resolved identity, allowed/forbidden concrete effects,
symbolic later lowers, independent boundaries/fresh uses, provider no-backflow,
equality and rollback. None proves complete Call, source hygiene, soundness,
principality or production cutover by itself.

## Annotation checking and publication owner

Elaborate a negative checking target and a positive exposed target in one shared
annotation variable/view environment at the actual body level. Check the original
body against the negative target, then publish the positive target at the binding
destination. Preserve the body's evaluation effect. An annotated binding must
not publish its original value endpoint instead of its exposed target.

A positive covariant port retains immutable annotation support (finite nominal
members plus its symbolic tail) as a structural lower operand; the negative
companion retains the allowance consumer. Annotation support is a type operand,
not an emitted contribution. Ordinary positive extrusion transports that lower
operand, while symbolic coordinates use the normal directional maps. Do not
copy unrelated upper bounds, anchor annotations at level zero, or mark rows
non-generic to compensate for incorrect publication ownership.

Focused evidence must cover exported support after positive extrusion, the
original body's checking, outside consumer constraints, correlated symbolic
tails through fresh uses and later lowers, actual source levels and rollback.
The architect confirmed this owner repair within the existing annotation
boundary contract; it introduces no new inference rule.

## Conflict ownership and replay

Forbidden concrete operands produce a feature-gated structured effect
conflict, preserving existing error occurrence/cause and Copy/Eq/Hash contracts.
Opaque operand/view handles are branded by the owning candidate; borrowed
observation validates the brand before table access. An optional annotation
handle is present only for an actual retained boundary. Ordinary bare-empty
constraints have no annotation handle. An omitted port within a real annotation
may retain the whole annotation position; it must not claim a nonexistent row.
Independent pre-write spec review confirmed this distinction.

The operand observation distinguishes an actual contribution from an annotation
support member. Resolve the latter through its retained annotation view and a
checked member index, preserving that annotation's genuine provenance. It has
no emitted-contribution instance or subtraction attachment authority. Retain
the originating support annotation and the rejecting boundary separately when
they differ; both identities participate in diagnostic deduplication. Independent
pre-write spec delta review confirmed this representation scope, without
certifying executable comparison or publication.

The existing typed memo remains the sole semantic pair authority. Retain direct
diagnostic dependency edges from actual enqueues and exact originating pairs at
bound insertion. A later opposite bound connects its actual comparison to both
the current processing pair and the retained bound's creator. Replay reachable
conflicts from the actual initial typed pair with the new occurrence/cause,
using iterative visited membership. This preserves future-lower and memo-hit
diagnostics without scanning unrelated views, disabling memoization, or adding
a second semantic completion relation. Canonical equality preserves distinct
annotation/contribution identities and genuine origin links.

Journal new direct edges, leaves and bound-origin entries; restore them together
with registry/error state on failure. Reserve before publication and maintain
nested capacity totals incrementally. The implementation review covers semantic
replay, exact API/owner conformance and materially new traversal/accounting risk;
use M3 with at most those three independent reviewers. Measurement starts at
zero; timing runs require a concrete decision.

## Practical formation and reconstruction envelope

The annotation producer validates recovery once at its boundary. Before recursive
type construction, an iterative preflight measures recursive type-expression
nesting: the root has depth one; parenthesized-inner and arrow-result construction
each add one. Syntax wrappers do not add another step, and row atom operands do
not invoke recursive type construction. Reject nesting above 128 at HIR formation
with `StructuralProjection`, before constructing or cloning the recursive
annotation. This separate measurement protects annotation construction; it is
not the existing expression-depth check. The current practical-envelope authority
permits this bounded first implementation, without making it a permanent language
restriction.

Each freshening/extrusion operation remaps an immutable view by its original
identity and the mapped symbolic tail. Support, allowance and member operands
with that same key share one reconstructed view; different mapped tails retain
distinct views. A member preserves its index and traverses its actual view-tail
dependency. This map records construction identity, not another solving memo.
Charge it and the remaining extrusion scratch immediately as capacities grow,
before nested resource samples, and release their charge after containers drop
on both success and failure. Focused checks must verify view-copy counts, tail
correlation, depth rejection and failure-path coexistence accounting.

These owner repairs were confirmed by the architect after the initial frozen
review. The [review/check record](../progress/2026-10-10-concrete-effect-initial-review.md)
records remaining implementation findings; this design does not claim they are
already repaired.

The later [implementation delivery](../progress/2026-10-10-concrete-effect-annotation-implementation.md)
records independent repair closure, 43 focused passing tests and warning-free
owning checks. It also records the separate default-parser stack gap; dedicated
deep-fixture workers verify HIR's parsed-artifact contract only. No complete
Call, source subtraction, general soundness/principality or F5 cutover is inferred.
