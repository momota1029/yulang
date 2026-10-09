# Contextual effect attachment: source/Oracle operational correspondence

Date: 2026-10-10
Successor baseline: `b69bb905983881506cdbb294805f2bdeacf77be9`; colon source update revalidated at `2a7cc93cdef1f55454814a0d0d01de7f5413c591`
Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Status: read-only source audit; candidate invariants, not an independent proof review
Scope: actual negative concrete attachment construction, contextual consumers,
four Function ports, finite admission and remaining source support
Authority: selected annotation policy and corrected callback target recorded in
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md`. The user's
later “ソレはミス” corrects the extra `int ->` in the earlier conversational
scheme; the target is `(int -> ['b, io] 'c) -> ['b] 'c`.

## Constructor, not a row-global removal flag

Frozen `annotation/constraints.rs:250–278` sets
`parameter_function_boundary=true` while constructing the parameter annotation.
The paired value connection at `:132–153` connects both annotation interfaces
with the ordinary formal row and returns the actual output predicates. The
owner is allocated as an annotation source boundary at lowerer creation
(`:14–28`), rather than inferred from a successful comparison.

For a concrete Function return effect annotation, `:424–470` constructs:

```text
t = annotation symbolic tail, or boundary-owned inner effect row
i = fresh subtraction identity
S = resolved concrete annotation set; annotation variables excluded
positive return effect = Stack(t+, PUSH_i[S])
negative return effect = Stack(t−, FILTER[S])
output predicate       = POP_i with filter S
```

The source registers the declared `(t,i,S)` stack fact before making the views.
This is not an emitted concrete lower contribution. The parameter boundary uses
its symbolic tail directly where present; a closed concrete row may share its
inner row using the source's closed-row cache, while each constructor still
allocates its own subtraction identity. `effect_row_stack` at `:657–691` has
separate wildcard, explicit-empty, variable-only and concrete branches. In the
concrete branch the collected atoms create one fresh identity. `:741–748`
excludes annotation variables from the concrete set without removing their row
connection.

The paired Function constructor (`:363–389`) is:

```text
positive = Fun(argument−, argument_effect−,
               result_effect+, NonSubtract(result+, output_predicates))
negative = Fun(argument+, argument_effect+,
               result_effect−, result−)
returned output_predicates = this Function's return-effect predicates
```

`NonSubtract` here carries contextual POP evidence at Value kind. Its name must
not be interpreted as inert metadata or a ban on ordinary effect propagation.
The negative concrete return-effect filter belongs to this source boundary;
it does not license removing the same nominal effect through every use of t.
The ordinary argument-effect construction (`:391–422`) instead supplies a fresh
row connected to the positive written effect row and shares its +/- interfaces.
Thus the nearest effect-port label alone does not select one constructor.

`lowering/signature_effect.rs:162–178,319–439` independently confirms the
negative signature return-effect inner row, fresh ID, declared stack fact and
filtered view. Signature Function lowering in `lowering/mod.rs:571–663`
reverses polarity for argument and argument effect, and retains it for result
and result effect. Its signature path is not the paired annotation API.

## Exact contextual operations and four-port consumer

Let W=(L,F,R), with left per-ID normal form POP^p PUSH^n, left filter F, and
right per-ID POP counts. Frozen `constraints/directed_weight.rs:137–176,
399–420` composes counts exactly:

```text
(p,n) ; (q,m) = (p,n-q+m)       if q <= n
              (p+q-n,m)       otherwise
```

Different IDs never cancel even when S agrees. Same-ID active families must
agree in the original directed composition. Counts remain actual counts.
`constraints/mod.rs:3566–3612` supplies these operations:

```text
left prefix:  B ; L, filter intersection, R unchanged
swap:         left POPs from R, All filter, right POPs from leading POPs of L
replay:       (L1 ; L2, F1 intersect F2, R2 ; R1), then directed mix
both-right:   left POPs from R, All filter, R unchanged
```

Swap drops active left pushes and the left filter. It is not an involution on
arbitrary contexts. Directed mix composes the right POPs into the corresponding
left words, removes exact cancellations, keeps active pushes on the left, and
moves remaining pure POPs to the right (`directed_weight.rs:12–39`).

`machine/propagate.rs:11–38` normalizes `Pos::Stack` and `Pos::NonSubtract`
by prefixing their weights onto W before comparing the inner endpoint. For
`Neg::Stack`, `:36–60` first checks the lower shape with the wrapper's filter,
clears that wrapper filter, checks the lower against the intersection of its
active push families unless that intersection is Empty, then places only its
POPs on the right suffix. Moving an entire filtered upper wrapper to W.right
would omit executable checks.

For `Fun(a,ae,re,r) <: Fun(A,AE,RE,R)` under W, `:207–271` generates:

| Port | Constraint | Context |
| --- | --- | --- |
| Argument value | A <: a | swap(W) |
| Argument effect, ordinary branch | AE <: ae | swap(W) |
| Result effect | re <: RE | W |
| Result value | r <: R | W |

The pure argument-effect branch at `:234–248` instead sends AE to the upper
return-effect target after stripping its `Neg::Stack` wrappers
(`:401–410`), under `both_from_right(W)`. It is not the ordinary ae row relation.
Current successor Value entry effects use explicit inferred entry rows and
edges into the returned row (`yu-solver/src/lib.rs:11135–11170`), so this Oracle
branch requires actual correspondence rather than literal copying of its Bot
sentinel.

## Filters are consumed at insertion and retained for future lowers

Frozen `machine/bounds.rs:3174–3210` performs lower insertion checks before
erasing the left filter from its retained replay context. Upper insertion checks
active left stacks and registers the filter on the source row before erasure.
`lower_filters` at `:3213–3255` checks all current lowers upon new registration;
`:3285–3303` checks future lower insertion against all registered filters.

Positive-shape checking (`:3305–3360`) traverses concrete registered effect
constructors, rows, unions, Stack/NonSubtract and variables. Variable checking
registers the same future-lower filter recursively. A positive Function is a
no-op for this check: it does not traverse its ports. Actual later Function
comparison, under the retained directed context, supplies latent-port work.
Consequently a Value row may consume its filter now and still carry a POP word
to a later discovered Function.

The output producer is equally concrete. `lowering/expr/tail.rs:1058–1079`
combines the defined lambda's annotation, frame and latent predicates;
`:1090–1114` wraps BOTH its body-effect and body-value endpoints. The lambda
parameter producer (`expr/lambda.rs:919–942,1244–1307`) associates predicates
with actual locals and the actual Function frame. Applying the output predicate
only to the immediate effect loses latent returned Function propagation.

## Concrete head and residual are a separate executable owner

Word cancellation does not delete nominal support. Frozen
`constraints/row_effect.rs:128–233` consumes a weighted negative effect row:
check written upper heads with the left filter; erase that filter; intersect
heads with the common active left stack set; derive retained concrete heads;
subtract those head families from the active stack family; and introduce/reuse
a residual row gamma keyed by `(source, retained families, residual weight)`.
It enqueues the unweighted head/residual row relation and then the weighted
gamma-to-original-tail relation. Future bounds on gamma participate in ordinary
replay. `:1190–1244` preserves each ID's POP/push counts while transforming the
active family to its residual set.

The compact/public support owner preserves that distinction:
`compact/collect/type_nodes.rs:83–95` passes NonSubtract into contextual
collection, whereas Stack additionally records stack-family/row coexistence;
`:404–445` merges actual concrete row items with separately collected variable
and nested support. It does not delete a concrete row item merely because its
family also occurs in a cancelled word. Generalization's live-ID collection
(`generalize/core/stack_ids.rs:79–105`) composes Function polarity, and pruning
has distinct dead/spent internal-weight rules (`core/prune.rs:606–730`). Those
Oracle pruning rules are evidence, not selected successor architecture.

## Source-derived candidate invariant and finite-owner boundary

The transitions above justify this candidate invariant: after wrapper
normalization and bound insertion, the retained bound's F is All; all effects of
the consumed F are represented by performed concrete/active-stack checks and
registered future-lower filters on its true owner. Its remaining ID/count word
and source attachment references retain their original identity and path order.
Opposite-bound replay composes those retained words; Function lifting creates
the four variance-correct children; residual consumption updates only the
particular active attachment route, while ordinary same-family contributions
remain independently reachable. This is an operational invariant schema;
the successor currently does not satisfy it because it has no contextual bound
or future-filter state.

Finite source IDs do not bound contextual counts. Oracle's same-variable
canonical omission (`machine/entry.rs:1101–1105`) occurs before enqueue; its
Var-alias bound admission (`machine/bounds.rs:4274–4317,7204–7233`) compares
positive count support only after filter erasure. Its terminal owner
(`entry.rs:1783–1816`) drops weights only for Bot/Top or nullary non-effect
constructor terminals, whose comparisons create no contextual children.

Support-shaped aliases are not a general congruence for future weighted replay:
POP_i^p and POP_i^(p+1) have identical nonzero support for p>0, but prefixing
PUSH_i^(p+1) gives an active PUSH_i in the first case and identity in the second.
This follows directly from the exact count formula. Therefore successor alias
subsumption requires an actual source-continuation restriction or an entailment
argument for all suppressed consequences. Preserving exact weights on one
retained alias does not by itself establish that argument. This audit establishes
neither global source count boundedness nor a semantic count cap.

## Successor seams and smallest truthful implementation scope

Current HIR already owns annotation owner/position, resolved nullary declaration
identity and symbolic names (`module/source_annotation.rs:31–92`); actual formal
actions retain AnnotationScope and parameter identity. It supplies no attachment
identity, output predicate/frame carrier or weighted endpoint. The paired
constructor uses shared ordinary rows and rejects explicit effects
(`candidate_effect.rs:845–866`); source preflight rejects them too
(`candidate_source.rs:77–82`). The whole-signature constructor independently
rejects negative concrete rows (`candidate_effect.rs:1135–1137`).

An executable minimal attachment cut must change the actual Value AND Effect
task/memo/bound owners together, normalize/check wrappers before identity
omission, consume/register insertion filters before one-sided replay, lift all
four Function ports, and consume concrete head/residual output. Scheme capture,
per-use reconstruction, extrusion and parent/copy SCC equality must carry those
same records and filters; equality can merge coordinates but cannot mint or
globally apply a boundary. Current `candidate_extrusion` stores only endpoints,
and `candidate_intrusion.rs:493–604` transfers endpoint bounds and replays them
after generation changes. A contextual variant cannot preserve current
unconditional equal-endpoint omission without accounting for its obligations.

This cut does not intrinsically need full Call registry, resumption or handler
runtime support: authentic negative formal construction, callback use, returned
latent Function, late concrete lower, fresh use, SCC equality and rollback can
exercise these owners in the existing private source solver. It does require
the exact finite contextual admission argument; datatypes or isolated algebra
helpers with the source refusal retained cannot be reported as completed
negative annotation integration.

At the audit baseline the exact supplied source had an additional missing producer.
`yu-syntax/src/expression/tails/colon.rs:50` emits `ColonApplicationTail` for
`run_io: cb 1`; HIR `module/local_source.rs:457–459` accepts only MlArgument and
CallTail. It has no handler form. No literal run_io occurs in the frozen Oracle
crates either; the name cannot be assumed to be a builtin handler or synthesized
from an effect annotation. A real in-scope run_io definition/import and ordinary
colon-application lowering are required before claiming its expected scheme as
an end-to-end production result. Ordinary colon application is a possible
separate source slice; it does not solve contextual termination or create a
subtraction consumer.

Concurrent upstream commit `2a7cc93c` subsequently implemented the ordinary
inline colon-application source bridge. The primary fast-forwarded to that
commit and inspected its
[delivery record](2026-10-10-colon-application-source-bridge.md). The colon
projection is therefore no longer the current blocker for the inline target.
That upstream work does not supply an intrinsic `run_io`, contravariant
attachments, contextual replay, or the expected type scheme. The solver and
pinned Oracle dependencies of this audit did not change. It is separate work,
not an implementation result of the present mathematical artifact.

## Verification and omissions

Read-only current source and pinned Oracle Git objects; seven requested notes
read. No compiler files edited, Git mutation, Cargo/build, child agent,
measurement or execution model. This note is producer mapping, not independent
review. Full Call, handler output selection/runtime, public owned scheme/import,
parameterized effects, source-cycle reachability, global finite termination,
hygiene/soundness/principality and target cutover remain unclaimed.

## Follow-up: fixed-family upward observers and their exact source boundary

Primary authorized this narrow append after the initial note was frozen. This
section concerns local source operations, not full residual/public semantics.

For nullary resolved nominal families, let n_i be an active push count and S_i
the current contextual family of ID i. `directed_weight.rs:276–282` enumerates
the family only when that entry's push count is positive. With fixed S_i, define:

```text
A(n)       = { i | n_i > 0 }
C(n)       = intersection of S_i over A(n), with intersection(empty) = All
H(n)       = written negative row heads intersect C(n)
violate_F  = exists i: n_i > 0 and S_i is not a subset of filter F
residual_E = E is a written head and exists i: n_i > 0 and E not in S_i
```

`row_effect.rs:794–815,1005–1034` supplies the exact C/H construction.
`:834–848,875–932` supplies active-stack family filtering. The formulas assume
the nullary nominal fragment, so membership introduces no additional invariant
payload constraints. At fixed families, componentwise n <= m gives
A(n) subset A(m), C(m) subset C(n), and H(m) subset H(n). Both violate_F and
residual_E are upward predicates. Their finite minimal thresholds are the unit
vectors for IDs with S_i not subset F or E not in S_i respectively. No positive
count magnitude beyond zero/nonzero is inspected by these local consumers.

In particular, for a written concrete head E, forwarding past this local head
match requires a **nonzero excluding active family**. With no active families,
C=All and E is eligible for the head. The *head-retention* observation is the
complement and is downward: adding a PUSH with family {F}, F != E changes
H={E} to H=empty. There is no unconditional “n=0 means E survives” rule.
Ordinary edges without a head consumer remain identity on concrete contributions.

This monotonicity is sufficient evidence for the observer formulas themselves.
It does not establish that the complete contextual solver is a fixed-family
monotone transition system. The actual source head consumer is not closed under
immutable active families. If H is nonempty, `row_effect.rs:175–183,1190–1217`
rebuilds each active entry with the same ID and same counts but family
S_i := S_i minus H; `:1220–1280` implements that subtraction for finite and
cofinite families. It creates/reuses gamma and splits head and residual relations
at `:185–233`. For the minimal example n_i=1, S_i={E}, written heads {E}, the
residual entry has n_i=1 and family Empty. A subsequent filter Empty accepts that
residual active family, whereas it would reject an immutable original {E}.
This is a direct local consumer discriminator. Keeping the annotation's original
S_i as immutable source authority is compatible with the source; using it as the
unchanged active residual family is not. No raw-source reachability theorem for
the discriminator is claimed.

### Compact projection observes ID presence, including unmatched POPs

The terminal negative-row projection uses a different observation.
`compact/collect/mod.rs:1019–1041` intersects the written heads with each
declared source-row subtraction fact **unless** `cancelled.contains(fact.id)`.
`poly/src/types.rs:382–384` defines contains as entry presence, not active push
presence. For a directed left word, this yields P_i = (p_i>0 or n_i>0), where
p_i is its leading unmatched POP count. With fixed declared facts, exact local
head projection is:

```text
projected_head_E = E in written heads
                  and for every declared fact f:
                      P_id(f) or E in family(f)
```

With one ID this is a single-ID OR of presence and fixed family membership.
With multiple IDs it is a conjunction of those per-fact ORs. If several facts
have one ID, their family-membership predicates can be grouped by conjunction
under the same presence predicate. This result concerns this method's projected
head only, not all output support, row-tail projection or generalization.

Minimal discriminator: give source row r one declared fact (i,{F}), F != E,
and project written heads {E}. For cancelled=empty, the fact is applied and the
projected head E is absent. For cancelled=POP_i, contains(i)=true, the fact is
skipped and projected E is present. Both words have saturated active-depth zero.
Hence active depth alone cannot implement this actual terminal observer. The
exact word/pending-POP component must remain observable. This is a method-input
source discriminator; its complete source program reachability is not asserted.

On the two-coordinate one-ID normal form (p_i,n_i), P_i is upward, and the local
projection formula is upward at fixed facts. On active depth alone it is not
even a well-defined predicate. Exact composition/swapping/mixing need their own
proof that the chosen observation domain and predecessor computation preserve
these facts; this appendix does not supply that proof.

Finally, positive concrete support is not filtered by this projection method.
`compact/collect/type_nodes.rs:261–272` retains a concrete Pos::Con row item;
`:199–224,404–445` combines actual concrete items and separately collected
variable/nested support. NonSubtract/Stack transport contexts, but a surviving
independent concrete E contribution remains an item. Therefore residual_E
cannot be substituted for the complete public “E present” observation.

Follow-up verification: pinned source inspection and scoped note diff check
only; zero models, builds, Cargo, measurements or Git mutations. Full directed
swap/mix, changing residual families, gamma splitting, source reachability and
complete public support remain outside the local upward-observer result.
