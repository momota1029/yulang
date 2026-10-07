# Round 3: exact self-initialization closure and remaining initialization cuts

Date: 2026-10-07
Baseline: `6fb5d7f697d5d592e0a39532ddb4967b54e18090`
Status: independently compiler-referee/spec-auditor reviewed exact source closure
Producer: primary (Astra)
Production cutover: prohibited by current user instruction

## 1. Start and rule consumption

The remote was fetched and the clean branch fast-forwarded from `dcea2caf`
to the baseline above before this attack. Start inventory: 89 nodes,
194 edges; CLOSED 6, CONDITIONAL-CLOSED 17, OPEN-PROOF 46,
OPEN-SEMANTIC 19, IMPLEMENTATION-ONLY 1, and no user-decision blocker.

The integrated [q1/d1 receipt](../../questions/2026-10-07-recursive-self-initialization/receipt.md)
and all three approved bundle files were reread. The current files must
match their committed contents, and the approved answer must embed the
exact saved draft; the final integration record records those checks.
No answer file is changed. The
[governing rule](../design/2026-10-07-recursive-self-init-executable-boundary.md)
extracts only the approved exact-singleton disposition.

Before: the q1 subcase inside `REC_INIT` has an approved choice but awaits a
governing rule and proof. After the proofs SELF-ENVELOPE, SELF-NOSTART,
SELF-INFER and SELF-ADEQUACY pass independent review: that subcase is CLOSED.
`REC_INIT` as a whole remains OPEN-SEMANTIC. A separate closed subcase is
reported honestly and is not counted as reducing the old 65 OPEN nodes.

## 2. Adversarial cases

The following discriminators attack different parts of the rule. They are
proof inspections against the approved decision, not source executions or
new expected production diagnostics.

| Proposed shortcut | Exact failure |
| --- | --- |
| Reject every inferred `Never` source | Recognition premise is the q1 source shape and resolved self-edge; general `Never` is explicitly outside the approved scope. |
| Refuse type inference or replace its result with an error | F4 inference is preserved by clause 2 of the approval; the new head is execution acceptance only. |
| Execute the lookup and then reject | Violates clause 3 even if the eventual rejection reason is identical; initialization must not start. |
| Treat `Return(lookup(f))` as an inert provider | Name/Result synthesis constructs an interface/derivation, not a value at the uninitialized member. |
| Use a preallocated code address as the result | Produces a value not selected by the approved rule and bypasses exclusive boundary rejection. |
| Apply the rule to `my f x = f` | A parameter/body closure has a different source shape; REC-K's inert provider construction remains separate. |
| Apply the rule to a same-spelling Name that resolves elsewhere | Fails original binder resolution; spelling equality is insufficient. |
| Turn rejection into a `Rel_C` runtime event | Confuses input-processing rejection with ordinary typed execution observations. |

The focused structural shadow tests check original self-edge recognition and
identity retention only. They cannot prove a production implementation enforces
the boundary; the shadow keeps exact q1 recognition and enforcement pending.

## 3. Remaining initializer classification

The approved exact case does not justify treating every recursive initializer
as strict, lazy, erroneous or divergent. Partition by the *actual source
constructor reached before the first demand on an unavailable member*:

| Class | Current usable evidence | First unsupplied clause |
| --- | --- | --- |
| q1 exact singleton direct self-Name | Approved EXEC-SELF-Q1 | None for its source disposition; production enforcement is separate. |
| Selected immutable function-closure knot | Reviewed REC-K constructs actual mutually captured providers inertly | Ordinary descriptor introduction and independent root-world/member validation, already REC_DESC/INIT_WORLD. |
| Other direct Name initializer | Name lookup/result interface laws only | Source acceptance and the result of demanding the original target before it has an actual value. |
| Mixed closure/Name component | Closure constructor exists for guarded members | Whether/when an alias may consume an already constructed same-component provider, plus original publication/availability order. |
| Call/Force/effectful initializer | Complete Call and entry equations on already available providers | Which initializer is entered, with which available roots and incoming current world, before its first provider demand or effect. |
| Other value constructors with recursive fields | No blanket knot rule follows from REC-K | Exact source constructor's guardedness, field evaluation/availability and admission rule. |

This partition is a proof-search partition, not a selected new source grammar.
For any particular source, its independently governing syntax and source
interpretation must first establish which row applies. No claim is made
that all displayed example classes belong to the executable envelope.

## 4. Next minimal rule head: another-member initializer read

Fix original source scope `sigma`, one declaration group `G`, original
member `b`, and a direct initializer Name `n` resolving to `g != b` in `G`.
Assume the source independently admits this initializer and has chosen to
begin it; the q1 rejection theorem supplies neither premise. Retain a
source-semantic availability relation `A` containing actual provider values,
not code labels or scheme roots. Let `iota` be the current initialization
activation and `w` the current world under the original `xi=(nu,K,D)`.

The exact first-read head needing a source rule is:

```text
InitRead(sigma,G,b,n,g,iota,A,w;xi)
  -> InitReadOutcome(value-or-failure-or-pending,
                     A',w',retained-continuation;
                     sigma,G,b,n,g,iota,xi).
```

Every argument is necessary for a concrete branch: `g` identifies the
provider being demanded; `b,iota` retain the consuming initializer;
`A(g)` distinguishes actual availability; `w` retains shared state/imports;
the outcome must state whether execution continues, rejects, or suspends,
with any saved suffix and changed availability/world. This is a missing
source rule signature, not a proposed implementation carrier or an assumed
semantic judgment that would solve it by naming it.

**Available-target subcase.** If an independently governing ordinary Name
lookup applies and `A(g)=v`, its data lookup returns exactly `v` at the same
original target, and Result wraps it without forcing a latent provider.
It supplies no operation that chooses `g` from a different scope or creates
an initial value. This is a consequence of the existing Name/Result rule,
conditional on that rule applying to the admitted initializer, rather than
a recursive initialization scheduling theorem.

**Unavailable-target subcase.** If `g` is absent from `A`, ordinary successful
lookup has no value premise. q1 cannot reject this different source, REC-K
cannot furnish a value for a bare alias, and F4's scheme cannot furnish a
runtime value. The first missing implication is therefore the disposition
of `InitRead(...,g,...,A,...)` with `g notin dom(A)`, *after independent
inclusion and start have been established*. It is strictly smaller than
the former undifferentiated `REC_INIT` question, but remains OPEN-SEMANTIC.

No two complete Authority-consistent meanings on the same independently
admitted source are constructed here; there is no user-decision claim.
Inventing rejection or re-entry for this subcase would exceed q1.

## 5. Evidence and integration boundary

The independent `round3_compiler_referee` and `round3_spec_auditor` reviewed
the frozen governing source and this proof record against the exact approved
bundle. Both returned PASS without findings, and the primary accepted both
after both reviews completed. This proof's reviewed SHA-256 is
`71ffbd4c586fb1ba2c73e352e3f657127a8674ef0c06ed7bd1d435f0a7cae9ad`.
Subsequent changes only record review/verification and update status wording.
The approved answer is the authority for the exact choice; no new user
confirmation is needed. The [integration record](2026-10-07-successor-round3-review.md)
records bundle stability, the CLOSED `REC_INIT_SELF` subcase and unchanged
OPEN-SEMANTIC aggregate `REC_INIT`.

Other source/semantic lanes proceed independently. Closed q1 rejection does
not manufacture `CALL_TYPE`, original contribution ownership/licensing,
all-world admission, recursive membership, generalization or principality.
