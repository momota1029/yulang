# Paired native Function-port hygiene: exact equations and operational limit

Date: 2026-10-15
Status: frozen research-only proposed reversible experiment; conditional algebraic derivation; independent review pending
Baseline: `9dc31c86294189e2e0929722f39d0d2b50ba0cc0`, `research/simple-sub-intrusion`
Lease: this file only; constructive leaf; no compiler/tests/shared records/Git/delegation
Parent: H1/H2/U OPEN; no production, full-Call, soundness or principality closure

## 1. Frozen claim and accepted limits

Fix original omitted formal f, its original Lambda L, registration root v,
lexical scope and seed; fix original Apply a and its complete upper demand
`U = A [Ein] -> [Eout] B`. Original sources and binders remain fixed under one
joint scoped assignment. The selected directional law adds protection only
at the upper Eout occurrence; it does not mark a provider's original lower
output or recursively add marks to Ein, B or nested Function fields.

This packet examines a new *paired* relative-context constructor at an actual
native four-port comparison reaching that U. It is not another proof of the
previous slot-2-only construction. The original all-source parent, including
independent same-family contributions, nested owners, inherited protections,
raw resumptions, recursion and future constraints, remains unchanged and OPEN.

Governing sources are inference principles §1.1; directional protection
addendum §§1–4; annotation-effect-hygiene integration §§1–5; contextual
attachment/admission §§3–4; compiler-engineering's proof-obligation economy.
The annotation integration §6 result remains RETRACTED. The primary supplied
the accepted correction that concrete effects in `cb(signal::ping())` are
subtractable independently of cb's annotation. Its retained user wording is
in the negative-formal-permission-field-law answer draft. This leaf did not
validate that approval bundle; it uses the primary's supplied decision.

The primary is currently asking whether an inner Catch should remove the
concrete provider event in `relay signal::ping`. The directional addendum §2
explicitly withholds a blanket concrete provider-event result. This note
selects neither answer. Its provider-body statements are **weight equations**,
not asserted expected Yulang results. The primary also reports that a source
CLI admission succeeded while an exact member-to-original-Eout assertion failed
on the subsequent probe. Therefore no runtime-authenticated original member
route is assumed here.

## 2. Exact native contexts and port proposal

Write a detached context value as `(left, right, filter)`. For a fresh inferred
boundary origin u, let G_u have left push count one and empty capability,
no right pops and filter All. Let P_u have left pop count one, no pushes,
no right pops and filter All. The empty active capability is `Some(empty)`,
distinct from no active family. The origin refers to the same original
L/f/a/U witness on both operations; it is not a concrete annotation grant.

Use these *existing detached operations*, whose actual implementations are
`candidate_context.rs:1646–1691`:

```text
PrefixLeft(W,C):  left = W.left odot C.left; right = C.right
SuffixRightPops(C,P): append P's leading pops to C.right
Swap(C):          left = C.right as pure pops; right = pops(C.left)
BothFromRight(C): left = C.right as pure pops; right = C.right
Replay(C,D):      mix(C.left odot D.left, D.right + C.right)
```

Filters follow the existing operations, not these abbreviated count equations:
Prefix and Replay intersect filters; Swap/Both construct their own unrestricted
result. No new filter-discharge policy is proposed.

At the actual matching Function comparison, let C be its exact retained
post-check context. Native endpoint directions are constructed together in
`lib.rs:12551–12579`. Proposed child contexts are:

| Field | Actual child | Proposed context |
| --- | --- | --- |
| Argument | upper argument <: lower argument | `Swap(C)` |
| ArgumentEffect | upper Ein <: lower Ein | `SuffixRightPops(Swap(C),P_u)` |
| ResultEffect | lower Eout <: upper Eout | `PrefixLeft(G_u,C)` |
| Result | lower result <: upper result | `C` |

An actual child-local annotation context still prefixes its inherited operation
in the existing source order, as `candidate_function_port_admit:2777–2833`
does. Its independent check cannot be silently erased by the inferred origin.
The exact placement relative to such a nonidentity child-local check requires
the existing annotation consumer's rules; this note proves only the payload-free
new-u count calculation below.

**Do not also add G_u at Apply slot 2.** This variant introduces it on the
authenticated ResultEffect child. The Apply invocation-to-result connector
retains its original identity context. Double insertion leaves an extra push.
The source may retain a pending introduction before a provider Function is
available; it need not solve the formal eagerly. The original constraints still
accumulate normally.

## 3. Constructive calculation on the two native routes

Claim class: exact finite calculation of the detached evaluator, conditional
on the specified contexts actually reaching the original ports and consumers.
For the new u projection take inherited C=identity and no pre-existing u
operation on the incoming contribution; other distinct boundary ids are
preserved pointwise. This is a local theorem premise, not a source restriction
or an assertion covering recursive reuse of u.

The proposed ArgumentEffect context evaluates to `(I,p_u)`, not `(p_u,I)`.
The ResultEffect context evaluates to `(g_u,I)`.

For an ordinary native identity or constant Lambda provider, the actual source
owner constructs the edge `Eentry <: Ereturn` in Lambda slot 3, independently
of body use (`lib.rs:11294–11355`). Its source context is identity at the
baseline, with a retained InferredEntryOrigin. Consequently, on a successfully
reached original Function comparison the argument-effect path is:

```text
argument contribution
  -- ArgumentEffect (I,p_u) --> provider entry
  -- authentic slot 3 (I,I) --> provider return
  -- ResultEffect (g_u,I) --> original upper Eout
  -- original Apply slot 2 (I,I) --> Apply output

Replay((I,p_u), I) = (I,p_u)
Replay((I,p_u), (g_u,I)) = mix(g_u,p_u) = I
```

Thus a weight-sensitive Catch consumer would see no *new u* obstruction on
that direct argument contribution. Whether that consumer instead treats direct
concrete rows by a separate source rule is explicitly outside this equation.

A provider-body effect enters provider return through the separate Lambda
slot-4 body edge. It does not traverse the ArgumentEffect edge or slot 3 merely
because it shares the returned row. Under the same successful route premises:

```text
provider body contribution -- slot 4 I --> provider return
                          -- ResultEffect (g_u,I) --> upper Eout
                          -- Apply slot 2 I --> Apply output
```

Its new-u projection is g_u. `Common(g_u)=empty` for the symbolic
weight-sensitive consumer. The equation does not decide whether a concrete
provider row receives that treatment in selected Yulang semantics.

For the proposed original receiver exit p_u, the guarded body path becomes
`g_u;p_u=I`; the already neutral argument path has a leading p_u. As in the
previous note, the latter requires its matching dynamic owner frame outside
the contribution's provenance fragment; it is not evidence of a subtraction
grant. A corresponding real source owner/frame and entry snapshot are still
required to give these labels their colored operational interpretation.

## 4. Ordering obstruction: the equation is not yet an imported hygiene proof

The correct arithmetic above is useful for a reversible experiment. It does
not establish that the imported normalized guard/pop semantics emits it.

If the proposed ArgumentEffect pop is materialized chronologically at argument
entry and the ResultEffect push at result exit, their directed path is
`p_u;g_u`. Its normal form is `(1,1)`, not identity. Oracle normalization only
reduces `g_u;p_u`, never the reverse. A frame outside the path can prevent
underflow but cannot change this noncommutative equation. Treating the pop as
an ordinary entry-time pop therefore fails to justify the pair's desired
neutrality.

The detached evaluator instead postpones a RIGHT pop: its replay formula places
that pop *after* the newly encountered left push. Exactly at this replay the
lower bound has `R1=p_u` and upper bound has `L2=g_u`. The pinned colored-core
directed-bound invariant (`directed_stack_weight_letrec_complete_ja.tex:577–585`)
requires `R1=0 or L2=0` to avoid moving an intervening right pop across a new
push. This pair does not meet that sufficient invariant. One cannot import
that source-generation proof or one-color lemma just by observing cancellation
in `evaluate_context`.

This is the exact remaining operational premise: establish a source-owned
*delayed negative entry observation* paired with this original output guard,
whose right pop is legitimately observed after the new output push, or derive
a different certified entry constructor avoiding that mixed replay. Such a
constructor may be natural, but it is a new construction to prove at the entry
owner. No chronology reversal is claimed as an existing source operation.

Blind use of BothFromRight does not resolve this. `BothFromRight(I)=I` cannot
supply the pair. If the already proposed `(I,p_u)` entry relation is replaced
by `BothFromRight(I,p_u)=(p_u,p_u)`, replay with output `(g_u,I)` yields
`mix(p_u;g_u,p_u)=p_u`, retaining an unmatched pop rather than the desired I.
The operation is defined and source-certificated for its own inferred-entry
responsibility; it must not be inserted by name to repair an unexplained edge.

## 5. Deferred original-root marker: implementer-facing retention invariant

Claim class: proposed constructor invariant for a provisional experiment,
not a characterization of the current implementation. The native retained
DirectionalIntroduction is created in `shadow_apply.rs:1497–1525` before
constraint admission and checked in `candidate_call.rs:435–517`. It knows the
original root Function demand and exact Eout. Retain that known construction
instead of rediscovering it from a solved Effect row.

1. Seed a deferred introduction on the original slot-0 Value constraint
   `(callee,U)`, identifying original L/f/a, receiver template binder, u,
   complete U, and an **upper-root cursor**. This is pending source evidence;
   it is not a guard operation applied to an arbitrary Value constructor.
2. Store it with its exact upper-bound fiber and relation, rather than in a
   canonical-row bit or unioned source set. Opposite replay transports it from
   the operand carrying that upper demand and retains the exact Replay input
   witness. Merely finding a's source in the union of both inputs is insufficient.
3. During extrusion/freshening, map the complete upper-root cursor and its
   fields through one actual operation/use map, while retaining the original
   binder and witness. `candidate_extrusion::Work::Function` reconstructs the
   four ordered fields together; `candidate_scheme` similarly reconstructs the
   captured ordered Function node. That is the owner at which to retain this
   mapping. A span of Parent rows alone does not label the root or nested field.
4. Consume this marker only when an actual Function dispatch's **upper root**
   is that mapped original U. Emit the paired AE/RE contexts with one shared u.
   Do not consume it at the first nested Function seen while following a
   selected bound, or at a child with a coincident Eout row.
5. Remove this root's pending marker from all four children after dispatch;
   the new operations are carried by AE/RE themselves. Argument and Result
   receive no newly introduced protection. Independently licensed nested
   introductions require their own authentic source marker.
6. Consumption is per exact source-qualified Function comparison fiber, not
   once globally per u. Every independently admitted provider comparison needs
   its paired operations. Replaying the same qualified fiber must not duplicate
   its push. Memoization must therefore include the pending identity or retain
   an equivalent obligation activation mechanism before endpoint omission.

These rules prevent a deferred marker from spreading by generic Value context
inheritance into nested Function fields. They are new retention/consumption
obligations at existing owners, not proof that all transports currently retain
them. The full source-to-consumer correspondence remains OPEN, particularly
where the original source probe's exact-member assertion failed.

## 6. Required falsifiers and experiment boundary

The following are adversarial checks, not additional hypotheses silently
imposed on source inference:

- Identity and constant providers with `cb(signal::ping())`: unused formal
  still forces its input at the actual native Lambda entry. Observe the exact
  slot-3 route and ensure the new-u projection cancels before relay's Catch.
- Provider-body `signal::ping()` with pure argument: observe the distinct
  slot-4 route and g_u count, while leaving its concrete handling expectation
  pending the user's decision.
- A contribution already carrying g_v from a distinct original owner: the
  pair must remove only its newly introduced u. The per-id equation retains
  g_v. Equal families and equal rows must not identify u and v.
- Recursive or re-entered original owner using the same static template:
  runtime activation/binder substitution must distinguish the applicable
  instance, or justify shared counts. A pop tied merely to a static Lambda
  name can cancel an earlier live owner's obligation. No all-source identity
  theorem for this case is supplied here.
- A nested known Function in A or B: the outer marker must be consumed only
  at its root and absent from children. A nested own omission supplies a new
  marker; inherited protection remains independent.
- A provider with no authentic native inferred-entry connector: an unmatched
  negative pop cannot be treated as permission or evidence of forced argument
  delivery. Keep the actual entry/Call constraints and diagnose the route;
  do not invent a connector from a successful Function comparison.
- A same-family arm computation outside the scrutinee cut, and a distinct
  residual lineage: neither disappears because the callback contribution is
  guarded, neutralized or consumed elsewhere.

The smallest experiment can attach these provisional typed operations only at
the authenticated top Function comparison, retain full context trees and
original sources, and inspect the two ordinary Lambda paths. It can falsify
the proposed native realization without adopting a durable representation.
It cannot settle the unproved delayed-pop operational bridge, the user-pending
concrete provider case, all-path transport, soundness or principality.

Proof-obligation economy: original entry/output preservation is A/B. Root and
field reconstruction from solved rows would be D; retaining their actual
constructor mapping avoids that debt. The remaining right-pop ordering law is
genuinely semantic, not discharged by another context classifier or probe.

## 7. Verification, runtime and commit packet

One bounded static leaf, 12-minute budget. Reads used `rg`, bounded `sed`,
pinned Oracle `git show`, hashes and narrow Git status. No builds/tests,
executable probes, network, delegated jobs or Git mutations. CPU/RAM unmeasured;
zero heavy processes and measurement samples. Requested Sol/high; observed
model/effort unknown. Current prover role pins neither setting; configured
defaults are Sol/high. This file is the only write; prior slot-2-only note is
unchanged and frozen for its independent review.

Frozen dependency SHA-256:

```text
6301ca80eec137df3f2c2c44e2edaa7dbdf1ed7a78c69617228888e63654e461  crates/yu-solver/src/candidate_context.rs
cc5778b936a5495182c08d4853ab9ef006d079df5e169dd94df629c2d82f3199  crates/yu-solver/src/candidate_call.rs
32a6d875b9e89af8192cf017fbeccc95e9648223490d72de64a6957c97aa6e1b  crates/yu-solver/src/candidate_source.rs
831dc28b977a5e01e6f0ef0faa795495d78ecb2cc01678db48e9cf7ea5132eac  crates/yu-solver/src/shadow_apply.rs
e902da1c9a7f0fb4dcd806c87563d1ae46d35bbb999e69b7fee51c3c0f6e4bf5  crates/yu-solver/src/lib.rs
b73bcf9baa65c3e8c3093bb8ff6fa0e303fedb3baae35dc4587b70679991efee  crates/yu-solver/src/candidate_extrusion.rs
c8ef7cc472f0dcb60d793c6f9b4f6ba1aefb76f919ff2a3ce9310f85eb647dcd  crates/yu-solver/src/candidate_scheme.rs
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  notes/design/2026-10-10-contextual-attachment-admission-design.md
6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7  notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
efd3752a40143f42e53dfa377d2420e0f9213ef1b58abb4649431f59f3de66ab  questions/2026-10-13-negative-formal-permission-field-law/answer-draft.md
efed007a3848c94f9d8925985f66e76ab86082dcb094c7ec3851b2bdd7082843  Oracle@a58eefc31:research/effect-mini-language/directed_stack_weight_letrec_complete_ja.tex
```

Commit packet: exact leased path is this file; baseline
`9dc31c86294189e2e0929722f39d0d2b50ba0cc0`; independent review pending;
no dependency edits intended. Proposed checkpoint message:
`research: derive paired Function-port contexts and isolate pop ordering`.
Shared-record deltas left to primary/curator: record the paired equations,
their top-root retention invariant, and the precise delayed-negative-pop
operational premise; keep user-pending concrete outcomes and H1/H2/U OPEN.
Next action: independently assess this paired-entry ordering law against the
actual source-owned entry mechanism before assigning a durable implementation.
