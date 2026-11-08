# T1: non-singleton intervals, normalization and state obligations

Status: proof implementation plan, 2026-11-08. No language-semantics decision.
Base: integration/m1-final at e65ad7b21.

## Data and independent judgments

Retain Astra's finite `Ty` endpoint syntax and its unbounded unary constructor
spines. A normalized interval is either an unreduced endpoint pair, or a
shared constructor containing another normalized interval. An independent
`Normalizes lo hi result` judgment performs only the spec 6.5 same-constructor
step; different constructors remain a pair. The executable normalizer must
preserve BOTH endpoint projections at every depth.

For generated ordinary constraints, use two distinct fresh slots, not the
settled fragment's single slot. Every occurrence of each captured name refers
to the SAME lower/upper pair. Repeated occurrences must retain all self/cross
checks. The independent property is `lower <: upper` under the actual Common
model, together with satisfaction of the unchanged original atoms.

## Planned quantified results

* For every lower and upper endpoint and every normalized result, the executable
  normalizer returns that result iff `Normalizes` holds. Both projections equal
  the original endpoints. Arbitrary finite depth is quantified, not bounded.
* For every old atom state, assignment, list of captured names, and two actual
  Common payloads, satisfaction of the shifted original plus actual generated
  constraints iff the old state holds and (the name list is empty OR the actual
  lower payload is a subtype of the actual upper payload).
* For every checked declaration, every requirement in its original ordered
  where list, and every pair of successful independent endpoint inspections,
  the SUM of child endpoint sizes is strictly smaller than the parent's sum.
  No endpoint equality, assumed rank, successful child, or fuel bound.

## Why the old proof cannot simply be copied

Settled `generated_state_exact` proves generated captures are tautologies
because both endpoints occupy the same fresh slot. This is false for two
unequal payloads: int <: str is an inconsistent added constraint. Therefore
settled `where_state_recollection` cannot justify keeping the old state for
open intervals. The correction is to retain the generated constraints and
thread their effects, not assume their validity or choose a center.

The normalizer and descent bridges do NOT by themselves establish a new
`resolve_exact`. Endpoint-by-endpoint head inspection can also miss a candidate
that narrows an interval. The outer resolver requires a real candidate/state
producer. We will not label a normalization-only X15/X16 theorem as an outer
resolver conformance theorem. If the state bridge remains open, T1 is partial.
