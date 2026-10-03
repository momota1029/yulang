# Value-entry request projection under the shared callback fiber

Date: 2026-10-04
Branch: `research/simple-sub-intrusion`
Status: proof-only conditional lemma; no source rule or implementation authority

## Scope and authority

This lemma uses the user-selected §21 Value-entry schedule, inert whole-
argument construction, callback slot as typed invocation view, and role-first
Function elaboration. It does not give `never`, `Any`, or an empty effect row
an effect meaning. It does not compare effect ports independently, compose
successful concrete inequalities, or define a total subtraction algebra.

The lemma isolates one consequence of the already recorded source equation
`Force(D) >>= B`. It strengthens the informal support statement in §9 of
`notes/design/2026-10-02-typed-computation-core-elaboration.md`: it states the
required quantification over current state and resumption histories explicitly.

## Conditional statement

Fix one inequality query `q`, one assignment `ν`, and one joint typed-family
fiber with the same `K,D` identities throughout. Let `D` be the inert argument
carrier received by an actual Value-entry invocation. In the receiver's source
execution, let `F_D` denote its designated one-layer execution followed by
rebind, and let `B` denote the body and its designated result consumer. The
complete call uses the state-threaded composition

```text
J = F_D >>= B
```

inside the actual complete callback `CallView`; receipt remains before `F_D`.
For a retained-computation entry this equation is inapplicable unless the
body explicitly consumes the carrier.

For each compatible current configuration and every finite legal response,
resumption, alias/store transition, and repeated raw-resumption history
reachable in `J`, suppose:

1. every typed request emitted while executing `F_D` is admitted by row
   descriptor `d` at its original typed occurrence and under the same
   `ν,K,D`;
2. every typed request emitted by `B` or the designated result consumer is
   admitted by descriptor `b` at its original typed occurrence and under the
   same `ν,K,D`;
3. every request-emitting transition in the complete `CallView` belongs to
   one of those two source segments, or is already included in the bound for
   the segment containing it. No request origin, operation instance,
   response dependency, or handler authority is introduced by flattening the
   descriptors.
4. for each occurrence from either segment that is observed at the complete
   call boundary, the source derivation supplies its event-specific `Flow`
   and `Observe` correspondence to that boundary, with the same occurrence,
   handler configuration, and `ν,K,D` fiber. These correspondences are
   admissible independently of the result of `q`.
5. the source-derived linked component-combination evidence maps those
   corresponding observations into `[b,d]` at the common output profile.
   This is a premise of this projection corollary, not a generic row-union
   law and not a consequence of merely sharing `ν,K,D`.

Then each request observed in the complete call is admitted by the same-fiber
combined view `[b,d]`:

```text
Obs(J, q, ν, K, D) ⊆ Row([b,d], ν, K, D)
```

Here `Obs` is the request observation at the complete source `CallView`, not
the union of independently solved port marginals. The bracket denotes the
user-selected linked effect-lifting presentation in its common fiber; it
does not assert a new general row-union judgment. Canonical flat-row
normalization may combine the visible components, while their source
correlation remains in existing constraint/evidence relations. Without
premises 4–5, the operational argument below proves only that each emitted
request has an argument-entry or body/result source origin; it does not prove
transport to the output occurrence or membership in `[b,d]`.

## Proof sketch

Mark each emitted request occurrence by the source transition that emits it.
In the `Return` clause of state-threaded bind, `F_D` has completed at its
current state and control enters `B`; requests in that suffix therefore carry
the second premise. In the `Request` clause, bind preserves the exact request,
origin, typed payload, operation instance, and live `K,D`, and attaches the
remaining suffix to the original continuation. The request is therefore
covered by the first premise, while any later suffix request is covered by
the premise for the segment that emits it.

Apply this argument after every legal resumption. The continuation receives
the current resumed state and retains its original caller lineage; the proof
does not restore an earlier store, identify separate operation instances, or
replay receipt. Multi-shot resumption can revisit either segment in a changed
state, which is why premises 1 and 2 quantify over every compatible state and
history, not just the initial call. Induction over each finite interaction
prefix proves that every observed request occurrence has one of the two
source origins. Premise 4 then transports those same event occurrences to
their complete-call observation positions. Premise 5 supplies exactly the
joint component rule needed to place those observations in `[b,d]`. Neither
transport nor combination follows from common `ν,K,D` alone.

The claim is only about requests in this immediate complete call relation.
Returned latent interfaces keep their own typed paths and require the
existing future-use obligations; this proof does not flatten them into
`[b,d]`. The theorem is query-local: it gives no rule for composing concrete
comparison successes from different queries.

## What it does not establish

The source schedule and callback slot view justify the operational shape, but
the source premises remain to be derived for a Function inequality. In
particular this lemma does not prove that `d` is the callback slot's admitted
argument descriptor, that `b` is the actual body's complete descriptor, that
the rows denote the whole admission domains, or that
`D_checked(q) ⊆ D_actual(q)`. It does not establish endpoint adequacy for
`T_P`, either universal clause of the complete Function comparison, or a
finite principal presentation.

Thus this is not yet a proof of
`Fun(a, never, b, c) <: Fun(a, d, [b,d], c)`. The bind argument supplies only
the source-origin factorization. Its typed-profile corollary additionally
requires the still-unproved occurrence maps and joint component rule in
premises 4–5. Neither step interprets effect-position `never`.

The next proof must construct these segment bounds and the complete checked
challenge domain independently of comparison success, then derive the
occurrence maps and linked combination at the output profile and relate the
actual Pure endpoint to its source description over all legal histories. State-slot
runtime transitions and opaque first-class-reference imports remain separate
source bridges; this lemma assumes compatible state/history premises and
does not construct them.

## Review and remaining gate

The first compiler-referee review found a major gap: source-origin coverage
and common `ν,K,D` did not entail event-specific `Flow`/`Observe` transport to
the complete call output or the linked component-combination rule. The
statement was repaired to make both explicit premises. A focused fresh
compiler-referee delta review found the finding closed with no further issue.
Accordingly, the proved content is the conditional bind/source-origin
factorization; typed transport and `[b,d]` membership remain unproved source
obligations. No source semantics, solver carrier, API, or implementation is
approved by this note.

Next: derive or refute those occurrence maps and combination evidence from
the already approved slot invocation view and source-owned `Rel_C`, `K,D`,
`Flow`/`Observe`, `Path`, and incidence. Then derive the checked challenge
domain and actual Pure endpoint correspondence over the same complete
histories. No comparison success may be a premise for admission.
