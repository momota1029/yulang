# Compose: effect-scope release and the identity case

Date: 2026-10-15
Status: Authoritative for the explicit user-selected compose expectation and scope of release below; representation and proof remain open
Selected-by: user, directly in the continuing hygiene conversation
Review: pre-write spec_auditor review accepted the expected-scheme replacement; final scoped transcription/supersession review found no findings
Scope: `my compose f g x = f (g x)`, its expected type and release of the `'e` protection scope within the output effect `'f`
Supersedes: only the earlier compose presentation in `../progress/2026-10-04-principal-scheme-acceptance-criteria.md`; clarifies the compose instance of `2026-10-05-handler-hygiene-public-provenance-notation.md`
Implementation: private scoped algebra implemented and locally proved; source/native integration and grammar adoption remain open (see checkpoint below)

## Direct decision

The user stated:

> `g x`が`'e`を放出するとします．このとき，`f`は`'e`の全てのエフェクトを捕捉できません．ただし，この保護は`f`が`id`であったときに破綻しかねません．それを防ぐために`'f`の出すエフェクト`'f`に`'e`の型が登場したとき，`'f`内から`'e`スコープの保護を外すというのが`'e?`です．内部ではもっと複雑な処理（それこそpush/pop的な処理）を行う必要があるとは思います．全体の型は`('a ['e] -> ['f] 'b) -> ('c -> ['e] 'a) -> 'c -> ['e?, 'f] b`です．

The selected expectation is:

```text
my compose f g x = f (g x)

compose : ('a ['e] -> ['f] 'b)
       -> ('c -> ['e] 'a)
       -> 'c -> ['e?, 'f] 'b
```

Notation normalization: the quotation's final `b` is written as `'b` above to
refer to the same result type variable. The function value `f` and the effect
variable `'f` are distinct. This is a user-selected expected presentation;
its principality and native derivation have not been established here.

## Scope of the operation

The contribution of `g x`, represented by `'e`, is protected while passed
through `f` in this unannotated composition. Sharing an inferred effect
component with `f`'s input does not itself authorize its capture.

When `'e` occurs within `f`'s output effect `'f`, the selected `'e?` operation
removes **the protection belonging to the `'e` scope** from those occurrences
in the output. This includes the forwarding case `f = id`: the output's
reference to `'e` must not retain that same scope's protection after release.
Merely constructing a separate released summand for the displayed `'e?`,
while leaving the corresponding occurrences inside `'f` protected by the
same scope, does not implement this decision.

The operation preserves the effect contribution and its attribution. Other
protection scopes remain distinct. It does not consume the effect or grant
capture by itself; subsequent handling follows the ordinary eligibility
rules. The separate [contravariant annotation policy](2026-10-10-annotation-effect-hygiene-integration.md#11-annotated-callback-and-computation-arguments-2026-10-15)
still governs the selected relay examples and the outward `write` residual.

The expected type must therefore retain the connection between `'e?` and
the occurrences of `'e` in `'f`. This record does not define an ordinary
set-union interpretation of that row, a general absorption equation such as
`['e?, 'e] = ['e?]`, or a graph traversal/substitution algorithm. Those would
need to preserve the selected scope and any independent protections.

## Implementation direction and remaining work

The [scoped algebra checkpoint](../progress/2026-10-15-scoped-effect-algebra-checkpoint.md)
records the compiled private kernel and independently reviewed local proof.
It does not establish the selected source scheme or activate handler removal.

The user selected the `'e?` strategy while allowing a richer internal
mechanism, including push/pop-like processing. This does not adopt the earlier
paired push/pop proposal or prohibit such operations internally. Grammar,
representation, transport through generalization and fresh use, and treatment
of overlapping scopes remain implementation/proof work.

The next concrete discriminator is `compose id g`: retain the supplied effect
through the input/output dependency and release the `'e` scope also where
that effect occurs within `'f`. An independent protection must survive that
release. Derive this behavior from ordinary source constraints, without a
special case for `compose` or `id`. Existing conditional protection-filter
results retain their premises; this clarification is not their source-to-code
bridge or a completed hygiene theorem.

## Supersession and verification boundary

The earlier compose expectation ended in the outer result-effect variable
alone (alpha-renamed, `['f] 'b`). The current expected presentation is
`['e?, 'f] 'b`. Other acceptance examples are unchanged. Historical
factorization attempts about the earlier presentation remain historical;
they do not automatically establish the new expectation.

This is a documentation-only M2 contract update with one scoped
`spec_auditor`. Checks are document references, code fences and
`git diff --check`. No builds, tests, source execution or measurements are
part of this update; no inference, implementation or production gate closes.
