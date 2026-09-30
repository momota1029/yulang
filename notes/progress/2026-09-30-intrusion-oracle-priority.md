# Oracle compatibility priority and q-erasure divergence record

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Status: concrete graph conflict recorded; successor remains unreviewed and
unapproved

## Priority and divergence gate

The user's priority is soundness, then principality, then Oracle-compatible
observable behavior. An Oracle mismatch alone does not authorize divergence.
The record must identify the concrete conflict, the exact Oracle behavior to
drop, the proposed successor rule, and compatibility impact. A new semantic
contract still needs independent review and user approval before implementation.

## Concrete conflict

The frozen Oracle `a58eefc31` source `pub f x = x f` has a selected graph with
q's direct upper bound `q ≤ Fun(S,V)` and the selected root lower edge
`Fun(q,V) ≤ root`. The Oracle erases q at negative polarity and publishes
`Fun(Top, ..., V)` with no q recursive bound. Under a subtype preorder where
`Top` is greatest, proper Functions are strictly below `Top`, and Function
arguments are contravariant, the erased scheme relation contains
`Fun(Top,Bottom)`. The selected source graph has no satisfying root below that
type: the root edge would imply `Fun(q,V) ≤ Fun(Top,Bottom)`, hence `Top ≤ q`;
the direct upper gives `q ≤ Fun(S,V)`, hence `Top ≤ Fun(S,V)`, contradiction.
The q/S cycle fragment is nonempty with `q=Bottom`, `S=Top`, `V=Bottom`,
`root=Top`. The complete derivation and graph-level scope are in
`notes/design/2026-09-30-intrusion-q-bound-successor-draft.md`.

This is a concrete mismatch between the selected source-bound root relation
and the published scheme's ordinary upward-closure relation, under the stated
semantic assumptions. It is a principality conflict for that graph fragment.
It does not prove the whole effectful source-to-scheme adequacy theorem or
that the Oracle accepts an invalid executable program. In fact, Oracle
specialization rejects both concrete uses traced so far: `f 1` at
`int -> unit`, and `f id` at `(unit -> unit) -> unit`. Oracle `dump-poly`
succeeds for the former source and reports `main : never`, while `dump-mono`
rejects it later. These are separate public phase observations.

## Oracle behavior proposed for removal

Drop the inference projection rule that erases a variable at one polarity
despite selected incident bounds and then prunes its recursive row. Keep
unconstrained one-polarity erasure. This is the exact behavior observed for q
in `pub f x = x f`, not a blanket rejection of all Oracle one-sided
projection.

## Proposed successor behavior

Retain a bounded one-polarity variable as a boundary parent in the generalized
member graph, retaining its selected incident constraints and recursive
back-edges. Freshen that parent and transport the same constraints per
incoming use. Derive the member's `Root` / `Pred` relation from that graph.
The intended rationale is that keeping the obligations avoids enlarging the
source root relation by deleting the q upper bound. Unconstrained one-sided
variables remain eligible for `Top` / `Bottom` projection.

This successor is only a draft. Its full principal-root theorem, eligibility
criteria for selected edges, and transport across effects and roles remain
unproved.

## Compatibility impact

For `pub f x = x f`, `dump-poly` would no longer publish `any -> ['a] 'b`
without q's bound; it would publish a bound-preserving graph view or report an
earlier use error. The observed `f 1` and `f id` programs already fail
`dump-mono`, so those fixtures may retain final mono rejection but change
failure stage, message, span, and public scheme output. API consumers that rely
on the broad displayed scheme may observe a narrower result. Acceptance and
diagnostics for other contexts are unmeasured. The proposed draft at
`notes/design/2026-09-30-intrusion-q-bound-successor-draft.md` lists these
risks and remaining proof obligations.

No implementation is authorized yet: the successor draft has no independent
review and no recorded user approval. The next gate is independent review of
the exact conflict and the proposed root-principality rule, followed by the
user's approval decision.
