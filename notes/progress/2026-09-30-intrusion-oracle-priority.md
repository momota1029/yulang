# Oracle compatibility priority and q-erasure divergence record

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Status: user-approved priority recorded; exact successor representation
remains unreviewed

## Priority and divergence gate

The user's priority is soundness, then principality, then Oracle-compatible
observable behavior. The user clarified on 2026-09-30 that q polarity erasure
is not required: retain any meaningful source constraint. Inference-stage
scheme formatting and acceptance phase need not match Oracle; final acceptance
of well-typed programs is the compatibility target. An Oracle mismatch alone
does not justify divergence; identify the conflict, behavior to drop,
successor rule, and impact. The user approved this priority and retention
policy. The exact parent graph representation still needs independent semantic
review before implementation under the repository design gate.

## Concrete conflict

The frozen Oracle `a58eefc31` source `pub f x = x f` has a selected graph with
q's direct upper bound `q ≤ Fun(S,V)` and the selected root lower edge
`Fun(q,V) ≤ root`. The Oracle erases q at negative polarity and publishes
`Fun(Top, ..., V)` with no q recursive bound. Under a subtype preorder where
`Top` is greatest, proper Functions are strictly below `Top`, and Function
arguments are contravariant, the pure value projection of the erased scheme
relation contains `Fun(Top,Bottom)` with its separate effect coordinates held
fixed. The selected source graph has no satisfying root below that type: the
root edge would imply `Fun(q,V) ≤ Fun(Top,Bottom)`, hence `Top ≤ q`;
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

## Successor behavior directed by the user

Retain a bounded one-polarity variable as a boundary parent in the generalized
member graph, retaining its selected incident constraints and recursive
back-edges. Freshen that parent and transport the same constraints per
incoming use. Derive the member's `Root` / `Pred` relation from that graph.
The intended rationale is that keeping the obligations avoids enlarging the
source root relation by deleting the q upper bound. Unconstrained one-sided
variables remain eligible for `Top` / `Bottom` projection.

The user directed this source-constraint-retention policy. Its full
principal-root theorem, meaningful-bound eligibility criteria, and transport
across effects and roles remain unproved and unreviewed.

## Compatibility boundary and impact

For `pub f x = x f`, `dump-poly` may stop publishing `any -> ['a] 'b` without
q's bound or may reject a use earlier. Such inference-stage scheme or
acceptance-phase differences are allowed. The observed `f 1` and `f id`
programs already fail `dump-mono`, so these examples can retain final rejection
while changing phase. The required comparison is final acceptance of
well-typed programs across the supported envelope; other contexts remain
unmeasured. The proposed draft at
`notes/design/2026-09-30-intrusion-q-bound-successor-draft.md` lists these
proof obligations.

The policy itself is user-approved. No implementation is authorized yet:
exact graph semantics and the final-acceptance theorem remain open, and the
successor representation has not had independent review.
