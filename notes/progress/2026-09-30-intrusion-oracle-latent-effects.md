# Oracle latent-effect obligations for SCC intrusion

Date: 2026-09-30
Oracle: frozen Yulang2 `main` at `a58eefc3`
Status: source characterization; no equivalence or principality claim

## Ordinary Functions already carry effect identities

The Oracle's ordinary Function lowering allocates effect variables even when
the source contains no explicit effect-row or handler syntax:

- `crates/infer/src/lowering/expr/constraints.rs:7–24` creates an exact-pure
  effect constrained between `Bottom` and the empty row.
- `lowering/expr/lambda.rs:954–969` places an exact-pure evaluation effect on
  a lambda and derives its return effect from the body.
- `lowering/expr/tail.rs:1092–1109` represents that return effect as a
  variable endpoint.
- `lowering/expr/lambda.rs:1127–1168,1251–1264` allocates function, output,
  and body effects for a defined Function and gives an unannotated parameter
  the `never` negative effect.

Consequently, an effect-free polarized value graph is not a complete source
semantics for ordinary Function inference. Any source-level Oracle parity claim
for Function uses must model these effect endpoints and their boundary identity
behavior, even if the supported source syntax excludes explicit effect rows and
handlers.

## Forced identity and use behavior

The no-explicit-effect source fixture recorded in
`2026-09-30-intrusion-bounded-negative-counterexample.md` §§ “Forced effect
quantifier use-map characterization” and “Two annotated-parent source uses”
observes:

- local generalization initially selects no ordinary quantifier;
- recursive effect passthrough forces one effect identity into the scheme;
- two reads of that scheme freshen the forced identity independently;
- eleven unquantified effect identities remain shared across those uses.

The lowering path is in `lowering/expr/tail.rs:970–1011,1241–1419`; per-use
freshening and preservation of unlisted identities are in
`analysis/instantiate.rs:620–648,732–760,798–808`. The unannotated-parent
branch instead retains the live local value when forced quantifiers exist.
This is identity transport evidence only; the two reads have the same call
shape and do not establish effect denotation or handler hygiene.

The nominally guarded two-member Function SCC with three differently typed
incoming uses is a separate Oracle characterization in the same bounded
counterexample record. It shows ordered component publication, internal live
uses, distinct incoming value identities, and differing argument constraints.
Its production freshening maps are not keyed to individual uses, and its raw
reachability check does not prove transitive isolation. It does not establish
effect transport for a multi-member component.

## Consequence for the full redesign goal

The effect-free Function graph in the abstract-semantics draft can serve as a
component lemma only. It cannot be the end-to-end source envelope or the
acceptance boundary for the user's Oracle-capability objective. The successor
semantics must eventually account for latent effect bounds, forced
generalization, use-site freshening, preserved shared identities, and the
sequential root/publication lifecycle. Handler matching, masks, weights, and
runtime freshness remain separate obligations until the supported source
envelope says they are admitted.

No Oracle code was changed and no test or measurement was run for this record.
The frozen source paths and prior focused probe records above are the evidence.
