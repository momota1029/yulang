# R61 source-owner audit: whole-Function ascription

Status: `NO_SAFE_CODE_SLICE`; first missing authority is a source typing/formation judgment for an explicit whole-Function ascription and its relation to checking and exposed interfaces.

## Fixed source and coordinates

For

```yu
act io:
    our tick: int -> int

my forward (t:[io] int): [io] int -> [io] int = t
my outer (q:[io] int) = forward q
```

the HIR source annotation representation can retain the owner and source position of each parsed annotation. The formal annotation is at `p_t`; the two nested effect-row positions in the whole-Function type are `p_A` and `p_R`. These positions arise from distinct syntax nodes; none is inferred from row shape. `SourceAnnotation` stores `{ owner, position, ty }`, and `SourceEffectRow` stores its own row position and resolved concrete effect declarations.

## Authority inversion

The approved inferred-Function-call-views design §1.1 explicitly separates written contracts, inferred public schemes, and internal evidence-rich views. Its §2 selects a shared role-indexed callback source-formation direction, says typed paths/Flow/ownership/receiver relations arise from source resolution and typed elaboration, and leaves the exact judgments that construct and preserve them open. Sections 5.1–5.3 require later judgments for callback contract generation, correlated `nu,K,D`, and annotation permission/protection. The approved answer likewise says detailed generation rules and proofs remain gated.

That authority governs the callback-view problem. It does not state a whole-definition-ascription rule for `forward`, nor identify how the written `p_A`/`p_R` contract is related to a raw provider `P`, a checking interface `C`, and an exposed interface `X`. Applying callback `F_cb` formation to this definition would therefore assume applicability and missing rules. No other pinned authority supplies the needed judgment in this R61 packet.

The first unavailable judgment is consequently a source formation/typing rule with operands at least identifying (a) the resolved source expression/provider and its owner, (b) the written whole-Function contract with `p_t,p_A,p_R`, (c) the typing/substitution environment and ordinary generated constraints, and (d) the scope-local permission and result evidence. Its conclusion must identify the source-valid ascription and a source-indexed relation to `P,C,X`, preserving the same provider/carrier and the jointly scoped `K,D` and correlated result coordinates. The governing callback-view authority gives a direction and invariants, but does not derive these operands or this conclusion for an explicit whole ascription.

## Existing source and native owners

HIR owns syntax retention. `source_annotation::form` parses a binding's complete written annotation; `parse_annotation` and `parse_expression_ascription` both call `parse_annotation_with_marker`, which stores the source owner, annotation node position, and parsed type. `LocalSourceBuilder` retains a binding annotation and creates an `Ascription { inner, annotation }` node for expression ascriptions. These are syntax/identity producers, not a typed derivation or `Corr` producer.

The candidate source builder owns native candidate routing. For the fixed definition annotation, the root `Action::Annotation` carries the body endpoint and the root target into `candidate_annotation`; that calls `candidate_annotation_pair`. The pair constructs the negative checking signature, links the body endpoint to it, constrains the body's computation effect, then constructs the positive exposed signature and links it to the root target. Expression ascriptions also use this pair with their child endpoint and same endpoint as target, but that is a different source form. These are implementation routes, not evidence that the corresponding source rule admits the fixed contract or that the route preserves the original provider and every source solution.

For the fixed annotation, candidate preflight recursively flips Function argument polarity. The explicit concrete row at `p_A` therefore reaches a negative position; `preflight_annotation` rejects concrete rows there. The signature constructor independently returns unavailable for a concrete row when its variance is negative. So the current guarded route does not construct the fixed whole-ascription candidate. The formal-parameter permission constructor is a separate owner: it records `FormalPermission` using a parameter index, occurrence, annotation owner/scope, port path, and source row. That domain is not a whole-ascription source rule and cannot be silently substituted for one.

## Dependencies and implementation decision

Because no source rule admits and types this contract, there is no derivation from which to establish the actual dependency structure of `Q`, `Corr`, source-solution lifting, or reverse interpretation under typed substitutions. In particular, `Q` independence is **unestablished**. I make no claim that the source excludes R59's assignment, that source solutions are counterexamples, or that R60's scalar result can be instantiated here. The original `K,D`, permission witnesses, and result correlation remain obligations.

`NO_SAFE_CODE_SLICE`: changing preflight or the negative-row constructor would implement a behavior without an authorized whole-ascription formation judgment. The next prerequisite is an authority-approved source rule naming the typed provider, annotation positions, checking/exposed relationship, substitution transport, local permission, and correlated result evidence; then a proof can map that rule to native construction and determine `Q` dependencies. Keep the current guards and parent theorem status unchanged until then.
