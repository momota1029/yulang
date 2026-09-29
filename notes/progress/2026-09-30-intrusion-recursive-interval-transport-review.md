# SCC intrusion recursive-interval transport review

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Reference: frozen Yulang2 Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Classification: conditional selected-view lemma; no carrier/principality claim

## Candidate lemma

The abstract-semantics draft now states a transport equation for Oracle
recursive interval restoration before constraint canonicalization. A row
`(q, lower_q, upper_q)` restores in order as `lower_q ≤ q`, then
`q ≤ upper_q`; rows keep their source order. The transport uses two sorted
identity maps:

- `rho` injectively maps the complete local TypeVar domain and fixes preserved
  TypeVar anchors;
- `tau` freshens listed stack-quantifier IDs and fixes unlisted IDs, with its
  fresh range disjoint from the fixed subtraction-ID namespace, including
  unlisted IDs outside the receiving namespace.

Both maps apply through finite polarized syntax and TypeVar payloads nested
inside subtractability filters. The proof is structural over `Neu`/`Pos`/
`Neg`, `StackWeight`, and `Subtractability`; variable back-edges remain
endpoints.
This proves renaming commutes with the ordered pre-canonicalization interval
insertion for an already selected view. It does not prove Oracle projection,
solver-event equivalence, a subtype carrier, or principality.

## Oracle evidence and review

Frozen `instantiate.rs::instantiate_scheme_parts` preallocates ordinary and
recursive TypeVar mappings before cloning. `clone_recursive_bounds` clones
the neutral bound, projects its positive/negative endpoints, appends lower
then upper constraints for each row, and calls the solver after building the
ordered vector. `project_neu_bounds` is structural over finite neutral forms.
The relevant source locations are `instantiate.rs:620–648, 763–775,
850–943, 983–1028, 1062–1118`.

An independent compiler-referee review found a major gap: the original
TypeVar-only renaming omitted subtraction IDs carried by stack weights. The
lemma now includes `tau`, scopes the behavior to the ordinary non-imported
scheme adapter, and states freshness against all fixed unlisted subtraction
IDs. The reviewer confirmed that `clone_stack_weight` maps each entry through
`clone_subtract` and that nested `Subtractability` payloads recurse through
`clone_neu`; `(rho, tau)` therefore covers the cloned identities. The reviewer
confirmed the ordered equation and the inequality/not-equation distinction,
with no remaining blocking or major finding.

## Limits and next work

No source fixture is established here for a recursive interval containing a
freshened stack weight. The lemma is a conditional syntax-transport result,
not evidence that Oracle root projection selects the row. The candidate
denotational carrier and principal-solution theorem remain unselected; this
lemma advances the independent transport part only. Next operational work is
projection congruence and the ordered one-root transition simulation, subject
to resolving how the selected graph's evidence/query outcomes are represented.

No compiler code or tests changed or ran. No Python or measurements were used.
