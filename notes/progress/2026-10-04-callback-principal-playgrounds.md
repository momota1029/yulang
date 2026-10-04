# Callback lift and principal-support research playgrounds

Date: 2026-10-04
Status: bounded executable characterization evidence; no implementation or
semantic authority
Review: one independent compiler_referee review; no blocking/major finding.
The minor identity-coverage suggestion was closed by generating distinct
per-occurrence evidence identities and checking preservation after lifting.
Governing direction: [inference research playgrounds](../design/2026-10-04-inference-research-playgrounds.md)
Governing callback design: [production callback endpoint generation](../design/2026-10-04-production-callback-endpoint-generation-draft.md)
Governing principal criterion: [principal scheme acceptance](2026-10-04-principal-scheme-acceptance-criteria.md)

## Callback lift invariant

[`tools/research_callback_lift.py`](../../tools/research_callback_lift.py)
models one fixed `nu,K,D` fiber and finite source-witness relations with
separate argument-origin, body-origin, and result fields. The candidate lift
adds total derived output coordinates from the same witness while retaining
the old tuple and distinct per-occurrence `d-`, `d+`, and `b+` evidence
identities. It exhausts all 16 binary relations on two coordinates. Every lift forgets back
to the exact original witness relation and preserves the complete modeled
observation.

The model also shrinks independent-marginalization failure to two correlated
rows, `(0,0)` and `(1,1)`. Taking the product of the two marginals invents
`(0,1)` and `(1,0)`. Six of the 16 binary relations expose such a mismatch.
This is a concrete finite obstruction to replacing a joint witness relation
with unrelated coordinate marginals. It is not a counterexample to Theorem C:
the model has no source constructors, binders, calls, future use, resumption,
endpoint solver, or actual/checked source correspondence.

## Principal common-support invariant

[`tools/research_principal_support.py`](../../tools/research_principal_support.py)
enumerates 584 assignments of one to three distinct source occurrences over a
three-element finite support universe. For each, it checks that the least
common support admits each original occurrence separately, and that every
candidate support admits all of them exactly when it contains their union.
Original occurrence supports remain an ordered tuple; no equality between
branch/call endpoints is introduced. The smallest two-endpoint witness is
`{0}` and `{1}`, whose common public support is `{0,1}`.

This is only the powerset algebra behind a common-allowance candidate. It does
not define effect-row subtyping, prove that source generation produces these
supports, account for coupled Function ports or subtraction attachments, or
establish either direction of the principal-scheme solution-family theorem.
In particular it does not justify the `compose` hygiene boundary or the
principal `call`/`twice`/`choose`/`higher` interfaces by itself.

## Next proof work

The callback main gate still needs a source-to-endpoint correspondence showing
that production source derivations satisfy Theorem C's full finite generator
and preserve its whole-bound inclusion under the same `nu,K,D`. This leaf
model checks only the local total-coordinate extension lemma's basic shape.
The principal main gate still needs one same-fiber factorization argument
through source constraint generation, co-occurrence analysis, complete
Function comparison/evidence, and generalization. The support model identifies
the least finite common support but does not supply that argument.

## Verification

```text
python3 tools/research_callback_lift.py
  16 relations; all total lifts preserve old projections and observations;
  six marginalization mismatches; smallest has two correlated rows.
python3 tools/research_principal_support.py
  584 finite assignments; 560 retain distinct endpoint supports.
python3 -m py_compile tools/research_callback_lift.py tools/research_principal_support.py
  pass
```
