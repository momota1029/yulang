# Callback source-to-endpoint evidence join

Date: 2026-10-05
Status: bounded executable bridge characterization; no production membership, inference, or semantic authority
Reviewed-by: independent read-only review closed the incidence-integrity major finding; no residual blocking/major issue

[`tools/research_callback_endpoint_source_join.py`](../../tools/research_callback_endpoint_source_join.py)
joins the existing finite `Observation` rows from
[`research_callback_consumer_factorization.py`](../../tools/research_callback_consumer_factorization.py)
to the existing `Evidence`/`Source` records and `generate`/`audit` functions in
[`research_callback_endpoint_trace.py`](../../tools/research_callback_endpoint_trace.py).
For a supplied identity-valued Handler-literal skeleton, it checks two pending
body-request rows and four completed histories. The designated result consumer
is silent in these histories. One Force request retains the same source event
under distinct `d-` and `d+` occurrence identities, and an observed body
request alone supplies `b+`.

The adapter validates the existing event-to-incidence relation before
constructing endpoint evidence. A first review found that the initial adapter
copied supplied occurrence strings without checking them against events; the
repair calls the existing `audit_projection`, enforces this singleton case,
and adds a ghost-incidence mutant. The final model rejects occurrence
collapse, owner substitution, scope substitution, missing body incidence, and
substituted source incidence (5/5).

This connects one operational source model to one B-step evidence model. It
does not implement or define a new carrier. Its `Force`/`CallView` path names
are the supplied bounded skeleton mapping; the model does not derive
production `Flow`/`Observe`, real `Rel_C`/`nu,K,D`, descriptor membership,
Option 2 extras, subtraction, actual-to-checked containment, or principality.
In particular, it does not close the production Function membership/admission
gate.

Verification:

```text
PYTHONDONTWRITEBYTECODE=1 python3 tools/research_callback_endpoint_source_join.py
  6 joined rows; 2 pending Body histories; 4 completed histories; 5/5 mutants rejected
PYTHONDONTWRITEBYTECODE=1 python3 tools/research_handler_provenance_projection.py
  historical independent probe still passes its 16 incidence assignments
git diff --check
  pass
```
