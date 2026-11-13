# Historical finite request observations through arbitrary feedback

Status: planned conditional soundness bridge, 2026-11-13, cycle 154.

The finite structural certificate from cycle 153 need not remain syntactically
visible after refresh. For a fixed list of requests, generated materialization
schemas depend only on constructors and interpretation, not the refreshed view.
Actual feedback steps retain these two inputs. Every final journal model is an
earlier model. Therefore a finite source observation at the earlier state proves
all generated constraints at the final state without an unchanged-view premise.

Planned theorem: for every registry, root, finite actual feedback trace from s to
t, request list rs observed by a finite point-tree certificate at s, final journal
model m, arbitrary declaration/capture and final report, generated rs at t has
materialization Models at m. The request list stays fixed. This does not prove
fresh requests are observed, current candidate reports valid, alias Joint, or
complete evidenceNode. Variable-only where clauses give a corollary for actual
requests, since these are precisely the fixed named root requests.

No new language semantics. Existing general definitions are unchanged. Yulang2
is not rerun: this is semantic transport in existing Lean transitions, not a
claimed source-language behavior correspondence.
