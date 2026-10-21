# R261–R265 parser/import evidence archive

These primary-only results refine the imported-root gate; none closes R149 or
authorizes runtime publication. Exact contracts, notes and inbox receipts are
in the paths named below and their bytes are frozen in Git.

| Sprint | Frozen contract | Result note | Main finding |
|---|---|---|---|
| R261 | `tasks/agent-loop/sprints/yulang2-y3-parser-root-witness-boundary-20261021-r261.md` | `notes/theory/2026-10-21-r261-parser-dialect-boundary.md` | Y3 parser treats some Y2 `--` comments as syntax; raw Y3 root counts are not Y2 evidence. |
| R262 | `tasks/agent-loop/sprints/yulang2-bounded-comment-projection-20261021-r262.md` | `notes/theory/2026-10-21-r262-comment-projection-falsifier.md` | Comment-only projection with an empty syntax environment produced 474 diagnostics; R264 later qualifies these totals. |
| R263 | `tasks/agent-loop/sprints/yulang2-inrepo-parser-registration-audit-20261021-r263.md` | `notes/theory/2026-10-21-r263-y2-parser-registration-audit.md` | No in-repository Y2 parser or ModuleMap registration implementation was found. |
| R264 | `tasks/agent-loop/sprints/yulang2-imported-operator-environment-check-20261021-r264.md` | `notes/theory/2026-10-21-r264-syntax-environment-confound.md` | Empty and all-source operator environments are both inauthentic controls. |
| R265 | `tasks/agent-loop/sprints/yulang2-module-local-syntax-environments-20261021-r265.md` | `notes/theory/2026-10-21-r265-header-import-coverage.md` | Current header scan sees 45 imports versus 112 direct use roots, with 20/40 modules differing. |

The temporary probes were removed. Their Cargo invocations are exploratory
syntax-interface observations, not retained tests or compatibility proofs.
R260's imported empty-set census remains conditional. The next useful source
seam is exact parsing of direct-root Y2 `UseDeclaration` inputs, not another
aggregate diagnostic count.
