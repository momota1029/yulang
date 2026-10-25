# R17.1 primary adjudication — reviewed prerequisite accepted

Date: 2026-10-25. Branch: `research/simple-sub-intrusion`. Baseline admission: `ef70266396de7500abb61945d6c1c1d8c0493682`; isolated worktree commit: `aacb81609`.

## Decision and boundary

Accept the frozen candidate as a reviewed prerequisite for the shared-context value-only universal-introduction and arbitrary substitution-transport seam across all six represented judgments. It consumes the R16.2 raw mapping prerequisite in the type-abstraction case and keeps the original arbitrary `σ`, D/Xi/Γ contexts, source forms and prior constructor premises. This does **not** close the full-paper typing theorem, omitted-rule coverage, inference/executor soundness, original A/B obligations, source/native/Rust correspondence, or production. Those parent gates remain OPEN.

Independent review found no blocking or major findings within its assigned R17 scope. The review was source-only and ran no Lean/Lake checker. It inspected all 36 constructors, the six transports, shared-context shifting, binder substitution, the concrete `var 0 → var 1` application, retained full types/axioms and governing manuscript locations. Its report is preserved at `paper-typing-subst-r17-review.md` (reviewer report SHA-256 `f2a37e0ef76957ca5dc352ea7878f68d7fd9f54d5209768fde0477e7cfe9cc3f`). No repair was requested.

## Frozen artifacts

- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean` — SHA-256 `8f4a32fd1c013ae78a161dadd52bed57cc7c99af5ae30fd30ba133de2c3f74a4`.
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean` — SHA-256 `b2975d38fccbf5c908741c3714b2b513b4b8706d80f3c009125c815d1b944d89`.
- Producer handoff: `paper-typing-subst-r17.md` — SHA-256 `fc23855facec8069ff3f4e72a2d7dc927680ceaaf68d2aa994cf715189b9efb6`.
- Exact audit input: `paper-typing-subst-r17-audit.lean` — SHA-256 `05e22fc223be25f2d7fc8894f8204e79e6040a3e5d6a344a419594ecbdbc9260`.
- Accepted review: `paper-typing-subst-r17-review.md` — SHA-256 `f2a37e0ef76957ca5dc352ea7878f68d7fd9f54d5209768fde0477e7cfe9cc3f`.
- R17.1 amendment: `tasks/agent-loop/sprints/paper-execution-typing-r17-amendment1.md` — SHA-256 `183b789f4bb87c45cbe72074061763e65f93a733e8dce006d3e2dea11d7c0450`.

## Primary verification receipts

R17.1 preserves every invocation 1–5, including the two disallowed version-query incidents, as charged historical evidence; no query was repeated. Worker invocation 6 directly audited the eight declarations and type-abstraction constructor in 2.336589 seconds. Primary invocation 11 attempted `lake build -j1 ...`; Lake rejected `-j` as an unknown short option, exit 1. This failed invocation is charged and no retry was made. Primary invocation 12 ran:

```sh
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake env lean -j1 -M1024 .lake/R17Audit.lean
```

Exit 0; 0.482882 seconds. It printed all six exact transport types, both shared-context application types, all six indexed judgment signatures, and constructor type/axioms. The eight theorems and `PaperValueTyped.typeAbstraction` each reported exactly `[propext, Quot.sound]`. No `sorryAx`, project axiom, or additional standard axiom appeared. The successful focused builds of changed Syntax, accepted BinderLaws and TypingSubstitution are the worker's invocations 3 and 5, recorded with full output in the handoff. Primary final call 11 did not provide an additional build receipt; it is recorded as a failure, not treated as verification.

Worker used calls 1–6 and about 31.146 checker seconds; primary used reserved calls 11–12. R17 total remains within the original 12-call and 180-checker-second caps. No calls were borrowed from R16, and no calls beyond the cap were launched. Reviewer used zero Lean/Lake calls. No tests were requested or run.

## Remaining work

The first omitted paper typing-table introduction is variant payload/tag/arity typing (`Value.variant`). The primary owns the next exact paper-rule coverage and proof packet. Further nominal/wrap/elimination/handler/map/template/primitive/admin rules and recursive graph guards remain unrepresented or open. Concrete executor/inference and source/native/Rust bridges remain separately owned and OPEN. No production authority is created by this acceptance.

The proof worker and reviewer both confirmed STOPPED, with no active processes, descendants or later writes. The review was frozen after report hash verification. The primary imported only the frozen artifacts into this checkout.
