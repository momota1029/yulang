# R277 — pinned fmt parser diagnostic census

Status: checkpointed, primary-only, unreviewed. The R149 Types/Console samples,
authentic imports, role selection, execution and proof remain OPEN.

## Parent obstruction

R149 requires the unchanged Types sample's `pair.say` to resolve through the
authentic pinned `Display` role. R276 established the exact
`lib/std/core/fmt.yu` blob and source-root identity, but parsing that source
currently yields syntax diagnostics, preventing `ShadowArtifact` publication.
This census identifies where those diagnostics arise before any parser grammar
change is authorized.

## Scope

Retain exact diagnostic ranges, source excerpts, and structural categories
from the same parsed snapshot. Group by an owning grammar/recovery shape where
the available parser evidence supports it. A small owner-local fix is allowed
only if malformed neighboring syntax remains rejected and pinned bytes stay
unchanged. Otherwise record a precise unresolved owner and stop before edits
outside the current leases.

This is neither a role resolver nor a proof step. The R149 source/native gate
remains OPEN, including the missing source-to-schedule/import correspondence.
The design and proof Markdown remains governing: contravariant `[io]` is the
open row `[io,'e]`; a `[state]` callback is not rejected merely because its
effect differs from `io`.

## Verification

The focused test parses the exact blob-asserted source once, retains all 50
diagnostic ranges and bounded 160-byte source excerpts, verifies every range
slices valid UTF-8 source bytes, checks preorder ordinals, and asserts the full
category/parent census:

| Diagnostic kind | Structural parent | Count | Representative source |
| --- | --- | ---: | --- |
| `ErrorGroup` | `Root` | 36 | `pub a.show: str`; `.show = ...`; `where 'a: Display` |
| `ErrorGroup` | `OperatorChain` | 7 | `>` in conditional expressions |
| `Missing` | `CaseArm` | 7 | zero-width missing-arm sites after case alternatives |

The root-level groups span role member signatures, implementation member
bodies, and `where` constraints across the module. The other two classes arise
in expression syntax. This is not one isolated recovery owner: grammar support
and semantic carriers are absent across declarations, constraints, operators,
and case arms. The exact parser owners lie under `crates/yu-syntax`, outside
R277's leases; editing them would also require HIR/source-carrier design.
R277 stops with this exact cross-owner boundary instead of masking diagnostics
or expanding leases mid-sprint.

Focused census test, `cargo check -p yu-playground`, sprint static check and
`git diff --check` pass. No full-suite run or independent review under this
solo sprint.
