# R266 result — direct-use CST route locator

Primary-only; no independent review.

On the exact 40 pinned standard-library sources, the comment-projected Y3
parser produced 112 direct-root `UseDeclaration` nodes across 27 modules.
Every node had `UsePath` descendants, no local Missing/Error descendants, and
a text range equal to its exact projected source slice. The probe emitted
route paths and source declarations, then was removed.

This supports a source-bound locator for Y2 use syntax but does not prove Y2
import/module/re-export semantics. Grouped imports include selected-item paths
and local routes such as `clock::*`; route-to-module resolution remains open.
R149 root composition and outputs remain open. See R266 contract and theory
note.
