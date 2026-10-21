# R267 result — Y2 use route prefix classification

Primary-only; no independent review.

The exact pinned bundle has 112 direct use declarations. The first `UsePath`
base begins with `std::` in 108; all 108 resolve by longest existing prefix
to one of the 40 pinned module files, with zero unresolved `std::` bases. Four
non-`std` bases map to host acts declared in the same source (`time.clock`,
`io.console.warn/die`, `io.file.file`) and re-exported locally. Grouped forms
have 21 selected-item path nodes after their base routes.

This is source-route evidence only, not Y2 import/re-export semantics or a
runtime ModuleMap witness. The temporary probe was removed. Next compare the
source-ordered module edge graph and its closure with the pinned 40-file set.
See R267 contract and theory note.
