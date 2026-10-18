# R25 closeout — caller evidence binding

R25 completed its transport-only outcome. The caller-selected path now has a
HIR input that owns an opaque `'static + Send + Sync` payload and binds it to
one exact parse root, module identity, and HIR-admitted top-level binding
declaration. Foreign parse/module and nondeclaration anchors fail explicitly;
`SemanticImports::empty()` remains available. Candidate and runtime continue to
retain the same HIR through existing ownership.

The proof and HIR implementation received CLEAN independent reviews. Five new
focused binding tests passed, as did 130 HIR unit tests. Two existing
`simple_module_resolution` failures reproduced on the clean `f7edada81` baseline
and are not caused by R25. The package formatter check reports broad preexisting
format drift; the new test file passes its focused rustfmt check.

The result transports allocation/key identity only. It neither creates a
caller context nor proves that payload contents are authentic or stable. The
actual playground still lowers with `SemanticImports::empty()`. Parent
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN/closure0, with
original mathematical conditions **0 -> 0**. The next target is locating an
actually supplied authentic caller context and its introduction rule, then
applying it to the original source registration. If none exists, record the
first missing supplier/input and keep implementation blocked at that seam.

See the [R25 sprint contract](../agent-loop/sprints/caller-evidence-source-binding-20261018-r25.md),
[design](../design/2026-10-18-semantic-imports-evidence-binding.md),
[conditional proof](../theory/2026-10-18-caller-evidence-source-binding.md),
and [implementation handoff](../agent-loop/inbox/20261018-semantic-imports-evidence-binding.md).
