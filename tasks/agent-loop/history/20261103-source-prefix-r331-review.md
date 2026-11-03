# R331 — independent source-prefix audit

Baseline `839f7e3aa`; read-only inspection of the existing source and R330.
R314's `Fixture.anchor_computed` and `selected_occurs`, R315's
`selected_inventory_row` and `selected_request_computed`, and R330's
`original_owner_computed` and `original_call_computed` establish the static
allocation and the actual owner and call. They do not establish that a runtime
environment reaches that position. `Environment` has no position field, and
`actual_decoder_registration` assumes an already decoded enlarged environment.

In particular, an outer lambda can have admitted description and view witnesses
but no admitted invocation candidates. Its universally quantified body judgment
can then hold vacuously, without any invocation reaching the selected call.
The appropriate prefix claim therefore preserves each admitted invocation and
both `executionOpen` and `executionFixed` alternatives; unconditional existence
would require independent inhabitation. The selected path includes the outer
description and ViewLogic, invocation, receipt, Return/rebind, Shared and
EventProof binders before the selected App.

Original logical admission remains independent: R330 reduces its obligation to
`admissions.logical`, while `SourceAppAdmissionR159.rejectApp_no_source` gives
a checked counterexample to deriving admission from successful decoding and
the other source premises. R315's `original_parent_formation_iff` still requires
the original incoming decode, admission, formation, locals, checks and both child
judgments at the same candidate extension. Callable-image checking and
synthesis endpoints remain separate. This source audit did not run Lean and
does not claim a new kernel-checked theorem.
