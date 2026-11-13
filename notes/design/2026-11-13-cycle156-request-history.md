# Request collection along actual Value executions

Draft proof design, cycle156, Evidence lane. This does not alter language semantics.

A finite `Collected registry root state batch` history starts at an actual empty-journal
source state. It may collect requests structurally observed at that current state,
advance by any actual Value step without adding requests, or append exactly the
requests emitted by an actual installation. The installation guard is the existing
syntactic condition that its materialized schema has no variables. In particular
this permits new allocated output identities absent from the initial carrier.

The history does not take final `Supported`, generated Models, BranchModels,
Evidence, Stable, or an executor correctness hypothesis. Its projections prove an
actual initial-to-final trace and derive Supported for the collected batch. Hence
all current journal models validate the generated batch, even after carrier-changing
refreshes. Sub-batches and reordered requests are supported by membership, so a
consumer need not use every earlier emitted request.

This is a finite operational-history interface for existing restricted request
proofs, not the missing assertion that every generated request is collected or
variable-free. Shared-variable requests and generic evidenceNode remain open.
A concrete reserved-output installation/equality/refresh history tests the interface.
