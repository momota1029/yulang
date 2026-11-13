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

## Stronger automatic reconstruction

`safeCatalog` reads the actual packet journal in chronological order and retains
exactly the emissions of syntactically variable-free packets. `safe_history`
proves, for *every* actual reachable state, that this catalog has a Collected
history. It requires no `Closed`, `Supported`, all-model validity or evidence
premise. Unrestricted steps installing variable-bearing packets are followed but
their requests are not collected. Thus this result does not restrict the entire
trace to closed packets. `history` additionally recovers the unfiltered catalog
when every final packet is variable-free.

`CatalogEvidence` and `CatalogMultiArgumentEvidence` connect finite catalog
membership to current scalar/nominal and arbitrary finite scalar-point heads,
then to the actual recursive selected-payload classifier. They still require
current head Shape and selected descendants' request inclusion. The latter is
not shown automatically for all language syntax; general evidenceNode remains open.
The actual reserved-output example checks exact catalog `[request]` and an
inhabited current dictionary although that output had no initial observation.
