# R275 revision 3 constructor and entry-route coverage

Readiness map only; this table proves no fixture-specific branch or normal
return. The 41 indexed payloads identify production owners and exact visible
forwarding. Omitted behavior remains unknown.

| Caller/callsite | Actual callee/owner | View payloads | Required normal-return premise |
|---|---|---|---|
| Fixture datum calls `scan_header(source)` and passes the same Arc to `parse_file` | `scan_header` → `discover_header` → `into_header_info` | R274-E001, R275-E001/E002; R274-E008 | Header discovery returns and HeaderInfo receives the exact Arc allocation. |
| `parse_file` | same-Arc assertion → operator selection → `cursor::parse_root` | R274-E009 | Arc assertion and operator construction pass; parser returns the required CST without recovery. |
| `cursor::parse_root` | `root_statement::parse_root_statements` → `root_statement_sequence` | R274-E003, R275R3-E001, R274-E010 | Root wrapper consumes to EOF and terminal handling returns normally; exact fixture branch/recovery status remains unproved. |
| Fixture HIR call `yu_hir::shadow::lower_module_with_local_source` | public HIR wrapper → `module::lower_module_with_local_source` and source-carrier construction | R274-E001, R275R3-E002, R274-E022, R274-E023 | Wrapper forwards identity/parser/imports; identity guards pass; lowering returns `Ok` with the exact root and fourteen-slot carrier. Correct owners are E022 for module lowering and E023 for local-source carrier logic. |
| Public `ConstraintBatch::collect(hir)` | `collect_mode(hir, false)` → candidate wrapper chain → `collect_candidate_world_scoped_v1` | R274-E024, R275R3-E003/E004/E005/E006 | World collection and seal return `Ok`; however this public entry forwards `candidate_values=false`. It therefore does not establish the candidate-source branch. |
| Candidate world collector after wrapper forwarding | feature-gated candidate branch; for each eligible source, `batch.emit_candidate_source(...)`; then collection seal/static-SCC return | R274-E024, R275R3-E005/E006, R274-E025 | Required feature and flags are enabled, source/root/receiver guards pass, emission and seal return normally. The caller and flag provenance must be independently established; the callsite alone does not establish production reachability. |

## Entry and flag provenance gate

The source-owner index records the visible ordinary production wrapper and its
argument forwarding, all indexed candidate-source callsites, and known
`candidate_values=true, candidate_graph_effects=true` test-call locators as
excluded metadata. Test bodies, assertions, helpers and outcomes are not
source evidence. A textual search result or absence does not prove production
unreachability.

Before authorizing the main trial, readiness must exhibit an actual production
entry that forwards the required candidate flags through the wrapper chain to
the guarded source-emission branch and collection seal/static-SCC return. The
visible ordinary `Collection::collect` path supplies `false`; it cannot serve
as that positive route. If the authenticated source-owner index and bounded
view do not establish a positive production route, STOP and report that exact
entry/configuration seam. Do not replace the goal with a hypothetical private
constructor invocation.
