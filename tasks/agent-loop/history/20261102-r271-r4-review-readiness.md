# R271-r4 clean review source-range readiness

The two frozen artifacts and all manifest pins were verified after Sol STOP. This record authorizes the listed production ranges only. Inherited exact hashes remain in R271-r2 contract/readiness (139 local paths) and R271-r3 readiness (68 additive rows); those tables also pin 302 distinct direct/inherited paths. Reviewer may hash the exact paths and compare cached archive members, but body reads are limited below.

## Exact production read ranges

| Path | Allowed production lines/symbols | Hard exclusion |
|---|---|---|
| `crates/chasa-recover/src/input.rs` | only `In::token`, `In::checkpoint/rollback`, and `Input for &str` mark/rollback symbols | no unrelated parser/test code |
| `crates/chasa-recover/src/parser.rs` | `token` and `Token::run_once` lines 132–172 only | hard EOF 434; tests begin 435 |
| `crates/yu-syntax/src/cursor.rs` | `LexRecover::mark/rollback` lines 35–42; `SyntaxIn::token` lines 60–83; `parse_root` lines 85–113 | no test-only struct fields/imports |
| `unicode-ident-1.0.24/src/lib.rs` | `is_xid_start/is_xid_continue` ASCII dispatch lines 261–274 | only pinned source |
| `unicode-ident-1.0.24/src/tables.rs` | `ASCII_START/ASCII_CONTINUE` lines 14–15 | no other tables |
| `crates/yu-syntax/src/lexical/lexer.rs` | `scan_identifier` 712–750; `source_identifier` 751–774; `source_declaration_head` 775–786; `scan_exact_word` 822–855; identifier continue/suffix 910–917 | do not read other lexer tests/helpers |
| `crates/yu-syntax/src/header.rs` | entire production `header.rs` 1–444, consisting only of header discovery/selection code | production symbols only |
| `crates/yu-syntax/src/full_parse.rs` | `parse_file` lines 345–371 only | hard cap 371; tests begin 372 |
| `crates/yu-syntax/src/root_statement.rs` | `parse_root_statements` 30–56; `root_statement_sequence` and its production helpers 106–419 | hard cap 419; no cfg(test) functions at 59–104 |
| `crates/yu-syntax/src/declaration/binding.rs` | entire production `binding.rs` lines 1–565; no test cfg body exists in this file | production symbols only |
| `crates/yu-syntax/src/statement.rs` | `braced_statement_block_with_recovery_normalized`/`statement_sequence_normalized` lines 750–890 only | production symbols only; no test module/body |
| `crates/yu-hir/src/shadow.rs` | `lower_module_with_local_source` lines 889–895 | exact symbol only |
| `crates/yu-hir/src/module.rs` | `lower_module_with_local_source`, `plan_root`, `plain_binding_header`, `lower_plan`, local-source retain/return path | hard cap 4747; tests begin 4748 |
| `crates/yu-hir/src/module/local_source.rs` | local-source builder types and `form`/block/lambda/apply/name/binding construction owners | hard cap 2832; tests begin 2836; NEVER read beyond 2832 |
| `crates/yu-solver/src/candidate_source.rs` | production production `emit_candidate_source`/source-retention methods lines 1043–2265 | exact fixture input/constructor arguments only at 2528–2537; never inspect line 2538 or adjacent assertions |
| `crates/yu-solver/src/candidate_value_graph.rs` | production graph methods lines 1–415, especially `retain_source`, `seal`, `qualifies` | hard cap 415; tests begin 416 |
| `crates/yu-solver/src/candidate_context.rs` | `candidate_context_seed` lines 3793–3862 | exact production symbol only |
| `crates/yu-solver/src/candidate_intrusion.rs` | 305–343, 346–349, 352–421 for `retain_extrusion_parent`, `finish_candidate_extrusion`, `recapture_candidate_extrusion` | lines 344–345 and 350–351 are cfg(test) and excluded |
| `crates/yu-solver/src/shadow_apply.rs` | source Apply execution lines 4302–4396 | hard cap 4396; cfg(test) begins 4397 |
| cached `rowan-0.15.17` source | only `GreenNodeBuilder::{new,token,start_node,finish_node,finish}`, `GreenNode::new`, `NodeCache::{token,node}`, green child traversal API and called text-size symbols | exact files already pinned by r3 readiness; no tests/unsafe internals beyond these symbols |
| cached `text-size-1.1.1` source | only `TextSize`/`TextRange` constructors, arithmetic and conversions used for the 87-byte fixture | exact files already pinned by r3 readiness |

The test-source exception grants only the fixture's exact input and constructor arguments, not its following `.unwrap`, assertions or downstream expected values. Each shell read must name one listed file and remain within its listed range; never combine adjacent ranges across a hard cap. Do not use bulk `sed` or search output that prints excluded lines. A required unlisted symbol/range is a stop boundary; do not expand authority.

## Fixed verification questions

1. Independently verify archive hashes and every extracted package member used by this trace; the previous partial review did not certify correspondence.
2. Independently derive finite ASCII predicate values and cursor rollback for this exact fixture.
3. Reconstruct the accepted parse/CST/HIR carrier only from permitted production ranges and the exact fixture string.
4. Reconstruct HIR occurrence identities/scopes, all 19 graph vertices/23 edges/three events, both seal guards, same-level SCCs, raw SCC comparison and actual `qualifies` consumers.
5. State exactly which claims are verified conditionally, which are accepted-source qualified, and why actual reached Parent/actual polar pair/independent `Need_D`/R71 remain open unless directly constructed. No approved-clause violation or parent counterexample follows merely from the raw/native difference.
