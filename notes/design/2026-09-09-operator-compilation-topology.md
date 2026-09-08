# Operator compilation topology

Status: Authoritative; private construction complete

Date: 2026-09-09

Approved-by: user, through the explicit request to reconstruct parser
responsibilities rather than mechanically rename temporary paths.
Reviewed-by: scoped read-only topology and split preflight audits.

Scope: separate source-header operator conversion, imported/local merge, and
conflict collection from the immutable operator catalogue. `operator_table.rs`
continues to own declarations, fixities, sites, binding powers, mechanical
merge/build, frozen tries, and source matching. A new
`operator_compilation.rs` owns conversion from `HeaderOperator`, imported-table
traversal, strict test compilation, recovering full-parse compilation, and its
conflict product. `full_parse.rs`, `syntax_diagnostic.rs`, and test-only
`syntax_environment.rs` imports follow that ownership. Public root exports,
syntax acceptance, CST, recovery records, diagnostic order/content, and test
contracts remain unchanged.

Authority: the user's current topology direction; the one-owner/one-reason
rule in `docs/yulang3-architecture.md` §12.1; and the direct-owner direction
in `2026-09-09-syntax-phase-topology.md`.

The existing flow stays one-way:

```text
declaration/operator_header → operator_compilation → operator_table
lexical/operator_scan       → operator_table
expression/operator_chain   → lexical/operator_scan
full_parse                  → operator_compilation → source_file
```

`operator_table` must not import `HeaderOperator` or the compilation owner,
including test-only paths. The split moves every header adapter: header binding
power conversion, `from_header_operator`, `from_header_operators`, and
imported-table seeding. The compilation owner may use narrowly crate-private
declaration constructors, builder operations, and immutable entry/site access;
it must not expose table vectors, tries, mutable fixity sites, or a broader
public API.

Keep direct table construction, fixity, duplicate-build-error, filtered-trie,
and source-traversal tests with `operator_table`. Move header conversion and
full-parse merge/conflict tests with compilation. Preserve imported-first
precedence, local source order, fixed capability traversal order, conflict
ranges/origins, later non-conflicting capability retention, and filtered-trie
freezing. No scanner/Pratt/header-declaration merge, generic `parser` owner,
or compatibility forwarding module is permitted.

Before closure run scoped table/compilation, syntax-environment/diagnostic,
full-parse, and public two-phase controls, then package check, format, and
diff. Measurement budget: zero samples/processes.

Construction completed 2026-09-09. M2 split preflight and independent delta
review found no defect. Scoped table/compilation, syntax-environment,
diagnostic, full-parse, and public two-phase controls passed 31 tests with one
existing manual measurement harness ignored; package check, format, and diff
passed. Benchmark use: zero samples/processes.
