# R146: finite source admission and candidate entrance

Status: **candidate source evidence; independent outcome review pending**.
Author: `/root/r146_proof`; no descendants or coauthors of this artifact.
Luna authored the separate execution observation. This author cannot independently
certify the combined result.

## Authority, scope and result

Contract: `tasks/agent-loop/sprints/source-admission-observation-20261020-r146-rev3.md`,
SHA-256 `3b6c24726ac4fe51b96d605d8a260d4a02023e009b244178f528f148ccd8171b`.
Luna activated it at `d95030bb2e202f5c83b601bb06a1c2baf6263428`.
Baseline: `f6e59e42bcfcfb3c13a0c511c63bcf9d0390005d`; complete baseline tree:
`38f79bf7203e9766ac26b5876d7569fc84dbc842`.

The fixed source is the unchanged tracked file
`tools/inference-playground/examples/nested-recursion.yu`, SHA-256
`51aac3016d9000a1cc0e34e2050ca73f4aa44112f461ec6237195b0d65d89906`:

```yu
my loop x = { my helper y = loop y; helper x }
```

**Result:** Luna's single invocation observed this input prepared by the existing
experimental inference path. The static audit below identifies the matching
syntax, HIR carrier and ordinary candidate entrance. It does not derive a selected
raw bound history, complete a consumer lineage, or prove a compiler theorem.

`R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1`, R71 and the original Simple-sub A/B,
source/native, evaluator/sample compatibility and production obligations remain
OPEN with their existing quantifiers and domains. The application to those parents
is a finite source entrance for subsequent research, not parent closure.

## Frozen evidence and scope interpretation

This worker checked all 19 live direct hashes against the contract and checked
the contract hash. Baseline object comparison and complete code-tree parity are
Luna's activation receipt; this worker performed no Git operation. In addition
to its direct hashes, rev3 pins the complete baseline code snapshot and requires
unchanged `Cargo.toml`, `Cargo.lock`, `crates/` and `tools/inference-playground/`.
Luna explicitly confirmed that static reads of the source owners below fall
inside that frozen tree scope. They are not newly admitted external dependencies.

An initial concern that `header.rs` lacked a direct manifest row was withdrawn
after that clarification. It is not an unresolved source-admission premise.
No source outside the frozen code roots was needed for this finite owner audit.

Luna's observation is
`notes/progress/2026-10-20-r146-admission-observation.txt`, SHA-256
`8cc78c35af7c09741c84be67b0fbda1862609fcde24b706cfb942e21f82e6548`;
this worker independently checked the record's live hash and read its contents.
It records exit 0, an intrusion report, 4.626 seconds, no limit trigger,
stdout 4,213 bytes (SHA-256
`57657eab318e9b4ae7ff4c15c7fc1e971be235a37237a7ff2c0970e2968924d8`)
and stderr 5,445 bytes (SHA-256
`230e7898768791d7c61341fc80502a7bd0f7542dedecec3e45e88dd68eb4006f`).
Those process facts are Luna's evidence, not an execution by this worker.

## Source constructors and entrance

1. `tools/inference-playground/src/main.rs::run` handles `--intrusion` and the
   source path. With no `--run` and no `--scoped-experiment`, it calls
   `infer_with_scoped_experiment(source, name, true, false)`. The inference
   entry calls `prepare` before graph export and intrusion rendering.
2. `lib.rs::prepare` obtains one `Arc<SourceText>`, runs `scan_header` and
   `SyntaxEnvironment::empty`, then `parse_file`. The pinned syntax wrapper
   delegates header discovery through `header::discover_header` and
   `cursor::discover_header` to `header::discover_header_with_cursor`.
   The initial `my loop` is a binding rather than a use/operator header, so
   the header loop stops at the first nonheader. `SyntaxEnvironment::empty`
   supplies no imported dynamic operators; `effective_full_parse_operators`
   builds the effective table from imported and discovered local entries.
3. `full_parse.rs::parse_file` calls `cursor::parse_root`, which starts Root
   and calls `root_statement::parse_root_statements`.
   `statement::classify_statement_item_lexical` selects Binding for a binding visibility
   and `binding_statement_selected_lexical`; the ordinary `loop`/`helper`
   followers use its ordinary-name branch. The binding constructor emits
   BindingStatement, BindingHeader and BindingBody around the target and `=`.
   `pattern/mod.rs` emits PatternMlApplicationTail for the spaced formal.
   The corresponding HIR `plain_binding_header` admits one identifier formal
   for each of `loop x` and `helper y`.
4. `expression/operator_chain.rs::append_nud` dispatches `{` through its braced
   expression owner; `statement::braced_statement_block_with_recovery_normalized`
   constructs BracedStatementBlockExpression and its statement sequence.
   The nested `my helper` is a BindingStatement, followed by the semicolon
   separator and final `helper x` expression. Identifier nud construction
   and `ml_argument` construct the two spaced applications `loop y` and
   `helper x`; `ml_argument` emits MlArgument with the argument expression.
   This is a source-constructor map, not an exhaustive proof of the parser,
   lexer, recovery machinery or external Rowan implementation.
5. `prepare` rejects nonempty syntax diagnostics before HIR lowering. With
   empty diagnostics it calls `shadow::lower_module_with_local_source`;
   the wrapper calls `module::lower_module_with_local_source`, which retains
   parse-branded source identities and enables local-source formation.
   Module lowering plans roots and builds the namespace before lowering
   binding bodies. Its binding lowering calls `local_source::form` and
   stores the carrier under the definition root.
6. `local_source::form` constructs the root Lambda for parameter `x` and its
   body work. `Builder::block` requires the final OperatorChain, records
   the private `helper` binding and its parameter `y`, and schedules its
   initializer before the final expression. `Work::Initializer` builds
   the helper Lambda; `Work::Publish` restores the initializer scope and
   publishes the local binding. `Builder::expression` turns MlArgument
   tails into Apply and identifiers into Name.
   Its lexical-first/namespace-second resolution gives `x` and `y` their
   respective Parameter identities, `loop` its unique ModuleDef identity,
   and the final `helper` its Local identity. The module/local/parameter
   identities retain their distinct owners; no equality is inferred from
   matching spellings alone.
7. `CandidateInference::solve` calls `solve_mode(hir, false, false)`.
   Its local-source preflight rejects unresolved/ambiguous names and checks
   any annotations. This input's formals are unannotated and the source
   has no operation/Catch or annotation form. The scoped-only internal-use
   refusal is guarded by `scoped` and is not selected here.
   Collection calls `ConstraintBatch::collect_candidate_mode_scoped_v1`
   and, for the retained source, `emit_candidate_source`.
8. `candidate_source.rs` retains Lambda recipes, Apply relations and source
   inputs, Block final-expression Group relations, local Install actions,
   Module actions for `loop`, and Local actions for `helper`. Its traversal
   records local initializer level one greater than the enclosing block
   level and retains that boundary for installation. `execute_candidate_action`
   dispatches these actions; `candidate_scheme.rs::route_candidate_local_run`
   captures the installed graph and prepares a fresh use. Its
   `step_candidate_local_use` restores retained bounds before linking the
   fresh root to the local occurrence target. `run_candidate` executes and
   finishes candidate observations. These are actual owner paths, not a
   proof that each abstract branch in those owners executes for this input.

The successful report can only be reached after `prepare` returns: syntax
diagnostics empty, HIR lowering successful, ordinary candidate solving successful,
and `candidate_conflicts()` empty. The observed invocation therefore supplies
finite operational admission evidence at these caller gates. This inference
uses both the observation and pinned caller logic; it does not replace the
constructor audit with CLI success.

## Retained report and precise remaining premise

The report records two same-SCC symbolic events: module `loop` to local `helper`
at bytes 43..44, and local `helper` to module `loop` at bytes 33..34. Its four
parent/copy pairs retain differing raw ordinals with equal reported
representatives, extrusion occurrence 1, target level 1 and source event `[1]`.
`render.rs::intrusion_into` obtains these from `intrusion_observation().events()`
and `.parents()`. It labels the result retained state, not a chronological trace.
The printed word `consumed` concerns the reported pending state and does not
authenticate a relation consumer, provider, witness or runtime handling event.

The next static entrance is `lib.rs`'s typed value-pair drain, whose
nonrow/row case calls `candidate_extrude` at the row's level.
`candidate_extrusion.rs::candidate_extrude` selects one-sided row bounds,
canonicalizes child endpoints for memoization, and retains the source
`BoundKey(endpoint, polarity, bound)` in `Work::Bound`. That arm calls
`candidate_insert_copied_bound` and `candidate_transfer_bound_origins`.
The latter owner is `candidate_effect.rs`.

No specific pre-extrusion slot or `Work::Bound` from this invocation was
identified. Equal final representatives and retained parent rows do not supply
all raw preimages, their mutation order or the selected bound's relation-local
residual/discharge, provider/attachment or scoped payload. No raw-to-canonical
consumer-adequacy premise is discharged by this packet. The construction/consumer
history is the next exact evidence obligation for Luna to allocate; this audit
ends at the finite entrance required by R146.

Stable TODO `R146-AUTHENTIC-RAW-BOUND-HISTORY-1`: preserve the accepted source
and snapshot; identify one actual ordinary drain item, selected raw bound and
`Work::Bound`, all relevant raw preimages, and its relation consumer through
`candidate_insert_copied_bound`/`candidate_transfer_bound_origins`. Falsifier:
the proposed item is absent from actual source execution, comes from a different
extrusion/restoration arm, or loses the required source/consumer lineage after
canonicalization. No second execution, instrumentation or code repair is granted
by this TODO.

R145's pre-observation absence of an admitted source history remains a correct
historical statement. The existing `candidate_graph_row_hashing_uses_merged_representatives`
test is a useful locator for this source's retained merge; it was inspected,
not executed, and is not reused as raw-slot or consumer proof.

## Additional inspected owner hashes within the frozen tree

```text
cd3791144704226f67a05ae3d39aff9b42f4380073b3e9f9817951a493bce5ad  crates/yu-syntax/src/header.rs
3f1e2c97c49318e02c595aa739bfb48532f7631d38afaaac4d8dfca6142cb973  crates/yu-syntax/src/syntax_environment.rs
f1a5bd012f064d414d476acbc326c6a9804dc8128bf2e4f1800acb718a7d423b  crates/yu-syntax/src/operator_compilation.rs
f08aae49fcf048ad11890def7ef9cadab56825a63b8d87db44821a792fe9b142  crates/yu-syntax/src/cursor.rs
c6d1dc49625d1687ff0dae8f6808f4c97c3f78398aae3bc061c44b6fc9661626  crates/yu-syntax/src/root_statement.rs
fe8ba4e144b0c3ea5c8f451dddea42f718e9c3087aa77bb81447c61a9d213797  crates/yu-syntax/src/statement.rs
eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544  crates/yu-syntax/src/declaration/binding.rs
81db2aec4774f2cd1ddc12b64fd9206cf41cdf3eee00ed740676ffc6d7fc5669  crates/yu-syntax/src/expression/operator_chain.rs
1b608422c93ce0f6947125a9b1ea88314a48b3a5e45030ed23e5154492ad7883  crates/yu-syntax/src/pattern/mod.rs
2e64dc8781189b4da21c30f4d1b3208aaef48ca247cae55fb7e77e68b5857850  crates/yu-solver/src/candidate_scheme.rs
86dba831366995d4c36e2446c9b8e6847f7bff524d5e7e7b6d12d02ff337fc66  tools/inference-playground/src/render.rs
```

Checks: bounded read-only source commands and SHA-256 comparisons only.
No worker build, tests, CLI invocation, runtime, Git, descendants or scratch
files. Exact outputs are this theory and the assignment handoff. Requested
routing: prover default/high (normally configured Sol/high); effective observed
model/effort UNKNOWN. Launch receipt: `2026-10-20 02:00:54 UTC`; 600-second
reservation, no renewal. Final handoff/message records cessation and elapsed time.
Independent final compiler/source review and Luna adjudication remain pending.
