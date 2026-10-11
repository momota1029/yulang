# Exact odd/even source admission audit

Status: frozen, unreviewed research checkpoint; static source characterization
Baseline: `e001972b31b7143c5f8318c48ebb47948d089fca`
Method: parser/HIR/private source-constructor crosswalk; no execution
Lease: this note only; no production implementation authority

## Objective and governing premises

Trace the user's exact source, without substituting a brace-block example:

```yu
my odd n =
    my even n = if n <= 0 { true } else odd(n - 1)
    even(n - 1)
```

The governing sections of
[parent-copy SCC intrusion](../design/2026-10-10-parent-copy-scc-intrusion.md)
are “Value-reference SCC clarification”, “Apply-result source-fragment
ownership”, “Nested Apply membership”, “Definition-root Value ownership”, and
“Retained boundary”. The integrated receipts for
[definition roots](../../questions/2026-10-12-definition-root-value-reference-forwarding/receipt.md)
and [nested Apply](../../questions/2026-10-12-nested-apply-reference-membership/receipt.md)
fix source incidence. The root rule assigns nested initializer references to
the nested declaration's root. These accepted meanings are inputs here;
neither an AST identity nor a comparison creates a native SCC edge.
The [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1, 3 and “Authority and integration” preserve the source/proof bridge as a
separate obligation. This audit does not reinterpret these decisions.

## Crosswalk and first missing step

| Source feature | Actual constructor or consumer at this baseline | Admission consequence |
| --- | --- | --- |
| Outer `my odd n =` and newline body | `yu-syntax/src/declaration/binding.rs:185,317`; `statement.rs:474` emits `BindingStatement → BindingBody → IndentedStatementBlock` and uses the ordinary statement sequence | The indented body has a distinct CST kind from an inline operator chain. |
| Nested `my even n = ...` | The same syntax binding constructor is available inside that statement sequence | Syntax nesting does not itself create an HIR local binder or Value row. |
| `if ... { true } else ...` | `expression/operator_chain.rs:285` selects `if_nud_normalized`; `expression/if_expr.rs:33,191,327` owns `IfExpression`, condition and arms | A syntax constructor exists. `LocalSourceForm` has no If variant; `local_source.rs:477–695` has no If lowering case. |
| `<=` and `-` | `full_parse.rs:317` builds the selected operator table; `lexical/operator_scan.rs:30` selects only entries in that table; `expression/operator_chain.rs:898` emits dynamic operator uses | Exact successful parsing requires an appropriate selected syntax environment. The supplied text declares neither operator. `SyntaxEnvironment::empty()` installs none. No such environment was supplied or executed in this packet. |
| `true` | `lexical/lexer.rs:685,705`; absent a selected dynamic operator declaration, it is an Identifier, not a dedicated Bool literal | `LocalSourceForm` has Integer/Unit but no Bool constructor; ordinary lexical Name lookup has no implicit `true` binder in the inspected local/module namespace. This does not decide language Bool meaning. |
| `odd(...)`, `even(...)` | CST CallTail; `local_source.rs:519–593` can retain Apply with callee/argument indexes; associated `HirExpr::Apply` in `yu-hir/src/lib.rs:76` separately denotes a dynamic operator application | Callable source retention exists only for admitted source operands. The exact program never reaches those retained Apply constructors through the inspected LocalSource route. |
| Ordinary HIR body | `yu-hir/src/module.rs:1597` explicitly handles an `IndentedStatementBlock` child by returning `ResolvedExpr::Error` with `UnsupportedExpression`; outer parameters are wrapped in Lambda at `:1473` | HIR availability is not successful semantic body admission. Nested `even`, its Names and its calls are not lowered by this path. |
| Private source carrier | `module.rs:1412` calls `local_source::form`; `local_source.rs:266` rejects recovery; `:251` requires the BindingBody's only child to be `OperatorChain` | Even with an operator environment that yields recovery-free syntax, the exact indented body fails `StructuralProjection` before the carrier is published. If syntax has recovery, the earlier `:266` guard fails first. |

Paths in the table are relative to `crates/`. There is no separate complete
AST handoff in this inspected Y3 route: parser output is Rowan CST; the public
`AssociatedChains`/`HirExpr` product explicitly calls itself pre-HIR and has no
declaration/name/type model (`yu-hir/src/lib.rs:20`). It cannot supply the
missing nested-definition lowering.

The decisive obstruction is therefore **indented BindingBody admission into
LocalSource**, with syntax-environment/recovery as a preceding conditional
boundary. Ordinary HIR explicitly substitutes an error body; private HIR
fails structural projection. No successful exact-source route was established.
The static rejection witness `my x =\n  1` removes recursion, operators,
`if`, and local declarations while retaining that same body-shape mismatch.
This witness was not run and is not a counterexample to the selected language
semantics or intrusion theorem.

Even replacing indentation with braces would leave separate unsupported
steps: LocalSource accepts only call/ML/colon/ascription tails, not
`InfixOperatorUse` (`local_source.rs:519`), and rejects `IfExpression` in its
default branch (`:694`). This is an obstruction inventory, not permission to
rewrite the user's source or narrow supported ordinary inference.

## Conditional binder-owner and level route

The following describes existing constructors on an admitted carrier. It does
not assert that the exact text reaches them:

- Module namespace registration includes `odd` before body lowering
  (`module.rs:1322`). LocalSource Name lookup checks its lexical `latest` map
  before that namespace (`local_source.rs:633`). Thus a retained inner `odd`
  Name would resolve to the module DefId when unshadowed.
- `block()` creates local `HirLocalId { owner: outer DefinitionRootId,
  ordinal }`, a separate initializer index, and `LocalInitializer(local)`
  scope. It records each local parameter's owner in `local_parameter_owners`
  (`local_source.rs:729–831`). The ID's outer artifact owner is not a claim
  that the outer declaration semantically owns the inner initializer.
- During an admitted function initializer, a temporary self binder is pushed,
  then its parameters; the parameter `n` therefore shadows the outer `n`.
  Publish restores those temporary entries and installs `even` for the final
  expression (`local_source.rs:338–386`). These constructors retain enough
  local identity to distinguish the two `n` binders on supported forms.
- `candidate_source.rs:254` starts its source body at inference level 1;
  Lambda, Apply and Group preserve that level (`:265–287`); Block visits each
  initializer at `level + 1` while its final expression remains at the
  block level (`:288–306`), then installs the local at that block boundary.
  Hence an admitted outer Lambda/Block route would place outer `n` and final
  `even` use at 1, and local initializer Lambda/inner `n` at 2. The numbers
  are the candidate planner's rules, not measured levels for this program.
- Name planning uses `PendingDefinitionUse`, formal endpoints, active-local
  links, or published-local actions (`candidate_source.rs:369–392`). Apply
  planning retains a `CandidateRelation::Apply` and `ApplySourceInput`
  (`:394–411`). The module root handoff at `:477–493` is an Action::Link.
  These are constraint/Call planning facts. They do not establish the selected
  definition-root or Apply Name-incidence SCC edges. This packet did not audit
  native SCC emission, transport, extrusion or intrusion qualification.

Under the approved source-owner rule, the reference to `odd` in the inner
initializer belongs to `even`, and the final reference to `even` belongs to
`odd`. Applying that rule to admitted/resolved source is distinct from proving
this compiler constructs it. No root is identified with a Lambda/Block/Apply
row in this audit.

## Dependency snapshot and checks

Read-only blob-hash comparison against the full pinned SHA found **no changed
dependencies** in 26 named inputs: the two governing design files; the two
question/draft/answer/receipt bundles; syntax binding, statement, If, operator
chain, lexer, operator scan/table/compilation/environment/full-parse files;
HIR lib/module/LocalSource/shadow files; solver candidate_source/lib files.
Representative SHA-256 values:

| Input | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `fd07ecc76e9df0b1937f72e74ce4a35b982b51031b04022672228e307d03615c` |
| `crates/yu-syntax/src/declaration/binding.rs` | `eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544` |
| `crates/yu-hir/src/module.rs` | `943dcab6440ffb70061f08641afa13fa8b36c5689a326d07288b9593e17ba8f5` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |

Commands: focused `rg`/`sed` source reads, `sha256sum`, and a read-only loop
comparing `git hash-object PATH` to `git rev-parse BASELINE:PATH`; no mismatch
output. Markdown link targets and trailing whitespace were checked after
writing. Existing parser/local-self-recursion assertions were read, not run.
No tests, builds, Oracle, randomized search, seeds/ranges, mutations, or model
checker were used. There is no independent executable oracle or shared
transition-model validation claim. Searches for nonexistent `yu-parser` and
`spec/` paths failed and were redirected to actual `yu-syntax`/HIR source;
no standalone spec directory was inspected.

Resource envelope: 30-minute wall-time allocation; lightweight source reads
only, at most three simultaneous read subprocesses, zero heavyweight
processes. CPU time and peak RAM were not measured. All unrelated work was
preserved. No Git mutation, child delegation or interactive user question occurred.

Unverified scope: actual exact-source CST/diagnostics under a selected operator
environment; runtime admission and inference; public F5/core correspondence;
native source-reference graph emission/transport; qualifying parent/copy
intrusion; soundness and principality. This note establishes no gate closure
and has no independent review.

Recommended next action: primary assigns one bounded source-admission packet
at the indented BindingBody/LocalSource constructor seam, with the required
If/operator/builtin dependencies explicit, before using this exact example as
native SCC or parent/copy execution evidence.

## Commit packet

- Exact leased path: `notes/progress/2026-10-12-odd-even-source-admission-audit.md`.
- Baseline: `e001972b31b7143c5f8318c48ebb47948d089fca`; changed dependency hashes: none.
- Review: frozen, unreviewed research-only characterization; no authority or
  theorem/implementation status promotion.
- Checks already run: focused source reads, pinned dependency blob equality,
  SHA-256 snapshot, Markdown link-target existence and trailing-whitespace checks.
- Proposed message: `research: record exact odd/even source admission boundary`.
- Shared deltas left to primary/curator: link this audit from the owning source
  gate in `tasks/current.md`; distinguish the accepted root-owner meaning from
  missing exact-source admission in the active theory record. No shared path
  was edited and no parent gate is marked complete.
