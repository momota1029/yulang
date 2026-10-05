# Current SCC definition-use collection coverage

Date: 2026-10-06
Status: reviewed bounded source-to-plan correspondence; successor coverage remains open
Baseline: `2eac534be08798c2d9ce34f2f974b31ff610b374`
Implementation authority: none

## Result

For the current production lowering envelope, collection inventories every
admitted definition and every resolved module-definition occurrence in the
supported body positions before it constructs the static SCC plan. The claim
is limited to that narrow envelope: identifier binding headers with zero or
one identifier parameter, and a direct integer/name atom body or retained
Error, optionally wrapped in one outer Lambda. It does not establish source
coverage for a broader successor language.

## Lowered source shape

`ResolvedExpr` has `Lambda`, `Integer`, `Name`, and `Error`
(`crates/yu-hir/src/module.rs:426–449`). Headers admit an identifier target
and optionally one identifier parameter (`:1471–1516`); lowering places the
body under at most one outer Lambda (`:1167–1207`). Successful lowered bodies
are direct integer or name atoms. A name can resolve to the local parameter or
to the module definition namespace; ambiguous, unresolved, and erroneous
bodies are retained as failures rather than module-use arcs
(`crates/yu-hir/src/lib.rs:136–193`, `module.rs:1419–1465`).

Module lowering builds the complete direct-root definition namespace before
lowering bodies (`module.rs:803–841,1088–1110`). Unsupported headers, root
items, multiple body children, and non-atom chains do not add supported
definition-use forms (`:1037–1066,1305–1387`). Nested-lambda capability is not
inferred from the recursive `Lambda.body` field; that field alone does not
show that arbitrary nested source bodies are admitted.

## Collection and static plan

`ConstraintBatch::collect` visits all HIR items and creates a definition
record for each binding, including bodies that lower to errors
(`crates/yu-solver/src/lib.rs:876–1002`). Within the supported shape it checks
both possible module-reference positions: the whole non-function binding body
and the immediate body of its one outer Lambda (`:1008–1076`). A module use is
created only for a resolved name targeting a module definition. Parameter
references do not create definition-use arcs; ambiguous/unresolved names and
Error bodies remain failed inputs.

After item collection, every pending use is resolved against the completed
definition endpoint table, and exactly one `SccPlan` is built before the batch
is returned (`:1085–1140,1218–1232`). `SccPlan::build` validates and groups
the supplied definition/use records into internal and incoming component
lists (`crates/yu-solver/src/scc.rs:212–296,416–451`), then exposes the plan
through read-only queries (`:658–738`). Its guarantee is completeness relative
to supplied slices; it cannot discover an occurrence omitted by an upstream
collector. The current executor consumes the frozen component order and use
lists (`yu-solver/src/lib.rs:12973–13006,13925–13980`).

## Distinct update owners and authority

Live value/effect row edges and their replay update constraint facts and
enqueue comparisons. They are not additions to the definition-use pair of
`(parent,target)` identities (`crates/yu-solver/src/lib.rs:3700–3718,
12073–12147,10903–10922,13985–14007`). This audit found no basis to treat
finite row-bound growth as discovery of a new SCC dependency.

The Authoritative F0–F2 foundation requires complete collection before the
static plan is sealed and excludes dependencies first discovered while solving;
it requires a later approved readiness/incremental owner or recollection before
admitting such arcs (`notes/design/2026-09-20-constraint-collection-scc-foundation-draft.md`,
“Oracle invariant,” “Lightweight-port boundary,” and “Phase and fact
ownership”). Those lifecycle clauses do not certify broader successor source
coverage or termination of generated type/scheme work.

## Review and limits

Independent `spec_auditor` review found no blocking or major issue. Its minor
wording correction is incorporated: the source envelope includes local
parameter-resolved names and retained failed bodies, while only successfully
resolved module-definition occurrences become module-use arcs. “Complete” is
always relative to the current supported lowering envelope and exact collector
entrypoint.

This is not a parser-wide acceptance audit, a theorem for other HIR entrypoints,
a source adequacy result for the successor, or a repository-wide claim that no
other path adds dependencies. The review read relevant test contracts as
corroboration; no tests, builds, or probes were run.

Inspected: focused current HIR lowering and association, solver collection and
execution, `SccPlan`, and the named Authoritative lifecycle clauses. No code was
edited; no production implementation authority follows.
