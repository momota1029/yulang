# R132 complementary source audit — frozen handoff revision 1

Assignment: R132 source/falsifier; contract rev1 SHA-256
`5335bbb4e6d0bdcd1f0e46e947990d1e61cdde1e23e53045abbe8e0760e5efe6`.
Baseline supplied by primary: `9fab033a27390ac12f7553a9d6af11a82ad66e1b`.
Worker/current session: `/root/r132_source_audit`, actual NEW_TASK received from
`/root`; requested Sol/high. Effective model and effort: UNKNOWN, because no
runtime metadata authenticates either. No descendants or Git commands.
Outcome class: **conditional source/native evidence**, unreviewed producer
artifact. No invalidating source-qualified counterexample found in this bounded
inspection. This is not independent review of the prover's output.

## Objective, authority and method

Independently inspect exact sample spellings and real source/inference/runtime
owners for identity-use contamination, recursion/cache misrouting, and a source
shape outside the existing envelope. Governing scope: frozen contract §§Fixed
sample and oracle, Existing authority and gate, Original outcome and success
evidence, and Complementary source/falsifier lane; inference principles §§1,
1.1, 3 and 5; research-playground Direction/Boundaries; module-expression owner
§§2–3 (expression uses consume published interfaces; ordered roots discard
expression values; selected-definition observation remains unchanged).
Rules read: AGENTS.md, AGENTS.pre-sprint.md, research-lab and its preserved
baseline, design-authority, git-concurrency, goal-driven-sprints, sprint skill,
current.json and handoff README. No language meaning was selected or changed.

Method: read-only source inspection, byte extraction/hash calculation, and an
explicit conditional derivation below. No executable semantic model, tests,
builds, compiler invocation, formatter, Yulang CLI, mutations or random search.

## Frozen dependencies

These owner hashes were checked and equal the contract pins:

| Path | SHA-256 |
|---|---|
| `tools/inference-playground/src/lib.rs` | `a0769f77feac552304f0516b0742637f51660c0bb8bf9391d18ae0f9de5e2473` |
| `tools/inference-playground/src/runtime/program.rs` | `28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d` |
| `tools/inference-playground/src/runtime/machine.rs` | `4fb918732047f61184bc8f89b829bde68a8d1e6649a24d02640ec14500ae0acd` |
| `apps/yulang-wasm/src/lib.rs` | `2fc9feb353b3130c4efc888270cec14cba8b2bbcc2fca03d3780c676e0468f8a` |
| `crates/yu-hir/src/module/local_source.rs` | `d7c02fb7ba08fa389229064c6c12504a237fbd15687858431738cb2b2939a5ce` |
| `crates/yu-hir/src/shadow.rs` | `ae5f40a9b1d34d08938eb23b8bc3d1756411d146b5c83ba73b7294f5d332a654` |
| `crates/yu-solver/src/candidate_source.rs` | `cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7` |
| `crates/yu-solver/src/candidate_scheme.rs` | `2e64dc8781189b4da21c30f4d1b3208aaef48ca247cae55fb7e77e68b5857850` |

External read-only sample and Yulang2 WASM oracle sources match respectively
`be076ab26780de6a5f6b75b75a11abec351114ec5fa3b6edfcbacd15e02fb284` and
`41ac039cb915effac5985456ef9c9875d5ad6ee1afec69c91587cd5633cc5b82`.
Authority hashes: inference principles
`7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`;
research playground `66c38775ddfbbf0823a9fc92d44a33fd7e12858224d6eae1552f647461e4bdac`;
module-expression owner `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5`;
tool README `681af715b51d236cabd2aaf481eea43abd36f114a841d49d3bcd520ef2c85f8c`.

## Exact source and byte discrimination

Sample lines 46–53 contain `my identity x = x`, three applications to `7`,
`true`, and `"ok"`, then three bare result names. Lines 60–63 contain
`my countdown flag = if flag { 8 } else { countdown true }`, the application
`our countdown_result = countdown false`, and its bare result name. There is
no arithmetic decrement, annotation, standard import or hidden `main` here.

Read-only Python byte extraction found that the expected fixture hash
`f10e7e57cdfc165436a89326c9f069f19aa0afd24cea80b2b570463fcc553487`
is exactly **388 bytes**, obtained from the two blocks excluding their final
LF, with **three LF bytes between blocks and two LF bytes at the end**, and
no leading LF. This detail was sent to the primary before submission.
One blank line between blocks and one final LF instead gives 386 bytes and
`7a2768319c9cd3531eae2a221c71899581566cbf1ffa1b185d98fe67ce6c7385`.
This is a whitespace precision issue in the prose, not a semantic mismatch;
the frozen byte hash is the acceptance discriminator.

## Source-owner derivation and remaining inference premise

1. `local_source.rs:630–659` retains named formal identities and wraps each
   parameter as `LocalSourceForm::Lambda`. Its identifier constructor at
   1041–1075 resolves `x`/`flag` lexically and otherwise resolves unique module
   names. Unshadowed `true`/`false` become Boolean literals. Thus the relevant
   intended shapes use retained Lambda, Name, Apply, If and literal owners.
2. `candidate_source.rs:1311–1327` retains each module reference as its own
   occurrence-qualified pending use and `Action::Module`. Applications retain
   their callee/argument/result/effect components at 1392 onward. The If owner
   at 1240 onward checks the condition against BoolNegative and constrains
   both explicit branches to the result; it does not execute the condition
   before inference.
3. `candidate_scheme.rs:1361–1445` processes definition SCCs in dependency
   order, runs all member schedules before capture/publication, and keeps
   active internal uses on open roots. `candidate_source.rs:1753–1759` chooses
   that open route for active internal uses and incoming routing otherwise.
   Countdown's internal self reference therefore belongs to the recursive
   route, while the three uses of identity are separate incoming occurrences.
4. `candidate_scheme.rs:1911–1965` freshens a captured graph for a particular
   use occurrence and stores that use's retained maps. The important guard at
   1598–1609 is `row.local && level > graph.boundary && !metadata.non_generic`.
   Its canonical-row map is allocated inside each fresh-use call: aliases in
   one use share an image; generic source rows in different calls allocate
   separate images **if that guard holds for the relevant captured rows**.

The final italicized condition is an explicit remaining premise, not an
observed row census. This inspection does not establish that every relevant
identity row in this exact parsed module has that locality/level/genericity,
nor reprove SCC construction, lambda/Call admission, extrusion or intrusion.
Those are prover/owning-construction obligations. Runtime output equality
alone cannot prove this premise: execution erases inference instantiations.
No direct R64/R65 premise is discharged here; those parents and all A/B,
adoption, effect-hygiene, source-law and production gates stay OPEN.

## Conditional runtime derivation and cache attack

Hypotheses: the exact fixture lowers to the described retained shapes;
`prepare` accepts it without candidate conflicts; runtime constructor and
receiving/invocation invariants hold; allocations and the transition budget
suffice. These hypotheses are not proved by manually following the machine.

`apps/yulang-wasm/src/lib.rs:11–19` calls existing `execute` with scoped=false.
`execute` at `lib.rs:166–180` prepares the entire source, constructs its runtime
program, selects the requested DefId, then starts the original source schedule.
It does not synthesize a replacement entry definition.

`program.rs:509–555` assigns the unannotated formals Value role and compiles
Lambda/Apply/If directly. Its 615–656 constructor schedules the four computed
bindings and all four bare name expressions; the two function values are
materialized when demanded. `machine.rs:1851–1903` visits the roots and only
then publishes the selected cell. ExpressionReturn (1250) discards the bare
expression's value; it cannot overwrite a selected-definition cache cell.

The cache attack is blocked on this source route by the distinction between
closure and invocation: first identity demand materializes its closure in the
identity definition cell; GlobalRead (1265) caches that closure. Each Apply
creates its own argument delay (899), enters the closure through ValueEntry
(989/1100), and `bind` (2025) appends a fresh parameter cell and environment.
The body reads that call's `x`. Thus, under the hypotheses, the three bindings
receive `7`, `true`, and `"ok"`; they do not reuse identity's first argument
as a cached function result. The same immutable closure can be shared safely.

Countdown first materializes its Lambda and clears its initialization marker
before invoking the body. Its outer parameter cell contains false, so Condition
(1179) chooses the recursive Apply. The self-name reads the already cached
closure, and the new ValueEntry cell contains true. The inner condition takes
`8`; both invocations return it. The cached callable therefore avoids the
RecursiveDefinitionInitialization path, and per-invocation cells prevent the
false argument from contaminating the true invocation. No effect request or
continuation participates in this finite trace.

Each `run` constructs a new Machine with new cells/environments (292–357).
Four selected-definition calls do not share module cache state across runs.
This is a source-inspected conditional derivation, not an execution receipt
or an established theorem for arbitrary recursive functions.

## Oracle independence, coverage and failure conditions

The external Yulang2 `runs_web_playground_example` at lines 164–211 supplies
independent expected values from a separate implementation's test source.
I read that test but did not rerun it. It executes the full sample and checks
ordered results; association to these four definitions follows the matching
bare source expressions and the same test's name/type list. Both versions
share the sample and intended language meaning; the Yulang3 smoke shares
the candidate evaluator's actual implementation. Four output comparisons are
finite compatibility evidence, not an independent proof of its transition
rules, generalized typing or whole-demo correctness.

Coverage is exactly the two literal source blocks, five application sites
(three identity, countdown false, countdown true), their bare result roots,
and the inspected constructors/routes. No seeds. The only enumerated range
was whitespace extraction: leading LF counts 0–2, separator counts 1–4 and
trailing counts 0–3, to locate the already supplied fixture hash. No semantic
mutation was executed. A hypothetical first-argument cache mutant is rejected
by bool/string output comparisons; the supplied static route already uses new
cells. A hypothetical broken fresh-use metadata guard could remain invisible
to output checks and needs owner evidence rather than another runtime toy.

Failure conditions: any pinned audited owner change, candidate conflict or
unsupported shape, ExpectedBoolean/ExpectedCallable, missing binding,
recursive initializer read before Lambda publication, invalid receiving owner,
resource exhaustion, fixture hash mismatch, or wrong selected output prevents
the claimed receipt. Whole-sample arithmetic, methods/roles, standard modules,
lists, tagged values and nondeterminism were not inspected here. No general
source acceptance, soundness, principality or termination claim follows.

## Commands, resources, state and next action

Commands: bounded `cat`, `rg`, `sed`, `sha256sum`; read-only Python extraction
and hashing. Initial `python` invocation exited 127 (command absent); reran
the same read-only calculation with `python3`, successfully. No tests/builds,
compiler/formatter/Yulang CLI/Git or background process. No heavyweight job;
CPU time and peak RAM were not measured. The actual audit began at tool clock
2026-10-19 15:47:00 UTC; final elapsed/remaining receipt accompanies its frozen
hash in the submission message. Hard wall cap: 240 seconds. No dependency
hash changed in the audited snapshot. No compiler/proof/implementation file
was written. Sole changed path is this exact leased handoff.

Recommended next action: primary consumes the prover's exact generic-row
premise evidence, freezes the byte-exact fixture and implementation, then
obtains the contracted fresh reviews before its single authorized smoke.
No interactive decision or broader API/semantics is required by this audit.

Worker state: **STOPPED on frozen submission; writes ceased**. No descendant
leases. Review status: unreviewed research/source evidence; primary adjudication
and independent final review pending. This file must not change under review.

## Commit packet

- Exact leased path: `tasks/agent-loop/inbox/20261020-r132-source-audit.md`.
- Baseline: `9fab033a27390ac12f7553a9d6af11a82ad66e1b`.
- Changed dependency hashes: none among the audited owners above.
- Review: producer evidence only, unreviewed; no self-certification.
- Checks already run: read-only source/authority inspection, supplied-pin
  comparison and fixture extraction/hash discrimination; no executable claim.
- Proposed message: `research: record conditional R132 ordinary-island source audit`.
- Shared-record deltas left for primary/curator: note exact fixture whitespace;
  retain the identity generic-row guard as an unproved source premise unless
  the prover supplies it; record this worker STOPPED and all parent gates OPEN.
