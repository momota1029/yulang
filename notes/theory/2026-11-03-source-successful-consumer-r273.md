# R273 — stopped successful-consumer trial and scope incident

Handoff **R273-SOURCE-SUCCESSFUL-CONSUMER**, revision **1**. Sole author:
`/root/sol_r270_source_qualification_auth`, coordination session
`01a1873a-a93b-7dc3-a8ce-028a7b543a80`. Requested Sol/high; effective observed
model/effort and child runtime UUID UNKNOWN. No descendants or coauthors.

**Disposition: INCOMPLETE / authority STOP.** Luna stopped this trial after
the producer disclosed reads of adjacent `cfg(test)` bodies outside the sole
fixture exception. This is a scope incident, not a source counterexample or
an accepted successful-consumer trace. No further technical read, search or
pin revalidation occurred after the STOP. Only this theory and its exact
leased inbox were written afterward to freeze the prefix and incident.

## Authority, pins and unchanged parent

Contract `tasks/agent-loop/sprints/source-successful-consumer-r273.md`, SHA-256
`f9baf8e2736b0a9bef1f4243cae1df35f9493c421a95973f82fd61b0cab3782e`, was
independently read/hashed in a contract-only WAITING gate, compared by Luna,
and followed by a separate explicit GO. First post-GO clock observation was
2026-11-02 **15:13:37 UTC** (2026-11-03 in Asia/Tokyo).

Before technical source reads, the exact input inventory hash matched:

`tasks/agent-loop/sprints/source-successful-consumer-r273-inputs.json`
SHA-256 `42040552635bb7c2652eb0bad68cb46295078d03ae70620b7edd555d3883fa5f`.

The successful independent initial static hash pass checked all **229 distinct
entry paths**, all **three source-manifest hashes**, and the **two additional
named inherited contracts**: **234 checks, zero failures**. The manifest's
authenticated origin tables contain 243 rows before deduplication. The exact
229 path/hash/from entries remain the inventory, not an invented larger set.

Source manifests:

| Record | SHA-256 |
|---|---|
| R271-r2 contract | `dfab9720fea19807bca1ad386bffbe4bdb508bef222c5f6480001350be35569e` |
| R271-r3 external readiness | `ef2b3f4c51e383722b458483ba3f5cf05e35ee8e4d918545c94294d0734a7871` |
| R255 contract | `f6138d36052934093328e34c01102fc9155ea9d8a0ccfd19182af6e7e2d946ef` |
| R269-r4 additional inherited contract | `a5f3bd1f3bc701ce75191ec234b72264d0dd9e73d7dfd31b88f0b8da0c6009ec` |
| R268 additional inherited contract | `719497ad1921be23329a8df790e942ba5c63170ed2bae4880c9656634389ad72` |

The initial hash-only attempt used `python` and failed immediately with command
not found (exit 127); it read no source. The same static inventory/hash operation
then completed using `python3` with `json`/`hashlib`, writing no file and
executing no compiler/source code. Final input pin revalidation was **NOT RUN**
because Luna's STOP expressly forbade further technical/hash work. The initial
pass must not be reported as a freeze-time pass.

The four named R272 context records also independently matched before their
use as conditional context:

| Record | SHA-256 |
|---|---|
| R272 theory | `be97b713d068a46d3705ec777bb8a591e00277fa9b5ebdf7fd7c7882672f9ece` |
| R272 inbox (hashed, body not reopened in R273) | `9310448373116ee8dc6e285a8484c2f6bf421c7b23872e54cf73e788693731e9` |
| R272 independent review | `d19dacb3b4d18a63d2febc56d7f0354552af3ad5ea8a3ab7434f5fe59f0b40d3` |
| R272 pin-count erratum | `98ccf3badb951699c862d2ef2d10de5167dbdc3720b4016c86e65e975c8e11b2` |

R272's 307-path assertion is withdrawn, not reused. Its review was INCOMPLETE;
its native equations are conditional context, not accepted R273 premises.

Unchanged parent: full inference/effects soundness → R70 →
`R71-RAW-CANONICAL-FIBER-COVERAGE-1`, preserving original domain/quantifiers,
Simple-sub A/B, independent assignments/shared witnesses, source/native
correspondence, F1/FK1 and foreign continuations. Parent/A/B **0→0**.
No Lean theorem, checker result or axiom audit is claimed. `NO_SAFE_CODE_SLICE`
remains; no implementation or production promotion is authorized.

## Established limited prefix and first unchecked implication

The permitted fixture excerpt `candidate_source.rs:2525–2540` supplies the exact
87-byte input spelling and constructor identities only:

```text
my outer = { my loop x = { my direct = loop x; my helper y = loop y; helper x }; loop }
```

It selects `parse_file`, same-source `scan_header`, empty syntax environment,
`shadow::lower_module_with_local_source`, empty semantic imports and FileKey
`("local-self-recursion-kernel", "source.yu")`. The fixture's `unwrap` is not
evidence of constructor success. No assertion or expectation is a premise.

The following inspected production equations are retained only with their
own explicit input/normal-return conditions:

* Syntax `full_parse.rs:1–220` retains source, green tree and parse identity;
  `SourceNodeKey::eq` compares parse Arc identity, green allocation identity
  and start offset. This does not prove that this fixture creates that tree.
* `header.rs:37–160` stops at FirstNonHeader when both header selectors reject;
  `operator_selected:163–220` reserves a lexical Binding before private
  operator selection. The complete selector application was not finished.
* `lib.rs:10400–10508` allocates dense per-kind rows, initializes source
  levels, and starts a candidate session on its candidate entrance.
  `:10702–10743` skips global pre-admission in active source mode and runs
  source schedules; `:10744–10771` distinguishes candidate execution from
  closed finalization and checks deferred field-tail selection. None proves
  successful execution of this fixture.
* `candidate_source.rs:2330–2505` production schedule owners dispatch actions
  synchronously; installation uses a distinct PublishLocal stage and source
  completion checks empty capture stack and Lambda depth. The interleaved
  test-only support helper is excluded from this equation (incident below).
* `lib.rs:11622–11834` production Lambda admission allocates entry/return
  effects, admits entry/body-to-return edges, builds a positive Function and
  constrains it to the Lambda root. This is a constructor equation, not a
  computed successful H/L Lambda continuation or equality result.
* `candidate_scheme.rs:5079–5150` production local capture/installation checks
  its matching slot, records a LocalScheme root/boundary and pops a matching
  capture; it does not itself assert equality of an extrusion copy and parent.
* `candidate_scheme.rs:5227–5335,5430–5470` production local routing captures
  a graph, prepares FreshUse, restores its bounds and links the fresh root to
  the occurrence component. No complete captured H/L graph, restoration,
  transaction, recurrence or successful publication was derived here.
* `candidate_scheme.rs:3150–3240,3369–3455` production graph-plan entrance
  executes source roots before capture/staging and orders definition/provider
  nodes. This is conditional on the actual collection/SCC inputs, not their
  completed reconstruction for this fixture.

**First missing implication:** exact bytes/classifier/scanner rollback and
complete header/statement-selector/parser construction → recovery-free accepted
CST → exact HIR root/fourteen-slot carrier → successful collection/static-SCC
entry. Owners remain syntax lexical lexer/current_item, local chasa-recover
Token, unicode-ident ASCII branches, header/statement/declaration/pattern and
expression owners, Rowan construction/readback, HIR local_source lowering and
solver collection. Although these owners have pinned paths, their complete
finite application was not established before the authority STOP. No missing
unlisted owner or changed source byte was found.

Consequently the R272 four-Parent e9/Ω9 result is **not promoted** into a fully
accepted R273 source trace. Actual later H/L Lambda admissions, every earlier
Effect drain, H/L FreshUse, equality settlement, every source-action return,
ordinary acceptance and successful final publication remain UNCHECKED.
Whether an approved successful consumer requires equality for all four Ω9
Parents and whether a competing path discharges it remain OPEN. No rejection,
different Replay order, equality discharge or failed publication was proved.

Independent `Need_D` still needs its source-required canonical candidate and
selected physical slot/consumer justification; `R71-RAW-CANONICAL-FIBER-COVERAGE-1`
still needs the raw/canonical incidence square, actual ordered opposite Replay
inputs, equality/canonicalization history and required witnessed continuation.
Their approved source/context/Replay/canonicalization owners are not replaced
by a local constructor equation or by this stopped trial. No edge is CLOSED.

## Exact scope incident

The contract permits test-fixture bytes only at
`candidate_source.rs:2525–2540`. My use of broad range reads displayed other
`cfg(test)` bodies. I disclosed this to Luna while working; Luna explicitly
ordered immediate STOP. The following are the exact incident-relevant commands
and requested line ranges. These are a record of reads, not commands to rerun.

1. Initial production/source-schedule excerpt:

```sh
sed -n '2330,2505p' crates/yu-solver/src/candidate_source.rs
```

Actual displayed bytes included the entire `#[cfg(test)]`
`supply_synthetic_source_support` helper between production source-driver
owners, plus test-only formal capture tracing blocks. This was a real body
read, not merely a locator. Its synthetic support was not invoked or used to
justify production execution. The permitted fixture range was read separately.

2. Broad entrance locator/read command:

```sh
rg -n 'pub fn|fn execute|run_candidate|finish|Unsupported|errors.is_empty|source.active|legacy|collect_hir' crates/yu-solver/src/lib.rs crates/yu-solver/src/shadow_apply.rs crates/yu-hir/src/shadow.rs
sed -n '10380,10815p' crates/yu-solver/src/lib.rs
```

The `rg` produced test-only locators among production locators. The read range
also contains test-only lifecycle probe blocks, injection helper bodies and
`run_with_observer` body. The returned tool result was truncated; I cannot
claim every requested byte was visible to the model, but test body bytes were
actually displayed by this read and/or the following overlapping read. The
unavailable/truncated suffix is not positive evidence.

3. Overlapping entrance/Lambda excerpts:

```sh
sed -n '10400,10520p' crates/yu-solver/src/lib.rs
sed -n '10640,10840p' crates/yu-solver/src/lib.rs
sed -n '11620,11755p' crates/yu-solver/src/lib.rs
rg -n 'install_candidate_local_term|freshen_candidate_local|candidate_local|publish_candidate|capture_candidate' crates/yu-solver/src/candidate_scheme.rs
sed -n '11750,11845p' crates/yu-solver/src/lib.rs
```

These definitely displayed the test-only CLOSED_LIFECYCLE_PROBE closures,
admission/provenance/finalization failure-injection helper bodies,
`run_with_observer`, test-only counters and the Lambda injected-failure block.
The scheme search produced additional test-only function locators, not their
bodies. No observer, injected failure, counter or test result is evidence for
the retained production equations.

4. Syntax owner excerpts:

```sh
sed -n '1,220p' crates/yu-syntax/src/header.rs
sed -n '1,180p' crates/yu-syntax/src/root_statement.rs
sed -n '1,200p' crates/yu-syntax/src/declaration/mod.rs
sed -n '1,160p' crates/yu-syntax/src/statement.rs
```

The `root_statement.rs` range definitely displayed the test-only
`parse_yulang_code_cell` body and `RootStatementState::fenced` body. The
`statement.rs` range definitely displayed test-only `statement`,
`statement_normalized` and `statement_from_item_normalized` helper bodies.
They were not used to establish the production root parser or fixture success.

5. Last technical operation before Luna's STOP was locator-only:

```sh
rg -n 'fn classify_statement_item_normalized|fn statement_item_normalized|enum StatementAdmission|fn select_non|selected_lexical' crates/yu-syntax/src/statement.rs
rg -n 'pub.*fn|fn .*selected|fn binding' crates/yu-syntax/src/declaration/binding.rs
rg -n 'fn token|fn with_str|fn run_once|struct Token' crates/chasa-recover/src/parser.rs crates/chasa-recover/src/input.rs crates/chasa-recover/src/lib.rs
rg -n 'pub fn parse_file|fn parse_file|parse_root|GreenNodeBuilder' crates/yu-syntax/src/full_parse.rs crates/yu-syntax/src/cursor.rs
rg -n 'fn scan_identifier|unicode_ident|fn scan_statement_payload|fn scan_expression_payload|scan_bare|scan_keyword' crates/yu-syntax/src/lexical/lexer.rs
```

The chasa/full_parse searches surfaced test-function declaration lines along
with production locators; no subsequent body excerpt was made. No further
source lookup occurred while classifying the incident. Exact guarded-body
sub-line endpoints have not been newly searched after STOP; the requested
ranges and displayed function identities above are the exact retained evidence.

Other technical body reads before STOP were the permitted fixture range,
`full_parse.rs:1–220`, syntax `lib.rs:1–210`, and the production scheme ranges
listed in the prefix. Context reads were the R272 review/erratum and theory
prefix, not independent certification. Operational reads were AGENTS files,
goal-driven-sprints, agent-loop README and the sprint/proofs/proof-portfolio
skills. No test assertion/expectation was used as evidence; no test or probe
was executed. This does not excuse the explicit read-boundary breach.

## Resources, omissions and cessation

No descendants, background processes, tests/builds/probes/Cargo/Lean/network,
nested CLI, Git, source/code/expectation edits, scratch/generated/cache outputs
or central-state writes occurred. All read/hash commands completed. Only the
two exact R273 leased artifacts were created. No frozen R272 record changed.

The full separate R273 Sol reservation is **3,000 seconds**, retained without
reset/refund/extension despite early STOP. Previous source-auth Sol reservations
of 12,300 seconds remain charged; cumulative Sol reservation **15,300 seconds**.
Actual active/CPU/RSS and exact GO-to-stop duration are UNKNOWN. First post-GO
clock 15:13:37 UTC; last technical clock observation 15:15:53 UTC, a 2m16s
observation span, not the complete trial duration. The terminal receipt records
the later artifact-only freeze observation. No continuing RUNNING work is
claimed.

**Writer STOP after final artifact hashes.** All technical exploration and
input hashing stopped at Luna's authority STOP. Only these two artifact writes
and their terminal read-only hashes followed it. Luna owns incident adjudication,
fresh review eligibility, leases, any next contract and Git. A future resumed
packet must maintain the precise test-body exception and close the actual
acceptance/entry premises before promoting the conditional e9 equations.
