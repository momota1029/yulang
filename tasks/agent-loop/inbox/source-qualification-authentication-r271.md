# R271-r3 frozen source-qualification handoff

- Assignment/handoff ID: **R271-R3-SOURCE-QUALIFICATION**, revision **1**.
- Contract: `tasks/agent-loop/sprints/source-qualification-authentication-r271-r3.md`,
  SHA-256 `67f9423c61042798b9fb6a85efe9ecf74577d941fb64cf8f1fe2c77a291f20bc`.
- Parent: full inference/effects soundness → R70 →
  `R71-RAW-CANONICAL-FIBER-COVERAGE-1`; original source domain, quantifiers,
  Simple-sub A/B, independent assignments/shared witnesses, source/native
  correspondence, F1/FK1 and foreign continuations unchanged. Parent/A/B
  delta **0→0**, original parent **OPEN**.
- Baseline supplied by Luna: `8d646ac2ed171e13a529e25e035fc75f91678b0b`.
- Worker/sole author: `/root/sol_r270_source_qualification_auth`, registered
  prover, no coauthors/descendants. Exact live identity compared before GO;
  fresh RUNNING acknowledgement in session
  `01a1873a-a93b-7dc3-a8ce-028a7b543a80`. Child runtime UUID UNKNOWN.
- Requested Sol/high; observed effective model/effort **UNKNOWN**. Configuration
  and request strings are not effective-model observations.
- Exact new/leased paths: this inbox and the theory named below; no other
  new/scratch/generated/cache path.
- Outcome class: **candidate source-native-evidence / conditional constructive
  trace**, pending fresh independent review. No checker, runtime success,
  source-qualified parent counterexample, approved-clause defect, production
  repair or full-inference acceptance is claimed.

## Result and application

The exact fixture is the 87-byte string:

```text
my outer = { my loop x = { my direct = loop x; my helper y = loop y; helper x }; loop }
```

The theory derives its normal source-constructor path under the selected
opt-in feature and successful-allocation envelope, rather than assuming the
fixture's `unwrap` or assertions. It separates syntax/HIR/source-carrier
construction, candidate collection, graph eligibility and actual extrusion.
The derivation is source-level work, not a kernel-checked Rust/library proof.

The concrete progress beyond R271-r2 is:

1. `SyntaxIn::token → In::token → Token::run_once → checkpoint/None rollback`
   restores the exact `&str` suffix. `with_str` captures consumed text and does
   not perform rollback. Reborrow traits/templates were inspected, not
   executed as a macro build.
2. Authenticated unicode-ident ASCII masks give true Start/Continue for every
   fixture letter, and false for space/`{ } = ;`. This supplies the finite
   continuation/suffix failure facts used in the cursor trace. Header imports
   and operator facts are empty; the effective operator builder returns its
   empty table. Literal mode returns None for the ordinary nonquote spellings.
3. The full parser's actual Binding/Pattern/ML-argument/braced-sequence owners
   give one outer BindingStatement, two brace blocks, three explicit separators
   and no recovery token. The Rowan builder/cache/ordered-child source owners
   preserve that content; hashes are not used as a tree-equality premise.
4. HIR uses one actual artifact A, outer definition root R and source root
   SR=Definition(R). Local IDs are owner-qualified ordinals L=0, D=1, H=2;
   parameter ordinals X=0, Y=1. The theory gives all **14 expression slots**,
   exact children, owner scopes and seven resolved Names. Temporary recursive
   self binding and Publish/Restore establish identity; spelling alone does not.
5. `lower_plan` retains this carrier in `local_sources[R]`. Its older ordinary
   brace-body facade is an UnsupportedExpression placeholder, which does not
   reject opt-in carrier formation. The candidate true/true collection route
   retrieves that same carrier, and `emit_candidate_source` checks pointer and
   R/DefinitionOrderId ownership. No foreign or reconstructed lookalike carrier
   is substituted. Source scheduling has no unresolved/imported Name.
6. Complete graph inventory: **19 vertices (9 semantic, 10 fragment helpers),
   23 raw edges and exactly three checking events**. Local/parameter births:
   outer=1; loop/X=2; direct/helper/Y=3. All helper entries preserve their actual
   planning levels, and every level is recorded before seal.

Event order is expression-vector order, not recipe execution order:

| event | checking | origin | receiver | native qualifies |
|---|---|---|---|---|
| 0 | (e4,0) | loop L, level 2 | helper H, level 3 | false |
| 1 | (e5,0) | direct D, level 3 | loop L, level 2 | false |
| 2 | (e9,0) | helper H, level 3 | loop L, level 2 | false |

The actual seal rejection premises are checked against the complete table.
Its equal-level induced graph is acyclic, so all native components are
singleton (`components[v]=v`). Raw references include L→H→L; raw graph
eligibility is true for events 0/2 and false for event 1. Collection calls
this seal; session initialization later reuses the sealed vector.

The real consumers are `shadow_apply` source Apply demand/slot-0 admission,
`candidate_context_seed`'s checking/event join, and
`retain_extrusion_parent`, `finish_candidate_extrusion`,
`recapture_candidate_extrusion`'s existential checks of the whole processing
source set. Since every event in this isolated batch is false (and invalid
indices also return false), their existential qualification is false for any
such source set. This removes R269's incomplete-event-inventory caveat for
this particular graph. It does **not** assert that an actual selected Parent,
extrusion pair, physical slot or canonical c has been reached.

The unchanged parent is still inapplicable at that exact missing join. Raw
SCC membership and an Apply event do not themselves create an extrusion or
prove its source-required equality. `Need_D`, the R268 incidence square,
ordered opposite Replay ancestry and universal raw/canonical coverage remain
unproved. The qualification discrepancy alone is not an approved-clause
defect or source-qualified parent counterexample.

## Mutual TODOs and implementation boundary

`R271-ACTUAL-PAIR-JOIN-1` to Luna: preserve R/SR/e4/e9/L/H from this carrier,
then trace the actual source-seeded processing ancestry to a reached production
extrusion Ω, actual polar parent/copy pairs and consumer. A proposed defect
is falsified if no pair is produced, a different occurrence owns it, or a
competing approved consumer supplies the needed equality. Any observer or
execution requires a separate exact lease; none is authorized/written here.

`R269-SOURCE-NEED-CARRIER-1` remains to Luna: independently justify the named
canonical c-bearing obligation before its witnessed copy/equality square and
complete slot/history/opposite-input transport proof. Endpoint/bucket equality,
source nonqualification and one local frame cannot replace that evidence.

Inspected owners `Graph::seal/qualifies` and
`retain_extrusion_parent/recapture_candidate_extrusion` leave implementation
**NO_SAFE_CODE_SLICE** absent a reached actual-pair violation. ENTRY-WF,
drain/eventual Diagnostics, Q262-EPISODE, TEMP265/Z265, permitted histories,
diagnostic/helper coverage, complete Call, soundness, A/B, F1/FK1 and foreign
continuations remain OPEN. No semantic change or source-domain narrowing.

Prior work reused only within its premises: R269-r4 LEVEL269/ownership by
`/root/sol_r269_source_need_r4`, bounded independent review by
`/root/r269_source_need_r4_review`; this author's earlier R270/R271 cursor,
literal and conditional HIR facts. R70/R71/R267/R268 supply unchanged parent
locators and bounded prior gaps, not source coverage. No quarantined artifact,
R255 theory, test assertion or withdrawn bypass is a proof premise.

## Frozen artifacts, dependencies, checks and cessation

Theory: `notes/theory/2026-11-02-source-qualification-authentication-r271.md`,
SHA-256 **`5760eeaac26e3b99104b3f14f137b37f60684434342a436527b849674be40147`**.
This inbox's final hash is delivered in the terminal receipt, avoiding self-hash.

Dependency manifests:

- R271-r2 contract:
  `dfab9720fea19807bca1ad386bffbe4bdb508bef222c5f6480001350be35569e`.
- R271-r3 additive readiness:
  `ef2b3f4c51e383722b458483ba3f5cf05e35ee8e4d918545c94294d0734a7871`.
- R269-r4 contract:
  `a5f3bd1f3bc701ce75191ec234b72264d0dd9e73d7dfd31b88f0b8da0c6009ec`.
- R255 36-entry manifest:
  `f6138d36052934093328e34c01102fc9155ea9d8a0ccfd19182af6e7e2d946ef`.

Initial and final `sha256sum` gates matched **139 local/r2 + 68 additive
external rows, 207 total manifest rows; 302 distinct inherited/direct pinned
paths, zero failures**. Final gate and unchanged additive readiness were
checked at 2026-11-02 13:55:29 UTC. New archive hashes match their Cargo.lock
checksums. Luna's archive-member/source-byte comparison is reused; this author
did not independently repeat every member comparison. The r3 contract's
historical r2-readiness hash citation has a primary-acknowledged transcription
typo; Luna owns its separate erratum. It is not an active source pin mismatch.

Bounded source reads and mathematical source inspection only. Some bulk output
was truncated and incidentally displayed in-file cfg(test) sections; no test
body is used as evidence and no exhaustive library audit is claimed. No Lean
types/axiom audit apply. No tests, builds, probes, benchmarks, Cargo, network,
source/expectation edits, Git, nested CLI, descendants, scratch/generated/cache
outputs or other file writes.

R271-r3 Sol cap **1,200 seconds**, no reset/extension; full reservation remains
charged. Earlier Sol charges remain R270 4,500 and R271-r1/r2 3,600; cumulative
Sol reservation **9,300 seconds**. Actual active duration/CPU/RSS UNKNOWN.
Observed r3 UTC cuts: 13:42:52, 13:44:44, 13:48:32, 13:49:16, 13:53:32,
13:55:29 on 2026-11-02. R271's total retained/allocated envelope remains 6,600
seconds; no automatic next grant is requested.

**Both artifact bytes are frozen at this revision. All proof exploration,
technical reads and writes stop.** Only final read-only artifact hashing
remains before the terminal cessation receipt. No descendants or unresolved
descendant leases. Luna owns fresh independent review, adjudication, shared
record synchronization and Git. This is a research-only milestone pending
review/integration; the parent remains OPEN and this worker is not claimed to
continue running while waiting.
