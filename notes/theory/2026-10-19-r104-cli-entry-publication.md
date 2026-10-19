# R104: finite public CLI publication for two ordinary-entry cells

Status: frozen candidate source/native evidence, assignment `R104-PROOF`, revision 1.
Author: `/root/r104_source_proof`. Governing R104 revision 2 contract:
`tasks/agent-loop/sprints/cli-entry-publication-20261019-r104.md`, SHA-256
`8cd15a5ab18a3923399ce2f14415df2782b131e626a7937b1e926decc8d40a61`.
Luna's NEW_TASK explicitly grants this two-path proof assignment. This is a
publication derivation with a finite runtime premise and a new CLI observation
still pending; it is not an independent certification or production guarantee.

## Parent, exact inputs, and reusable evidence

The R104 local obligation is to connect two R97 ordinary-entry cells to the
public `--run main --steps 1000 <example-path>` consumer. Its original parent
remains proof-backed inference/evaluation and runnable source, including §21
entry behavior. Original Simple-sub A/B, effect-hygiene, method/role and evaluator
quantifiers are unchanged. No foreign-continuation quantifier follows from this
local ordinary-call trace.

Let `D` be the exact UTF-8/ASCII bytes
`act signal:\n    our ping: () -> int\n`. Here `\n` denotes one LF.
The two R97 strings are exactly:

| Cell | Body appended to D | Historical R97 outcome |
| --- | --- | --- |
| V | `my ignore x = 9\nmy main = ignore (signal::ping())` | UnhandledRequest, declaration-owned ping, Unit payload |
| C | `my ignore (x:[] int) = 9\nmy main = ignore (signal::ping())` | Completed Integer `9` |

Neither R97 string has a final LF after the last `))`. Fixture identity must be
checked against this recipe; an added byte is not silently justified by R97.
The new examples and test belong to the implementation lane and were not read
as proof inputs: they are not among this assignment's frozen pins. Fresh review
must join their final hashes and bytes to this finite domain.

`runtime_control.rs:14–43,46–77,157–162,193–198` contains the actual constructors,
ordinary preparation helper and the two assertions. The helper parses using
`SyntaxEnvironment::empty`, lowers with empty SemanticImports, solves ordinary
CandidateInference, rejects conflicts, constructs RuntimeProgram with default
evidence, selects `main`, obtains execution_roots, then starts that schedule.
The frozen R97 closeout records its one six-cell command passing, with all
assertions reached. This establishes historical exact-cell compatibility and
10,000-step outcomes; the proof note's earlier UNOBSERVED status is superseded
only by that closeout on those assertions. Its conditional statements outside
those observations remain conditional. The final implementation handoff hash
is the closeout's disclosed `b6d9...`, not the proof handoff's earlier `247e...`.

R97's historical ModuleIdentity is `FileKey("runtime-control", "test.yu")`.
The CLI constructs `FileKey("inference-playground", example-path)` and uses
1,000 steps. This note does not assert a general filename/identity renaming
lemma or infer a 1,000-step receipt from a 10,000-step receipt. Public file read,
current preparation and sufficient fuel are explicit R104 observation seams.
R97's RuntimeProgram hash differs from the current pinned file; no whole-file
identity is assumed. The current needed branches are inspected below, while
the current whole outcome remains for Luna's command. Runtime literal decoding
of the exact `9` is reused only within R97's observed cell; no new literal-owner
claim or unpinned owner inspection is made.

## Finite source schedule and entry path

The pinned program consumer copies the original formal ID and derives Lambda
role by outer annotation row presence (`program.rs:488–508`). V therefore has
Value; C has Computation even though its row is empty. The retained argument is
the whole Apply child (`:510–515`), not a selected request prefix. C's
RootCompSchema retains the authentic formal and Lambda SourceSite, requiring
matching annotation/formal ownership and outer row presence
(`receiving.rs:21–42`). These identities are not collapsed into spelling,
solved support, provider identity or a witness from another receiver.

On the R97-constructed forms, ignore's Lambda is a value root and main's Apply
is a computation root under `program.rs:570–600`. The public execution_roots
returns `source_schedule.clone()` (`:246–247`); the CLI-only
start_source_schedule passes `&self.source_schedule` to the same start
(`machine.rs:288–292`). Thus these two entry methods use the same stored root
sequence for each given RuntimeProgram; this is direct field/argument evidence,
not general source/native or filename equivalence. `start` validates IDs,
initializes empty cells/frames and begins root zero (`:299–373`).

The constructor-to-consumer sequence is:

1. main's Apply saves its entire argument and evaluates ignore's Name
   (`machine.rs:645–656`). The global Lambda can materialize into a closure,
   retaining formal, role, schema, body and environment (`:558–644`). GlobalRead
   caches and consumes that closure (`:1219–1233`). This does not run ignore's body.
2. Callee allocates an inert Delay for the whole argument, then creates the
   closure invocation and installs ReceiverReturn (`:879–969`). No ping executes
   while that argument is merely constructed. The original call/provider sites
   and receiving view remain separate.
3. V installs ValueEntry and executes that Delay (`:969–977`). Ping's declared
   Unit payload selects Value entry in the operation branch (`:1011–1069`);
   its payload returns Unit, OperationPayload constructs its request carrier,
   and OperationResultConsumer executes it (`:872–877,1927–1957`). No Catch exists
   in either source. The actual request path can reach stop_unhandled_request
   and emit UnhandledRequest (`:1531–1776`). V's body 9 cannot be evaluated
   through its pending ValueEntry before its argument returns. This explains
   the historical R97 V observation and predicts the same public finite outcome.
4. C enters the computation schema under that invocation, binds the Delay to
   the original formal with Computation interface, and evaluates body 9
   (`:978–1009`; receiving `:116–175`). That branch does not execute Delay.
   The ignored formal has no body read. ReceiverReturn passes back the body's
   value; Root stores it and begins the remaining schedule (`:1070–1080,
   1210–1218`). Once the schedule ends, the selected cached value becomes
   Completed (`:1816–1855`). This explains R97's C observation and predicts C's
   public finite outcome without invoking the delayed operation.

This trace applies the finite entry result to R104's public consumer. It does
not prove preserved suspended suffixes, general handler search, continuation
resumption, sibling permission, a complete projection theorem, method/role
execution or source-wide entry behavior. The V request's continuation existence
was asserted by R97; no suffix-content/equivalence theorem is imported from it.
The machine's stopping semantics (`:482–519`) return the first terminal outcome
within the caller budget; an exhausted budget yields ResourceExhausted rather
than a completed value. R104's smaller-budget outcome remains unobserved.

## Deterministic publication lemma for these outcomes

For either exact invocation, main's parser accepts `--run main` and positive
`--steps 1000`, and the one example-path selects File::open/read_source
(`main.rs:9–79`). No help or inference-output branch is selected by those
arguments. File open, valid UTF-8, input cap, parser diagnostics, lowering,
ordinary solve/no-conflicts and current runtime construction/selection are
prerequisites, not consequences of argument parsing (`lib.rs:40–51,167–189,
266–342`). All preparation uses the actual candidate path; no inference,
propagation, level, extrusion, intrusion or generalization bypass is added.

For a machine outcome UnhandledRequest, execute immediately returns
`Err(bounded_message("unhandled runtime request at <range>"))`
(`lib.rs:186–187`), before allocating its normal-result Output (`:190`).
`bounded_message` (`:395–402`) uses the pinned Output helper. This short ASCII
message and the bounded source range fit BYTE_CAP; no observation charge is
made. There is no result-prefix write to stdout. The `?` at main.rs:76 exits
run before its sole `print!` at :80. main then `eprintln!`s the error and returns
ExitCode::FAILURE (`:84–91`). Under successful ordinary process I/O, V therefore
has unsuccessful status, empty stdout and stderr containing the existing
`unhandled runtime request` diagnostic followed by a newline. Exact stderr
range text is intentionally not generalized or frozen as a new diagnostic.

For Completed(h), execute resolves h with machine.value (`lib.rs:180–182`;
`machine.rs:468–470`). Given the exact R97 C value kind Integer("9"), the
Integer branch writes that stored string, then one LF, then finish
(`lib.rs:190–201`). Output starts with empty text, work=0, failed=false
(`output.rs:15–20`); its write_str appends both bytes because 2 < BYTE_CAP
(`:38–54`), and finish returns precisely that text (`:30–35`). Therefore the
library returns `Ok("9\n")`. run's sole print writes exactly those bytes,
returns Ok, and main returns ExitCode::SUCCESS without the error branch.
Under successful ordinary process I/O, C therefore has stdout exactly `9\n`
and empty stderr. No inference graph/banner is printed along this --run path.

These implications are newly derived source-consumer evidence. Their runtime
antecedents on R104's concrete file invocations remain predictions until the
single authorized command. Tests of outcomes alone do not prove every internal
allocation or identity statement above.

## Application, falsifiers, and remaining gates

R104 now has a pinned finite bridge from historical ordinary-entry observations
through current outcome/Output/main consumers to public predictions. Before:
R97 observed runtime outcomes only. After this candidate: each of those outcomes
has an explicit public exit/stdout/stderr implication, including atomic result
withholding on the request path. Fresh independent spec and compiler/source
review, implementation byte identity and Luna's one exact command remain OPEN.
No production edit is needed or authorized by this proof.

`R104-CLI-JOIN-1` (Luna): join exact final fixture bytes and test/hash to this
candidate, obtain fresh CLEAN independent reviews, and run only the contracted
command once. Falsifiers are input drift, preparation rejection/conflicts,
wrong exit status/stdout, missing expected diagnostic, nonempty successful
stderr, unexpected exhaustion or dependency drift. A failure is recorded without
repair/retry under R104. The first missing observation is the actual file-based
public preparation plus 1,000-step outcome, owned by `main::run -> execute ->
prepare/RuntimeProgram::from_hir -> start_source_schedule -> Machine::run`.
The implementation lane owns the two example files and integration test;
reviewers must check serial public binary execution and all six output/status
assertions. No proposed compiler TODO has an evidenced necessity here.

The original Simple-sub A/B and evaluator parents, full §21, all six hygiene
fronts as general obligations, authentic method/role consumers and their adoption
gates remain open. Historical R97 observation is reused only as stated; R92,
R95, R96, R101–R103 are not imported as additional evidence or read as inputs.

## Frozen dependencies, provenance, and resources

All 14 contract input hashes were checked and MATCH. Contract hash also MATCH.
The source audit stayed inside these inputs; governing sprint workflow and
handoff instructions were read separately as required by the assignment policy.

| Frozen input | SHA-256 |
| --- | --- |
| `tasks/agent-loop/sprints/value-computation-entry-20261019-r97.md` | `2a9e65fd973e4d9c7f0916440fe8438eb6e9a8b8cd7969dc8f89025d9cf1b1ce` |
| `notes/theory/2026-10-19-r97-value-computation-entry.md` | `77b4ea777a2fd413b356b5128cc55362f1126e6298bcb7c310f776cfd53b4b98` |
| `notes/progress/2026-10-19-r97-value-computation-entry.md` | `aa06b04ff9ad0fb882c89c26e0375fd21eddba489c44b7d54f6156585a66d734` |
| `tasks/agent-loop/inbox/20261019-r97-proof.md` | `6a84958c082f6ec9575cb13962ad395c4246a5e7636df6921429399503eabdfb` |
| `tasks/agent-loop/inbox/20261019-r97-implementation.md` | `b6d9b8206ca433839ab48b9822f8546bf89d40099a2e8e763da1cb6d210ec39d` |
| `tools/inference-playground/tests/runtime_control.rs` | `2619e4c8bb006e2d98cf81887091ae372cb1ae3731de76e7b707a97db577009c` |
| `tools/inference-playground/src/lib.rs` | `bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b` |
| `tools/inference-playground/src/main.rs` | `75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100` |
| `tools/inference-playground/src/output.rs` | `04e99c5bdb562a8edb8a7e17bdcc03f7b46eaca9d8e13b20216b4dcf3032a88a` |
| `tools/inference-playground/src/runtime/machine.rs` | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| `tools/inference-playground/src/runtime/program.rs` | `7bc27580711d3ef09044e324541904ef3388aca8e3b4f3a72437b1e04dc0210a` |
| `tools/inference-playground/src/runtime/receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| `tools/inference-playground/tests/cli.rs` | `cf265feba7414b159353c81751608e9c127b072559b2c8c4cc513ecbc15c22ea` |
| `tools/inference-playground/Cargo.toml` | `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56` |

Sole author `/root/r104_source_proof`; no descendants/coauthors or scratch paths.
Requested model/effort: Sol/high (`gpt-6.1-sol/high`); observed model/effort:
UNKNOWN/UNKNOWN because effective runtime metadata was not supplied. The actual
NEW_TASK receipt establishes this assignment and exact leases. Session:
`current-conversation-2026-10-19-r104-cli-entry-publication`.

Resources: proof cap 600 seconds, Astra 0. A clock receipt at 06:10:35 UTC records
an intermediate start marker after initial reads; full assignment elapsed time
is UNKNOWN and no unmeasured budget is reclaimed or enlarged. Work consists of
read-only inspection/hash reads and these two leased writes. No tests, builds,
CLI/runtime execution, formatter, Git, external contact or production edits.
Note/handoff hashes are supplied in the intake message, avoiding self-reference.
The assignment ends at freeze; worker STOPPED and writes stopped after the
final handoff hash. Review, verification and integration remain Luna-owned.
