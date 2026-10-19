# R105: finite stdin CLI receiver-permission publication trace

Revision 1, 2026-10-19. Sole author `/root/r105_source_proof`.
Status: **candidate / conditional source-consumer evidence; frozen for review**.
This is a finite publication derivation, not independent certification or parent closure.

## Parent and finite source domain

R105 revision 1 asks whether the exact R96 P/N source bytes produce the specified
public stdin CLI observations. P is 210 UTF-8 bytes, no final LF, SHA-256
`765a89c4cee89ceaf4213663b1be8e3110d0f81f4026d2112ddf4ee2f9a23780`.
N changes only `catch pending` to `catch thunk`, is 208 bytes without final LF,
and has SHA-256
`e1b42dbbbd1141c35857a552123e78f4bb8fe69d55bdd2429aaa6614f135705c`.
Their exact source is frozen in the R105 contract and R96 paired test; no fixture
change or added newline is authorized.

R96's closeout records exit 0 for its one paired runtime test: P completed as
Integer 7 and N produced `Unavailable(HandlerEvidence(_))`. Its independent
spec/compiler-source review receipts are CLEAN for that finite candidate
correspondence. Those are historical observations for R96's entrypoint and
identity. They establish neither public CLI execution nor source-name
independence. The R96 proof's pre-run unobserved seams must not be mistaken for
observations made by that author; the later run receipt supplies only its
stated fixture observations. R96's handoffs are provenance, not correctness
certificates; its implementation handoff contains an inconsistent baseline
label, so this report uses the explicit contract/final-file hashes instead.
No R104 artifact is read or reused.

The wider hygiene parent keeps provider, annotation-position, receiver,
request, residual and witness lineages under `xi=(nu,K,D)` distinct. Original
Simple-sub/evaluator, A/B and F1/FK1 quantifiers remain OPEN. Generation,
accumulation, propagation, levels, extrusion, qualifying intrusion and
generalization receive no new theorem or implementation authority here.
R50 remains NOT_ADOPTED and R85 remains AWAITING_USER_ADOPTION as recorded by
R96; R105 supplies no semantic adoption or production authority.

## Completed finite consumer trace

1. `main.rs::run` accepts `--run main --steps 10000 -`. The parsed definition
   is `main`, positive step count is 10000, source path is the literal `-`,
   and neither intrusion nor scoped experiment is enabled. The explicit path
   avoids the no-path terminal-help branch. `read_source(stdin.lock())` reads
   bytes through EOF, validates UTF-8 and the 65536-byte cap, and appends no LF
   (`lib.rs::read_source`). Both fixed sources fit the input cap. Host I/O,
   subprocess creation and successful delivery/EOF remain execution premises.
2. The name is `path.as_deref().unwrap_or("stdin.yu")`, hence exactly `-`,
   **not** `stdin.yu`. `execute(source,"-","main",10000,false)` calls prepare.
   `prepare` uses the shared source text for scan_header/parse_file, requires
   no syntax diagnostics, lowers with empty SemanticImports, solves ordinary
   CandidateInference and requires no conflicts. No solver bypass is introduced.
   Its HIR module identity is constructed from
   `FileKey::new("inference-playground", "-")`.
3. R96's `runtime_receiving.rs::machine` instead constructed its module from
   `FileKey::new("runtime-receiving", "test.yu")`. Treat each input/preparation
   as its own branded source world. In a world W write original outer formal
   t_W, helper formal d_W, family io_W, member tick_W, source root R_W,
   request q_W and runtime views/receivers with the same W tag. No equality of
   these IDs across R96/CLI or across P/N preparations is asserted. P and N
   CLI processes use the same FileKey *value*, but this is no assertion of a
   cross-process HIR identity or transfer of authentication receipts.
4. `execute` uses default RuntimeEvidence, calls RuntimeProgram::from_hir,
   selects `main` with `definition_named`, then calls start_source_schedule.
   `program.rs::execution_roots` returns `self.source_schedule.clone()`;
   `machine.rs::start_source_schedule` calls `self.start(definition,
   &self.source_schedule)`. Thus, within one already prepared program, the
   old helper's execution_roots/start route and the CLI's direct route supply
   the same schedule values to the same constructor. This owner-local fact
   does not identify two independently prepared programs or prove that a new
   FileKey preserves parsing, inference or runtime construction success.
5. Reuse R96's reviewed finite runtime derivation only as its stated mechanism,
   with W-local authentic constructors as premises for the CLI prediction.
   Both annotations yield Computation entry/schema; the helper closure captures
   t_W with outer view V_R,W, while entry binds d_W to V_H,W whose image adds
   helper boundary b_H,W above inherited b_R,W. P executes d_W and then t_W;
   N executes captured t_W directly. At the helper-owned Catch, P observes
   V_H,W and has an authenticated owner/view receipt and reachable b_H,W.
   N has a genuine helper-owner read receipt for V_R,W, whose image lacks
   b_H,W; the unused V_H,W entry receipt cannot substitute for that view.
   `receiving.rs::local_grant` checks active owner, exact observed view,
   receipt, family and image reachability. `machine.rs::propagate_request`
   returns HandlerEvidence when its required positive grant is absent.
   Under the finite premises P selects its payload arm and completes with 7;
   N reaches the candidate HandlerEvidence boundary. These are predictions
   for the CLI world, not a new proof of its source formation or execution.
6. Conditional on P's CLI machine completing with a valid Integer("7") handle,
   `lib.rs::execute` retrieves that value, writes `7` then one LF to a fresh
   Output and returns its finished string. These two bytes fit Output's byte
   cap. `main.rs::run` prints the returned string only after execute succeeds;
   `main` then returns ExitCode::SUCCESS. On the inspected success path there
   is no stderr publication. With ordinary successful host stream writes,
   the resulting finite observation is success, stdout exactly `7\n`, and
   stderr empty. No partial value is printed before completion.
7. Conditional on N's CLI machine returning
   `RuntimeOutcome::Unavailable(RuntimeUnavailable::HandlerEvidence(site))`,
   execute returns the bounded message from
   `format_args!("runtime unavailable: {error:?}")` before constructing its
   result Output. `run` propagates the error before its print statement;
   `main` writes it via eprintln and returns ExitCode::FAILURE. Therefore this
   inspected route withholds stdout and publishes an error line. However, the
   formatter is defined in the existing pin `program.rs:102–123`: both
   SourceSite and RuntimeUnavailable derive Debug, and the enum contains
   HandlerEvidence(SourceSite). Hence formatting that variant begins with
   `HandlerEvidence(`; the ordinary bounded message contains the required
   `runtime unavailable: HandlerEvidence` prefix. Output-cap replacement is
   an explicit alternative error path and must not count as success.
   ResourceExhausted, UnhandledRequest, Running, preparation failure and
   output-cap failure have distinct error routes; none counts as N success.

## Parent application and exact remaining premises

The finite consumer route is now explicit: original bytes are read without
newline insertion; this invocation chooses the literal `-` module name; the
ordinary preparation and runtime constructors remain on the path; successful
Integer 7 completion maps to one `7\n` result; candidate HandlerEvidence maps
to a bounded derived-Debug error, no stdout and unsuccessful exit. This reduces
the original R105 publication obligation to the actual *new CLI* preparation,
runtime and publication observations for the fixed pair. It does not transfer
R96's IDs or certify a newly constructed CLI world from its historical run.

During source inspection this author initially reported that the enum Debug
owner was missing. Luna pointed to the already pinned program.rs definition;
re-inspection confirmed derived Debug for both RuntimeUnavailable and SourceSite.
That missing-owner report is retracted. No runtime/mod.rs or other unpinned
compiler file was opened. No contract expansion or budget reset occurred.

`R105-CLI-OBS-1` remains pending Luna: after proof/implementation freeze and
required fresh independent CLEAN reviews, the contract's one command must
observe P success/`7\n`/empty stderr and N failure/empty stdout/the required
diagnostic substring for these exact bytes and the literal `-` identity.
Required inputs are the 16 frozen pins, this note and the separately frozen
subprocess test; proposed output is the single exact command's status and pair
of stream/status assertions. First missing evidence is actual execution through
this fresh CLI identity and consumer. Falsifiers include failed stdin delivery,
syntax/HIR/solve/conflict errors, runtime construction/start failure, wrong
runtime outcome, unavailable value, output cap replacement, unexpected stream
or status, timeout or source drift. These remain concrete observations to make,
not assumptions certified as having happened by this author. Failure closes
R105 without repair/retry under revision 1.

`R105-REVIEW-1` remains Luna-owned: fresh spec/compiler-source review of the
frozen proof and separately frozen test must validate byte identity, W-local
ID separation, source_schedule delegation and stream/status publication.
A blocking/major finding stops this slice. This author cannot certify its
own derivation or the combined result. The new subprocess test has not been
read or run by this author; its conformity is an independent review seam.

No general sibling permission, language rejection, source-name independence,
native K,D/residual correspondence, unmatched suffix, continuation capture or
resumption, source-wide CLI soundness, method/role dispatch, parent closure,
semantic adoption or production authority follows. The other five hygiene
fronts and method/role/runnable-surface breadth retain independent work.

## Frozen provenance, checks and resources

R105 contract revision 1 SHA-256
`2e037e3848b95f7a60f5809e4a88018b7088d12489cb45149fceca38ed3f1d77`.
All 16 below were byte-hash checked twice while preparing this frozen result;
all MATCH. This author inspected only these evidence pins plus mandatory
repository operating/skill instructions. No unpinned compiler owner was opened.
The R96 proof author is `/root/r96_proof`; paired-test author is
`/root/r96_implementation`; independent review and closeout preserve their
recorded separate provenance. This note's sole author is
`/root/r105_source_proof`, with no coauthors or descendants.

```text
195468ceef7c5fe29aee157260e9f0c218a5dd3e95ed759c40f1f86b348d4892  tasks/agent-loop/sprints/sibling-receiver-permission-20261019-r96.md
2e6026e77d04fa6385e82ecf62cf9f0e63448bcd7619fb6500f11ca2789fe9a9  notes/theory/2026-10-19-r96-sibling-receiver-permission.md
f106525812de5a2788b465dfffb4d8a386883aa8d90b631616ea4bdcb5dd9533  notes/progress/2026-10-19-r96-sibling-receiver-permission.md
84b3302c61e4a20e882552c960c95dadb5e9cb14bae80a5e9e810815f18de583  tasks/agent-loop/inbox/20261019-r96-proof.md
fb99947f978ab905bc65e5f7291ff38f18a74c062b2bc1fe2c5f85113f69b2d6  tasks/agent-loop/inbox/20261019-r96-implementation.md
c43298fcea613e065bd41cceddddaf4c921d060c3cb47263f027acdecb780294  tasks/agent-loop/inbox/20261019-r96-spec-review.md
7390302bd1055ea95f4b73cc20d7a2e356199a915882885e4db422be56b50cdc  tasks/agent-loop/inbox/20261019-r96-compiler-review.md
6ff65fc977c88837ec279b84088a6c2d89ebfc7f78915e7ac985904fcaa26bf2  tools/inference-playground/tests/runtime_receiving.rs
75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100  tools/inference-playground/src/main.rs
bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b  tools/inference-playground/src/lib.rs
04e99c5bdb562a8edb8a7e17bdcc03f7b46eaca9d8e13b20216b4dcf3032a88a  tools/inference-playground/src/output.rs
fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46  tools/inference-playground/src/runtime/machine.rs
7bc27580711d3ef09044e324541904ef3388aca8e3b4f3a72437b1e04dc0210a  tools/inference-playground/src/runtime/program.rs
8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9  tools/inference-playground/src/runtime/receiving.rs
cf265feba7414b159353c81751608e9c127b072559b2c8c4cc513ecbc15c22ea  tools/inference-playground/tests/cli.rs
87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56  tools/inference-playground/Cargo.toml
```

Requested model/effort: Sol/high. Observed model/effort: UNKNOWN/UNKNOWN.
Launch evidence: primary's supported NEW_TASK grant to this task and current
session source inspection; no routing observation beyond that is claimed.
Exact elapsed active work: UNKNOWN (not instrumented). Proof cap 600 seconds,
Astra 0; conservatively charge the full 600-second reservation, remaining 0.
Checks were read-only source/receipt inspection and SHA-256 comparisons only.
No tests, build, runtime, CLI, formatter, Git, external contact or source edit.
All new/scratch paths are this note and the single assigned proof inbox;
no scratch/generated paths exist. Freeze ends the assignment. Writer state is
STOPPED after final hash submission, both outputs immutable pending Luna's
intake/review, no unresolved descendant leases. A revision requires a new grant;
this producer cannot independently certify this report.
