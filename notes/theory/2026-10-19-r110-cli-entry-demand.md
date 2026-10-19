# R110: finite ordinary entry demand at the public CLI boundary

Status: candidate source/native trace and conditional CLI prediction; R110
execution and independent review are pending. Sole author `/root/r110_proof`,
assignment `R110-PROOF`, revision 1. Governing contract:
`tasks/agent-loop/sprints/cli-entry-demand-20261019-r110-rev1.md`, SHA-256
`d651d326981e1b27bb329b3655ccd612809a1c871f67511baf365cd7d0082976`.
Its literal status is DRAFT_FOR_PRE_EXECUTION_REVIEW; the primary's actual
assignment authorizes this construction, not an assertion of review approval.

## Original obligation and exact finite inputs

The parent direction is §21 entry according to the original formal annotation,
with §17 whole inert argument introduction and entry in the same receiving
invocation, as stated in the pinned R97 proof/contract. R110 applies that
ordinary-entry premise to two exact source strings and asks whether the public
stdin CLI publishes their finite outcomes. This note borrows the historical
constructor evidence within its actual premises; it does not reread or extend
unlisted parser/HIR/solver owners or independently reprove the charter.

Each string is the literal prefix `act signal:\n    our ping: () -> int\n`
concatenated with the corresponding body below, with no final LF:

```text
V: my loop x = loop x
   my ignore x = 9
   my main = ignore (loop ())

C: my loop x = loop x
   my ignore (x:[] int) = 9
   my main = ignore (loop ())
```

The indentation after `V:`/`C:` is presentation only; actual binding lines all
start at column zero. V has 97 UTF-8 bytes, SHA-256
`1c1d1d5d98c1acc3148f199408cb1324a4c1fee3aa4474034ed7495d7ee54446`;
C has 106 bytes, SHA-256
`ac926feeb27c26d81f8545ac05810dbcf7f8dd60719b84fee316db2417b8ec73`.
Both lengths, digests and absent terminal LF were checked by literal assembly
and hashing only; no parsing or execution was run by this worker. The retained
Act declaration is present in both historical R97 cells. Neither cell calls
ping, installs a handler or resumes a continuation.

The fixed subprocess arguments are `--run main --steps 10000 -`; scoped
experiment is absent. Each child gets its own source, preparation and machine.
All source identities created by the CLI use its own module/FileKey brand;
no R97 formal ID or R103 SourceSite is asserted equal across these separate
preparations.

## What the reusable evidence actually establishes

R97's six-cell test `section21_outer_annotation_selects_entry_for_ignored_arguments`
contains these exact V and C cells in `runtime_control.rs:157–196`. Its helper
at `:16–44` asserts empty syntax diagnostics, successful authentic LocalSource
lowering and ordinary CandidateInference solve with no conflicts, then builds
RuntimeProgram with default evidence, selects main, obtains execution_roots and
starts that schedule. The executed assertion for V is exactly
`ResourceExhausted { .. }` after `run(10_000)`. The executed C assertion checks
Completed Integer `9`. The pinned R97 closeout reports that sole command passed
all six cells after CLEAN fresh reviews. This is finite prior candidate/runtime
evidence, not a universal constructor or divergence proof.

R103's pinned proof and CLEAN closeout add the finite structural projection for
the same C source. The historical source argument follows
`plain_binding_header`/top-level parameter formation -> `local_source::form`
and `Builder::set` -> annotation owner/key/outer-row retention -> authentic
LocalSource -> RuntimeProgram Lambda -> RootCompSchema. The observed R103 test
checks original formal identity, annotation components and runtime schema/site
projection. Its exact C source has a distinct loop formal and ignore formal,
even though both are spelled x. The unannotated loop formal has no annotation;
ignore retains an Int endpoint and a present empty outer effect row, including
its original row key. Empty contents do not erase row presence. R97 already
supplies acceptance and bounded execution of this exact C cell.

For V, the R97 original-formal/source trace and finite run are the reused
ordinary unannotated premise; R103 does not newly establish V's projection.
R97's historical proof/handoff predate execution, so their original UNOBSERVED
labels are read with the later closeout, without rewriting them. R103's original
proof likewise is not treated as its own independent certification.

R105 supplies an already executed public stdin subprocess convention. Its
wrong/sibling permission result concerns its own sources and is not evidence
that either R110 cell has already run through the CLI. The pinned existing
`cli.rs` helper shows pipe creation, exact stdin byte write, closing the taken
stdin handle and `wait_with_output`; `cli_entry_publication.rs` demonstrates
status/stdout/stderr assertions. R110's new test is independently leased and
not a coauthored input to this proof. This note specifies required observations
from the contract; it has not inspected or certified that writer's output.

## Direct source trace on the pinned current runtime

1. **Preparation and authentic role.** `main.rs::run` parses `--run main`,
   positive `--steps 10000`, and source path `-`, reads stdin using
   `lib.rs::read_source`, and calls `execute` with scoped=false. The read keeps
   the UTF-8 bytes intact subject to the 65,536-byte cap. `lib.rs:266–342`
   parses, checks diagnostics, lowers with LocalSource, performs ordinary
   CandidateInference::solve and rejects conflicts before constructing the
   runtime. This does not bypass generation, accumulation, propagation, levels,
   extrusion, qualifying intrusion or generalization. Those internals are
   borrowed only through R97's actual preparation receipt; no new inference
   theorem is claimed. CLI uses FileKey("inference-playground", "-") whereas
   R97 used FileKey("runtime-control", "test.yu"). The CLI preparation must
   therefore succeed anew; prior execution is not that new observation.
2. **Instruction emission.** `RuntimeProgram::from_hir` retrieves authentic
   LocalSource (`program.rs:249–330`). Its roles table (`:414–440`) and Lambda
   constructor (`:488–508`) use annotation.ty.effects.is_some(), not a solved
   effect support or whether the body mentions x. The Lambda keeps parameter.id
   and the entire argument Apply is represented by its callee and argument
   labels (`:509–515`). Groups forward to their whole inner label (`:483–486`).
   The C annotation selects Computation; V and loop select Value.
   `RootCompSchema::from_parameter` (`receiving.rs:21–43`) requires matching
   annotation owner and formal root, a present outer row and a primitive ground
   endpoint, and clones the original formal plus Lambda SourceSite. The R103
   positive predicates hold for C ignore; an absent annotation gives no schema
   for loop or V ignore. Schema absence is not a global nonprotection theorem.
3. **Source schedule.** Lambda definitions are fetchable values, while main's
   Apply makes main a scheduled computation (`program.rs:570–600`). Thus merely
   defining loop does not execute its recursive body. `start_source_schedule`
   calls the actual `start` with that schedule (`machine.rs:288–372`), initially
   with owner ModuleRun and zero steps. Main is materialized on its schedule;
   `Frame::Root` stores its successful result and `begin_root` completes the
   selected cached main (`:1210–1218,1805–1862`). Closure fetches may be cached;
   executing a Delay is not a cache of argument execution. This same source
   schedule is what R97 obtained using execution_roots/start.
4. **Whole inert argument, then receiver.** Lambda evaluation retains the exact
   formal, role, schema, body and lexical environment in its closure
   (`machine.rs:630–644`). Apply evaluates only its callee and saves the whole
   argument label and caller environment in Frame::Callee (`:645–656`). On
   callee return (`:879–902`) it allocates one Delay containing that entire
   argument label and lexical environment. It executes no prefix of `(loop ())`
   during allocation. `direct_formal_root` (`:1478–1491`) only inspects a direct
   Execute Parameter Name; a grouped Apply is not such a direct formal.
   `new_invocation` (`:1248–1267`) then mints activation a with actual call and
   provider sites and sets current_owner=Invocation(a). ReceiverReturn is
   installed before choosing either parameter role. The Delay is inert code
   plus lexical references, not a captured handler/store snapshot.
5. **V entry demands inside that receiver.** Value branch (`:969–979`) installs
   Frame::ValueEntry with the original parameter, body and closure environment,
   then executes the entire Delay. Delay execution (`:1929–1934`) changes only
   code/environment; it does not replace Invocation(a). If the argument returns,
   ValueEntry binds that result with Value interface and begins ignore's 9
   (`:1081–1099`); ReceiverReturn retires a only after completion
   (`:1070–1080`). Recursive loop applications create their own nested receiver
   invocations while a remains live. The loop closure's Value formal receives
   Unit, its body applies the module loop to its original formal again, and no
   inspected body path produces a return to ignore's pending ValueEntry.
   This explains the finite-exhaustion prediction using R97's exact observed
   V cell; it does not prove unbounded execution or mathematical divergence.
6. **C entry binds without executing the argument.** Computation branch
   (`:980–1009`) enters the original schema for activation a, preserving the
   inherited delay view, and records the original-formal receipt
   (`receiving.rs:130–175`). It binds the Delay itself with Computation
   interface and begins body 9. This branch calls no execute on that Delay.
   The literal body never reads x and provides no other consumer of its code.
   ReceiverReturn then retires a; main's root result can be cached and completed.
   The entry order is established by these source branches; the forthcoming
   CLI stream assertions do not instrument or independently measure each
   internal allocation/ownership transition.

## Finite fuel and publication mapping

`Machine::run` (`machine.rs:482–492`) calls step at most the supplied budget.
`step` increments its counter for each live transition (`:495–519`). A stopped
outcome is returned immediately; otherwise consuming the loop budget yields
ResourceExhausted with the current step count. For this initially zero-step
machine, 10,000 live transitions without an earlier stop predict steps=10,000.
R97 asserted the ResourceExhausted variant, not this CLI diagnostic text or
its counter value. The new finite subprocess observation must supply those
boundary facts; the prior test cannot stand in for them.

`lib.rs::execute` (`:167–202`) returns an Err on ResourceExhausted containing
`runtime step budget exhausted after {steps} steps; no completed result`.
It constructs formatted normal output only after Completed and a valid value
handle. An Integer 9 is written as `9` followed by LF into the bounded Output,
then finish returns the whole String. `output.rs` retains output privately and
fails atomically at its caps. `main.rs` executes `print!("{output}")` only after
the execute Result succeeds; an error reaches main, which eprintlns it and
returns ExitCode::FAILURE. Success returns ExitCode::SUCCESS. Therefore the
conditional finite boundary predictions are:

| Exact cell | Required R110 external observation | What remains unobserved here |
| --- | --- | --- |
| V | unsuccessful exit, empty stdout, stderr containing the existing step-budget-exhausted diagnostic | new CLI preparation, finite exhaustion and actual streams/status |
| C | successful exit, stdout exactly `9\n`, empty stderr | new CLI preparation, completion and actual streams/status |

No new diagnostic or exit code is prescribed. The V assertion concerns
unsuccessful status, not a chosen numeric error code. Compiler warnings from
building the test would be separate Cargo process output, not the child's
captured runtime stderr. A preparation error would also withhold stdout but
would fail the contracted exhaustion observation; empty stdout alone cannot
establish correct entry. A timeout, wrong output, unexpected diagnostic or
source mismatch stops this packet without repair/retry.

## Parent application, missing evidence and exclusions

This construction connects existing finite ordinary source/role evidence to
actual CLI preparation, source schedule, machine outcome and publication
owners. It reduces R110's next seam to one exact two-child subprocess test
under fresh eligible post-output reviews. `R110-CLI-RUN-1` is owned by Luna:
verify the independently frozen test implements both exact stdin strings,
arguments and serial observations, obtain CLEAN spec and compiler/source
reviews, then run only the single contracted command once. Any mismatch or
wrong observation falsifies this finite boundary prediction and ends the
packet. This proof lane proposes no production implementation change; the
inspected owners already implement the two branches and output mapping.

The result remains candidate/conditional until review and the new observation.
Even a passing R110 test would close only the finite CLI claim for these two
strings. It would not prove universal §21, source-wide preparation completeness,
mathematical divergence, general eagerness/safety, effect hygiene, continuation
or foreign-continuation quantifiers, evaluator correctness, original Simple-sub
A/B, semantic adoption or production authority. Method/role work still needs
its authentic executable binder and typing/lookup/dispatch consumer; ordinary
entry is only a reusable premise when that exact boundary is preserved.

`R110-PARENT-SCOPE-1` remains with Luna: retain broader parent quantifiers,
source domains and owners; extend only under a separately frozen contract.
R109's nested-handler source-range mismatch is unrelated. Its source, test,
expectation and failure have not been read as inputs, altered or diagnosed
here. Other hygiene fronts remain independent. This packet does not revive
withdrawn inference bypasses or collapse residual/provider/witness lineages.

## Dependency freeze, provenance and resource receipt

All 22 input pins in the R110 contract matched actual SHA-256 bytes before
construction. No unlisted proof/source owner was read. Direct evidence used:

```text
77b4ea777a2fd413b356b5128cc55362f1126e6298bcb7c310f776cfd53b4b98 notes/theory/2026-10-19-r97-value-computation-entry.md
aa06b04ff9ad0fb882c89c26e0375fd21eddba489c44b7d54f6156585a66d734 notes/progress/2026-10-19-r97-value-computation-entry.md
2619e4c8bb006e2d98cf81887091ae372cb1ae3731de76e7b707a97db577009c tools/inference-playground/tests/runtime_control.rs
114f5bcfa31a50ffc6111364f28d1e0f1abe41d94030dc1a5afc3d4e66756c74 notes/theory/2026-10-19-r103-parameter-projection.md
c2cf5b99d0948a016792b62199ada85b87ee2f7d18a93dc66d2d6e11bb0abe0d tasks/agent-loop/inbox/20261019-r103-proof.md
701abe0a6f319eab8c282281ff66f66a63a8758becd238b44d30581894d49377 notes/progress/2026-10-19-r103-parameter-projection.md
8b1662794800df84b65839c27d3536ed7b05068e6c74955ed44f6b86377b7a07 notes/progress/2026-10-19-r105-cli-receiver-permission.md
ac2ba1cb201f35c79dbc67d140012b2c5db4b43c2395efe804be7e9a11f9535e tools/inference-playground/tests/cli_entry_publication.rs
cf265feba7414b159353c81751608e9c127b072559b2c8c4cc513ecbc15c22ea tools/inference-playground/tests/cli.rs
75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100 tools/inference-playground/src/main.rs
bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b tools/inference-playground/src/lib.rs
04e99c5bdb562a8edb8a7e17bdcc03f7b46eaca9d8e13b20216b4dcf3032a88a tools/inference-playground/src/output.rs
fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46 tools/inference-playground/src/runtime/machine.rs
7bc27580711d3ef09044e324541904ef3388aca8e3b4f3a72437b1e04dc0210a tools/inference-playground/src/runtime/program.rs
8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9 tools/inference-playground/src/runtime/receiving.rs
```

Sole current author `/root/r110_proof`; no coauthors or descendants. Historical
proof authors remain `/root/r97_proof` and `/root/r103_parameter_proof` with
implementation authors/receipts and Luna's integration as recorded in their
pinned handoffs/closeouts; no self-certification is inferred. Requested
model/effort: Sol/high (`gpt-6.1-sol/high`); observed effective model/effort:
UNKNOWN/UNKNOWN, absent independent runtime metadata. Actual launch receipt:
this session's NEW_TASK from `/root` naming R110 and the two exclusive paths.

Resources: 360-second proof cap, Astra 0, no renewal; exact aggregate active
work spent/remaining is UNKNOWN. Checks comprised bounded text reads, pin and
literal-source hashing, and writing/hashing these two leased artifacts. No
tests, build, compiler/runtime/formatter, CLI, Git, external contact or scratch
files. New outputs are this note and
`tasks/agent-loop/inbox/20261019-r110-proof.md` only. Writer stops at immutable
handoff submission; reviews, command and integration remain with Luna.
