# R113 finite expression cursor: conditional partial source evidence

Status: **STOPPED_INPUT_BOUNDARY; no complete R113 claim**. This is a producer's
conditional source/control argument, not an independently reviewed theorem,
an execution receipt, or production authority. Payload decoding to native 99
and public preparation success remain **OPEN**. Luna explicitly adjudicated the
new-owner boundary as a hard stop under rev3; no decoder source was read.

Author: `/root/r113_proof`, sole author; no descendants. Requested model/effort:
Sol/high. Observed effective model/effort: UNKNOWN/UNKNOWN. No model switch is
claimed. Exact exclusive outputs are this note and
`tasks/agent-loop/inbox/20261019-r113-proof.md`.

## Parent, accepted input and actual application

Parent: the finite source path and public observation fixed by
`tasks/agent-loop/sprints/cli-outward-expression-suffix-20261019-r113-rev3.md`,
SHA-256 `f58944ee47053d6808c52fcc37a2fa97690f091a8d8f31942c433a1fe042559f`.
The source is exactly 83 UTF-8 bytes, without final LF:

```yu
act io:
    our tick: int -> int
    our other: int -> int
io::tick 99; my main = 7
```

Source SHA-256:
`f80549d67af6ffb8d402e5f469c7b3e7c22c7ec971377de47c2cb6c469d33f63`.
The byte count and hash were checked directly from this literal. The accepted
program, original Simple-sub behavior and original broader theorem quantifiers
are unchanged. No claim about all programs, all effects, arbitrary continuations,
F1/FK1, A/B, source initialization adequacy or a native suffix theorem follows.

The useful result applies to the parent at its missing exact-cursor premise:
the inspected production constructors retain `ExpressionReturn { root: e,
next: 1 }` without replacing it by continuation depth, a definition root, or a
claim about a later execution-root list. The complete fixed-source result is
still OPEN because the native decoder and preparation bridges are unestablished
within this pin set. No conditional reformulation is recorded as parent closure.

## Inspected construction and finite control argument

Write `e` for the authentic expression root of the retained `io::tick 99` item,
`L` for its compiled body label, and `d` for the selected `main` definition index.
The following argument is conditional on the fixed source reaching its intended
supported HIR/carriers and runtime construction, and on its ground-value/helper
steps succeeding. These entry premises have not been silently discharged by the
historical test.

1. `program.rs::RuntimeProgram::from_hir` visits `hir.items()` in order
   (`:275` onward). An expression obtains its root by
   `hir.expression_root(expression.occurrence())`, then obtains its actual
   carrier by `hir.local_source_for(&source_root)`. It compiles carrier forms
   directly: Operation retains `SourceOperationResolution`; Apply retains the
   callee and argument labels; Integer retains its spelling (`:450–552`).
   Each `Code.site` clones the same carrier owner, occurrence and range
   (`:555–565`). This is a source-preserving join on returned carriers; it
   does not prove that public preparation returns those carriers for this input.
2. The runtime schedule classifier (`program.rs:570–612`) includes every
   authentic expression and includes only the computed-definition subclass.
   Given the intended carriers, `main` has Integer body, so it is retained in
   `definitions` but contributes no `ExecutionRoot::Definition`. The schedule
   is exactly `[Expression(e,L)]`; registered Act placeholders are skipped by
   their explicit error/declaration check. The live selected index remains `d`.
   There is no second scheduled entry representing textual `my main = 7`.
3. `RuntimeProgram::start` (`machine.rs:299–378`) authenticates expression
   root membership and its exact root/label join, creates empty cells and frames,
   sets `current_owner = ModuleRun`, and calls `begin_root(0)`. In
   `begin_root` (`:1806–1857`), fetching the sole root increments the cursor
   from 0 to 1 before pushing `Frame::ExpressionReturn { root: e, next: 1 }`.
   It evaluates `L` in environment 0. It neither evaluates the selected
   fallback nor installs an expression cache cell.
4. The inspected Apply/operation path retains the actual declaration and
   application site (`machine.rs::evaluate`, `return_value`, `:1010–1070`).
   Returning the resolved Operation to `Frame::Callee` allocates an inert
   argument delay. The declaration's `int -> int` value argument selects
   `OperationPayload`; the result consumer is the actual operation declaration
   consumer. Stack order, bottom to top, is expression return, operation result
   consumer, receiver return, operation payload. Evaluating the argument calls
   `literal::integer(text)` on its retained spelling. **The result of that
   decoder is not established here.**
5. If that argument step succeeds with received payload `p`,
   `Frame::OperationPayload` calls `make_request_carrier`, retaining the exact
   declaration, `p`, and original Apply `SourceSite`. `ReceiverReturn` restores
   the previous ModuleRun owner. `OperationResultConsumer` executes that
   carrier; `Machine::execute` (`:1929–1957`) moves its declaration, payload and
   original source into `PendingRequest`, with a fresh event and empty suffix.
   No Catch is installed on this finite path. At this point the live frame
   stack consists solely of `ExpressionReturn(e,1)`.
6. This last entry state gives a direct two-transition proof of exact cursor
   retention. In `propagate_request` (`:1531–1761`) the last frame is neither
   CatchReturn nor GlobalRead. Popping `ExpressionReturn(e,1)` therefore selects
   the `ordinary => SavedFrame::Ordinary(ordinary)` arm and appends the same
   frame to `request.suffix`. This arm invokes neither `return_value` nor
   `begin_root`. The next propagation sees an empty live frame stack and calls
   `stop_unhandled_request`. That function (`:1763–1776`) moves
   `request.suffix` directly into `SavedContinuation.frames`, moves its
   observations, and stops with the same source, declaration ID, payload handle
   and event. Thus the saved vector is exactly
   `[SavedFrame::Ordinary(Frame::ExpressionReturn { root: e, next: 1 })]` at
   this conditional entry. Exact identity follows from move construction,
   independently of the positive-depth accessor.
7. The only normal expression completion arm (`:1204–1210`) would validate `e`
   and call `begin_root(1)`. At 1 this schedule is exhausted; the separate
   selected-definition fallback (`:1844–1857`) could then evaluate `d` if its
   cell is empty, with a cache-bearing Root frame. The unmatched-request path
   in step 6 never takes that completion arm. Its terminal state prevents that
   fallback from evaluating or publishing `main = 7`: `step` first returns any
   stored stopped outcome (`:494–498`), and `run` returns the first non-Running
   outcome (`:483–491`). The initially empty main cell is not written by the
   operation/application/request path. This is withheld fallback execution,
   not preservation of a nonempty remaining ExecutionRoot suffix.

`continuation.rs` defines immutable ResumeTemplate nodes, including Bind with
a Frame, but the unhandled saved vector here is `machine.rs::SavedContinuation`.
No template is entered on this path. Storage of this frame establishes neither
resumption behavior nor the foreign-continuation quantifier of any other theorem.

## Original HIR provenance and public consumer

The HIR source-owner API uses a private `ExpressionRootId`, an occurrence-root
registry and membership checks (`module.rs:331–337,953–965`); its direct-expression
construction and carrier ownership are the relevant original owners
(`:1234–1243,1312–1315`). The inspected runtime never manufactures an expression
root from a definition or from range arithmetic. `Code.site` is copied from
the carrier expression; `make_request_carrier`, PendingRequest and
`stop_unhandled_request` retain that site. In particular the request site is
the Apply occurrence retained by the operation consumer, not a handwritten
span and not a substitution of the operation declaration's source location.
This audit has not reconstructed a numeric range for the fixed source.

`lib.rs::execute` first calls `prepare`, then `RuntimeProgram::from_hir`, selects
`main`, and starts the retained source schedule (`:166–179`). If the conditional
path above reaches UnhandledRequest, its result match returns
`Err("unhandled runtime request at " + Debug(source.range))` (`:180–189`).
Output construction occurs only after that match. `main.rs::run` passes stdin
from `read_source` into execute for `--run main --steps 30000 -`, and `?`
returns the error before `print!("{output}")`; `main` writes that error to stderr
and returns failure. `output.rs` also buffers successful output, but the earlier
error branch already withholds all successful result rendering here. Consequently
empty stdout/failure/exact HIR-derived diagnostic follows **if preparation and
the specified machine path succeed within the budget**. No child process or
runtime observation was performed by this author; that premise remains OPEN.

## Exact obstruction, prior evidence and mutual TODOs

**R113-PROOF-NATIVE-99 (OPEN):** the current pinned
`machine.rs::evaluate(Integer)` calls `runtime/literal.rs::integer(text)`.
That owner is absent from rev3's frozen inputs. Retained spelling `"99"` is
established by the constructor mapping; native decoder return `Some("99")`
is not. The decoder was not read, assumed correct, or added as a dependency.
Luna must decide a later exact input allocation if a source proof of this
bridge is required. Falsifier: the actual decoder refuses or returns a value
different from native integer 99 on the retained spelling.

**R113-PROOF-PREPARE (OPEN):** `lib.rs::execute` has an earlier fallible
`prepare`/CandidateInference boundary. Successful construction and admission of
this exact 83-byte source have not been observed in this packet. The owning
consumer is `lib.rs::execute`; the prepare/inference construction retains its
own source owner and accepted Simple-sub obligations. First missing evidence is
the authorized exact-source public test/prepare observation, not another proof
of saved-vector storage. Falsifiers include preparation failure, a different
carrier/operation identity or range, and budget exhaustion instead of the fixed
unhandled outcome. Any broader source proof needs Luna's explicit frozen inputs.

**R113-PROOF-INTAKE (Luna):** preserve this partial result as stopped evidence;
do not promote the requested complete finite claim, repair the contract in
place, or run a command on the strength of this note. Luna owns the remaining
assignment/review/resource disposition and compiler/source reviewers. The author
cannot certify this result. The next in-envelope step was freezing the evidence;
that step ends this assignment at its hard input boundary.

The pinned historical runtime theorem is reused only for its distinction
between source provenance, ModuleRun scheduling, normal completion and the
separate selected-definition route. The carrier theorem is reused only for its
authentic-root/retained-carrier ownership explanation within its original
entrypoint premises. Their older internal production hashes do not prove
correspondence for the present implementation automatically. The existing
`expression_request_retains_original_provenance_and_pending_suffix` test asserts
Expression provenance and positive depth; it supplies neither exact saved
cursor identity, operation/payload assertions nor a public CLI receipt.
R99's fresh-receiver law, a general suffix theorem, whole-source admission and
initialization adequacy are not imported.

## Frozen direct inputs and resource receipt

All 15 rev3 pins below matched on initial inspection; no mismatches were found.
No dependency was expanded. The two governing approvals retain their scope and
leave their broader source/initialization premises OPEN.

| Input | SHA-256 |
| --- | --- |
| `tools/inference-playground/tests/runtime_module_expressions.rs` | `8eaad5f05b2592ce068f6ed2ed2e7934eaad68e368f4f60b8e3a60e59cf9ff1f` |
| `notes/design/2026-10-16-module-expression-source-owner.md` | `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5` |
| `notes/design/2026-10-16-initialization-order-global-effects.md` | `e2f70f535319522261cc6f52592d62b491d9d0e9d32e14310ac5d9fb81ee1bb6` |
| `notes/theory/2026-10-16-runtime-module-expression-roots.md` | `915f99eb5cbd9734c3d1e4e0b778682bf1dbb3a8044ea21d5d77cee9d7250694` |
| `notes/theory/2026-10-16-module-expression-carrier-correspondence.md` | `600391db278adf29c955b407e3586b2e351994d7a8a7aa5003349fe72209d39a` |
| `crates/yu-hir/src/module.rs` | `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a` |
| `crates/yu-hir/src/module/local_source.rs` | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` |
| `tools/inference-playground/src/runtime/program.rs` | `7bc27580711d3ef09044e324541904ef3388aca8e3b4f3a72437b1e04dc0210a` |
| `tools/inference-playground/src/runtime/machine.rs` | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| `tools/inference-playground/src/runtime/continuation.rs` | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |
| `tools/inference-playground/src/lib.rs` | `bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b` |
| `tools/inference-playground/src/main.rs` | `75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100` |
| `tools/inference-playground/src/output.rs` | `04e99c5bdb562a8edb8a7e17bdcc03f7b46eaca9d8e13b20216b4dcf3032a88a` |
| `tools/inference-playground/tests/cli.rs` | `cf265feba7414b159353c81751608e9c127b072559b2c8c4cc513ecbc15c22ea` |
| `tools/inference-playground/Cargo.toml` | `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56` |

Method: bounded constructor/consumer inspection plus exact frame-move case
analysis, applied directly to the finite parent's cursor and withheld fallback.
Checks: all pins and literal hash/count; source inspection only. An initial
`python` hash command was unavailable; one Python3 table-extraction attempt
failed before validation because its regex crossed table lines; corrected
line-scoped extraction then checked every pin. These were metadata checks,
not compiler/runtime probes. No test, build, CLI/runtime, formatter, Git,
production edit, external contact or delegation occurred.

Allocation: 600 seconds, reserved against R113's existing 1,500-second budget;
stopped within that allocation. Exact elapsed active time is UNKNOWN; no time
is reclaimed here. Astra 0; heavy processes 0; runtime/probe samples 0.
All new paths are the two exact leased outputs; scratch paths: none.
Writer status after handoff freeze: **STOPPED_INPUT_BOUNDARY; writes stopped**.
No descendants or unresolved descendant leases exist. Review/integration and
all shared-record synchronization remain Luna-owned.
