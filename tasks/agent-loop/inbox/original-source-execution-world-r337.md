# R337 original execution world — revision 1

Assignment `R337-WORLD`; author `/root/r337_world`; supplied baseline
`ac995af26`. Contract `tasks/agent-loop/sprints/original-contract-family-r337.md`,
SHA-256 `b4dc9ed1e68303300af636481dbe689e42bbd9780ba3a89a41e92df88a36e9a1`.
Requested role `astra_prover`, normal requested effort medium; observed
model/effort UNKNOWN. Runtime identity available to this worker is the display
path above; no independent session identifier was exposed. No descendants.

Outcome: **checked conditional falsifier / source-native evidence**. Six
theorems apply the original result consumer to reject a specific incorrectly
joined event interpretation. This is not a counterexample to EI, a constructed
original execution interpretation, or closure of R311/R306/R159. The native
world projection is universal over its represented worlds; its identification
with the selected source's complete original semantics remains an obligation.

## Parent claim and actual application

EI §§3.1–3.4, GR3 and the complete-Call Return/future clause require the actual
receiver result, its original provider and current event, with all original
response/current-world/future domains and lawful whole actions retained.
`OriginalSourceInterpretation.function_return_result` is unchanged. It takes
the same Function row, genuine membership, actual provider, admitted complete
challenge, actual raw execution, checked trace readout and pure Return form,
and concludes `result.event = raw.event ∧ Meaning inputs (.value result)`.

R335's native `Frame::ReceiverReturn` observation is recorded **before**
`leave_owner`; its later matching selected-definition result authenticates
the returned value/view/interface/dispatch, not equality of their worlds.
The checked R337 application proves that interpreting the first raw event as
the pre-exit world and the result at the successful post-exit world cannot
satisfy that original consumer. It does not claim R335 already makes this
incorrect interpretation: this is a precise falsifier for a proposed bridge.

The argument is stronger than the fixture's owner `Invocation(8)` versus
restored `Invocation(6)`: every successful existing `returnOwned` retires an
active invocation, so the full represented world changes even if an invalid
saved previous owner equals the retiring owner. It uses no assumed injectivity
of opaque original sorts. `OriginalParameterSemantics.nativeSorts` explicitly
sets Configuration to `Snapshot`, whose `world` is the existing complete
represented `World`. The theorem applies only to those existing sorts; no
isomorphism with arbitrary fixed `Sorts` is claimed.

The positive parent edge is still OPEN: there is no derived selected-source
`inputs.execute`, `checkedObservation` or `traceForm` equation, original
semantic result-provider map, full current-world certificate, or lawful
whole-action/response-domain construction. R311's returned phase and R306's
licensed child are not supplied. No independent arm, F1/FK1 quantifier,
provider lineage, witness, or source behavior was removed.

## Checked declarations and exact premises

Namespace `YulangClosure.OriginalSourceExecutionWorldR337`. Full elaborated
types are in `/tmp/yulang-r337-world/WorldAudit.log`; the source contains the
complete binder lists. In the schemas below `S = NS b D V ViewData Site Rest
Body View`; every type parameter and every displayed object is universally
quantified, with no finite fixture restriction.

1. `leave_shape`: `before.leave id previous = some after` implies
   `before.current = invocation id` and existence of `rest, invocation` with
   the actual stack, registered cell and `invocation.active = true`, and
   `after = ⟨deactivate before.invocations id invocation, rest, previous⟩`.
2. `return_owned_fields`: `returnOwned before id previous input =
   some (after,output)` implies pre-current `invocation id`, post-current
   `previous`, `output = input.asValue`, exact preservation of environments,
   cells, receiving and rest, and `¬ OwnerActive after.control (invocation id)`.
3. `return_owned_changes_world`: the same successful-return premise implies
   `after ≠ before`. No owner-inequality or ControlValid assumption is needed.
4. `successful_return_events_differ`: for arbitrary `before after : Event S`,
   `returnOwned before.current.world id previous input =
   some (after.current.world,output)` implies `after ≠ before`. Other Event
   fields remain arbitrary; no unchanged assignment/witness assumption occurs.
5. `pre_exit_trace_rejected`: for arbitrary `inputs : Inputs S`, `before`,
   `result`, `observation`, `interface`, a successful native return from
   `before.current.world` to `result.event.current.world` and
   `inputs.traceForm ⟨interface,observation,before⟩ = pureReturn result` imply
   `¬ Meaning inputs (trace ⟨interface,observation,before⟩)`. This applies
   existing `return_observation_iff`.
6. `function_rejects_pre_exit_execution`: retains the original Function form,
   membership, actual provider, complete admitted challenge, checked readout
   and pure-Return form premises. If `returnOwned raw.event.current.world id
   previous input = some (result.event.current.world,output)`, it concludes
   `¬ inputs.execute provider challenge.input raw`. Its proof calls the
   unchanged `function_return_result` and contradicts the proved Event
   inequality. It does not assume the negated execute proposition.

**Complete axiom audit: all six depend on exactly `[propext]`.** The census
enumerates every theorem originating in this module, checks all six required
roots, rejects project axioms and any dependency outside standard axioms, and
reports `YULANG_AUDIT_COUNT 6`. No sorry/admit/checker bypass occurs. Three
text-search matches in the 18-module cone are ordinary comments.

## Source/native evidence and limits

Read actual `tools/inference-playground/src/runtime/machine.rs`:

- `Frame::ReceiverReturn` at 2480–2513 constructs the returned Value interface,
  preserves value/view/dispatch, records test evidence, then calls the fallible
  `leave_owner`, then installs `State::Return(returned)`.
- `leave_owner` at 3004–3032 requires the current owner, pops the active stack,
  finds and retires the invocation, and restores the saved previous owner.
  On successful branches these are exactly the existing `Control.leave` and
  `returnOwned` projection equations. Failed Rust branches may already have
  popped the stack; no error/rollback correspondence is claimed.
- R335's exporter at 5568–5608 joins selected Call/invocation, source provider
  site, return tuple and later cached completion. It supplies no original
  event interpretation. The provider `SourceSite` still denotes the invoked
  source callable, not a returned semantic provider of `Inputs.actual`.

The read-only R335 revision-2 artifact has SHA-256
`6783f166e8da158d2bb8047300999bc6eb60284a8027d3bf236905291306b5e7`.
Its selected receiver activation/current owner is 8, saved previous owner 6,
return value/view 4/5 at step 63, and selected completion is at ModuleRun at
step 73. No numeric identity from another run is joined to this run. The
artifact is **not** an import of the new proof and was not rerun or rechecked
here; its earlier review supplies only its recorded finite evidence. No
theorem asserts that this artifact already constructs an `Event S` pair or
the successful `returnOwned` premise at an original semantic event.

Investigated the other actual constructor route before settling this falsifier:
`OriginalReturnWorld.Packet.outcome` constructs a formal Value-entry
Return/rebind with allocation and explicit current EventFields; it is not
the enclosing receiver's return. `OriginalNameForceExtraction.inputs` owns
the Name-argument Force form and retains `base.execute` for other operations.
Neither may be relabeled as a whole-Call execution constructor. `ownedEvent`
reads an already interpreted Current and assignment; it does not derive
them from the R335 handles. No new event/Inputs semantics was added.

Reused R336's source-owner investigation and exact missing equations, the
existing native `returnOwned`/`deactivate_current`, nativeSorts representation,
and original `return_observation_iff`/`function_return_result`. Rejected the
temptation to use formal Return/rebind or Name Force for receiver Return, or
to choose an arbitrary Inputs instance with a desired traceForm. New progress
is the checked projection and parent-consumer falsifier, not another positive
conditional wrapper or a claim that R336's missing premise is discharged.

## Exact next owner / mutual TODO

`R337-WORLD-EXECUTION-1`, carried from `R336-RESULT-EXECUTION-1`, belongs to the
original execution interpreter and its source/native correspondence owner.
Construct the successful ReceiverReturn **post-exit** current projection at
the same source Call and continuation, then derive the original raw execution,
checked observation and Return form equations, result descriptor/root/provider
and event incidence at the original result endpoint. Preserve full admitted
response worlds, pending prefixes, remaining suffixes and lawful whole actions.
An existing interpreted Snapshot/Current producer can discharge the raw native
premise using `return_owned_fields`; filling arbitrary logical fields cannot.

Minimal provisional implementation TODO, only if the interpreter needs native
evidence: owner `Machine::return_value / Frame::ReceiverReturn`; retain a
successful post-`leave_owner` projection joined to the same activation/result,
separate from pre-exit diagnostics and later selected-definition completion.
Exact falsifier: a proposed bridge passing either the pre-exit snapshot or
the later ModuleRun snapshot as the immediate post-exit state must fail its
current-world join; changing only the active bit also defeats a pre/post
world equality even with equal owner IDs. This requests no production edit,
new global semantic model, or authority expansion. Additional finite logging
alone does not discharge universal execution, original provider or world laws.

Next proof step requires that source-owned interpreter, not another theorem
whose hypothesis is its desired readout. No such producer was found in the
inspected owner definitions. This is the genuine-obstruction stop condition;
the unchanged positive parent remains owned by Luna and OPEN.

## Checks, resources and freeze

Read-only `elan which lake` resolved
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
`lake --version` and `lake env lean --version`: exit 0, Lake
`5.0.0-src+eb6cafb`, Lean `4.35.0`, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

All commands ran in `/tmp/yulang-r337-world/project`, with `--no-cache env
lean -j1 -M2048`. The exact target was compiled with explicit `-o
.lake/build/lib/lean/YulangClosure/OriginalSourceExecutionWorldR337.olean`.
The isolated 18-module source cone was copied from the repository; unchanged
dependency oleans were reused from the previously checked R336 Union copy
only when that cached source was byte-identical. No shared cache was written.
The new module check and `WorldAudit.lean` / `WorldCensus.lean` checks all
exited 0; final target log is empty (no warnings). Integration/default-root
checks belong to the primary; this module is not added to public imports.

One initial target check failed on a dependent case rewrite (`found` had
already become reflexive) and issued two unused-simp warnings. The proof was
repaired, then strengthened to eliminate the owner-inequality premise; final
build and complete audits passed. `build-17.log` retains the failure. Two
read/manifest attempts used incorrect file paths and were corrected; neither
changed proof inputs. No mathematical counterexample or tool timeout occurred.

The 3000-second/eight-stage grant was not exhausted; five substantive stages
(owner audit, native projection, event distinction, parent falsifier,
verification/handoff). Exact total active seconds/CPU/RSS UNKNOWN. Checks
were one process at a time after Luna's checker grant; the slot was explicitly
released. No Rust test/build, Git, dependency/config change, production write,
external contact or descendant.

Frozen Lean source SHA-256:
`b6d524a13d74184d7b76e77c03be08ad3ed2183f21b958ee0c6d453a4e0be462`.
`WorldCensus.log`: `bbcf86a8ab770b4782d0c191da43e71b4973334774f91fd76d55a35732231677`.
`WorldAudit.log`: `f351815c14ef68d3846d190a5637f9991de367393ec605ce8a740648fa9edb2d`.
Exact 36-path authority/source/dependency hashes are in
`/tmp/yulang-r337-world/final-input-hashes.json`; the import order, initial
dependency hashes and check commands are retained alongside it.

New repository paths: the leased Lean module and this exact handoff. All
scratch writes are below `/tmp/yulang-r337-world`: isolated `project/`
(18 sources, unchanged project files, local oleans, `WorldAudit.lean` and
`WorldCensus.lean`), dependency-order/hashes JSON, commands JSON, initial and
final build logs, explicit audit/census logs, theorem list, input manifest and
source-search audit. The final scratch hash receipt enumerates their files.
No other path was written; existing proof/source authors are unchanged.

**STOPPED; all writes stopped after revision-1 freeze.** Source bytes were
separately frozen and sent to Luna before this handoff. No worker/process is
running in the background. Independent review, acceptance and integration
remain with Luna; this producer supplies no self-certification.
