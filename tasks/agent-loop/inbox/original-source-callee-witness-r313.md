# R313 original source Callee witness — proof handoff revision 1

Sprint: `tasks/agent-loop/sprints/source-callee-witness-r313.md`, SHA-256
`fbcc6748d0fcb2459670109f254064f64efce648cc020ad6b9a044700fbde1a9`.
Assignment `/root/r313_callee_proof`; baseline
`2bcca07070de18415abde1515cbfaa38e09bfb35`.
Outcome: **checked conditional source/native data refinement; parent REDUCED,
not CLOSED**. Independent review and source/native adjudication are pending.
No production authority, Git, compiler edits, children or shared-status writes.

## Authority, original parent and quantifiers

Read root AGENTS.md / AGENTS.pre-sprint.md, goal-driven-sprints, the fixed
packet, Lean skill and source/execution references, and proof portfolio.
Semantic authority is selected `notes/design/2026-10-24-computed-call-result-constructor.md`
§§2–5, especially §3.1 pending callee and §3.2 actual same CalRet/argument
formation, SHA `2f3a5461b6dacaa29e881ba8b3003120b912e441dd5e4c47fc4ccaa27d3b31a6`.
The CB draft's original unconditional CB2/CB3 are withdrawn; no draft is used
as an operational or semantic axiom. Original source constructors are
`OriginalSource.Source` / `sourceRules`, with lossless scoped allocation in
`OriginalScopedClosure.allocate` / `source`. Both App annotation alternatives
and all original child Programs/premises/Position route/telescope/frame survive.

Original global claim: intrusion preservation manuscript
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5,
SHA `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`,
with the birth-level correction
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6,
SHA `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`.
It remains universally quantified over the original supported source domain
and lawful histories, preserving one original scope/shared witness and all
independent alternatives. `SourceProblem.InferenceSoundness` remains a Prop
definition, not a proved concrete instance.

Exact local parents inspected and retained:
`YulangClosure.SourceAppAdmissionR159.app_admission_iff` (all original locals,
both finite checks and both arbitrary source children in the same extension),
`YulangClosure.ComputedCallUnionRealizationR293.app_result_pair` (genuine
Checking plus actual trace membership, preserving arbitrary original arms),
and R311 `calRet_introduction` / `designated_force_from_carrier`.
No parent statement or source domain changed.

## Frozen outputs and dependencies

- `notes/theory/lean/YulangClosure/OriginalSourceCalleeWitnessR313.lean`, SHA
  `46494caab63654ad86bc16e0922d817ea1a77076e4f1d008485b049e916d197b`.
- Owned scratch `/tmp/yulang-r313-proof/ParentApplication.lean`, SHA
  `9d0216f25c302e6242653a22fd5c23b3f62bbe810cde27ca1700543b55ddedd5`.
  It is checked against the real R311/R293 consumers; it is not a root import.
- Frozen native R2 receipt copied unchanged to
  `/tmp/yulang-r313-proof/native-witness-r2.txt`, SHA
  `7e98da35f51301ff0524cc7ea8b332532e17deb42afc80e029ab4a07e7443ea7`.
- Native R2 machine input SHA
  `9e74fe2e071df6c8e723707f608fdbe069dea45a55589bc26b102ec6b7c32ae7`;
  program SHA `9c280992897b5664fef12e38df8161c4f1561a2d69654b1f5e1146339a3ca903`;
  native inbox revision-2 SHA
  `5a9c260f43637465192ff8c0c499e18f017f0c513d1e6c6cdf4c085a2fa1f838`.
- R312 history SHA
  `c2e5aef86baa66304c6c575c67dd9b3cfb83f539f796e4832ffe6aa88c05dff8`;
  R312 application SHA
  `4bab607556ba9d0f89cb61db17ce8894fd87b9c0d14d44bc98437be9c03d4a26`.

All authored Lean declarations are under
`YulangClosure.OriginalSourceCalleeWitnessR313`, except the scratch
`R313ParentApplication` namespace. All writers/authors: this leaf only;
R312 reused constructions retain their existing authorship. Native data comes
from `/root/r313_callee_native`; no native check was rerun or certified here.
Requested/observed model and effort, runtime-session identifier: UNKNOWN in
available runtime metadata. Actual assignment identity is the parent-issued
`/root/r313_callee_proof`; this report is its active-work/cessation receipt.

## Constructed and applied edges

`original_call_occurs` computes the original App rule from the actual original
builder for arbitrary Position, Context, callee and argument; it handles both
annotation choices. `SourceApply.toApplySource` requires an explicit original
root occurrence and exact immutable code owner/source joins; it computes the
R312 call rather than accepting an arbitrary `CallOccurrence` record.
`both_operand_decodes` and `source_enter_saves` retain the actual Apply and
BOTH operand labels, original root occurrence and saved caller environment.

The frozen fixture has receipt-local H0/S0 coordinates: Apply label8/occurrence12
at bytes113..118, callee label9/occurrence13 at111..112, argument
label10/occurrence16 at113..118. `Fixture.sourceCoordinate` retains these raw
coordinates separately from original source Site/Declaration coordinates.
`Fixture.codeArena` retains Apply8=(9,10), Apply9=(11,12), and Name10=parameter
Observe, with every other code row preserved by `otherCode`.
`Fixture.sourceApply` / `Fixture.preparation` compute the original source/code
adapter and R312 Preparation with caller2. The ONE original coordinate map,
full original root occurrence and actual original CalRet readout remain
explicit inputs; receipt-local integers do not prove that map exists.

`observe_has_no_inherited_root` computes the ordinary unknown Delay metadata
from this actual Observe instruction. `nativeAdapter` and `sourceNativeRead`
compute lexicalObserve through the actual executable Delay label and source
Name instruction, not a Boolean lexicalObserve input. Independent future
snapshot/cell/view equations remain required at arbitrary Reach events.

`Fixture.boundCaller` constructs the real R312 BoundCaller from the recorded
original caller bind (before cells5/environments2, parent0; bound cell5/env2,
Value4/view5), actual CalRet cells10/env7/views18 and the independently supplied
original event/coordinate readout. It is distinct from the returned closure's
later cell10/env7 bind. `Fixture.name_readback` APPLIES R312
`caller_name_evaluate` to this constructed caller and proves the computed
Name evaluation `.ok (5, Received(value4,Value,view5,None))`.
`initialized_name_force` applies R312's finite-prefix/receipt readback for all
n+2 fuels with actual source-derived Observe. `Fixture.exact_delay_operands`
proves fresh handle16, code10, environment2 and next value count17 from the
actual numeric snapshot counts. Allocation/capture require no whole History,
desired carrier Meaning or successful Force premise.

`Fixture.same_saved_frame_across_request` preserves native F2 in both the
pending and actual Return record while keeping current owners2 and6 distinct.
`calleeWitness` only constructs a returned triple after actual returned control,
top Callee with matching original Position/labels/environment, a returned
provider-vector lookup, matching Return view and an actual Closure executable.
`Fixture.actual_return_witness` applies it to Return Value15/view17; its
provider-vector and executable-to-original projections remain explicit raw
readout equations. Request and wrong saved caller environment return no witness.
This is not an original `traceForm=pureReturn` or `inputs.actual` proof.

The checked scratch theorem
`R313ParentApplication.r311_calRet_from_actual_witness` maps this witness to
R311 BoundReturn and applies `calRet_introduction`. It explicitly requires the
ORIGINAL callee trace membership, original Return-form equation, genuine
checked Function transport, Function sort and actual-provider relation.
The checked scratch theorem
`R313ParentApplication.r293_name_force_from_source` applies original R311
`designated_force_from_carrier` and R293 `injectSource`, with arbitrary original
arms and the source-derived Observe mode. The old History/carrier Meaning is
constructed by R312 from explicit independent all-Reach leaves, never an input.

## Precise remaining parent goals and owners

First missing source bridge: authenticate the native H0/S0 owner/occurrence
map to the FULL original root/Position/Context and the original event readout
(including the shared scoped witness); `SourceApply.present` and actual
`calRet` alignment/readout equations are not derived from one run. Owner:
original source/event correspondence lane, coordinated by primary.

Then R311 CalRet still needs callee membership, original Return-form and
actual-provider interpretation, and genuine Function checking; owner: original
callee/source interpreter and Checking owners. The raw same-event tuple and
Closure tag establish none of these.

For carrier membership: every original Reach world/license/inert/capture/demand
law; actual future snapshots/cell and view preservation; all observation-prefix
compatibility/coherence/guards/fields. Owners: native world/history, original
license and observation/future interpretation. `sourceNativeRead` supplies
only executable/mode projection, not these semantic laws.

For original whole Call/result: independent challenge q_c and ALL arm laws,
full phase/IF/action/response/future interpretation, original target Checking
and R159 local admission/children. Owners: original EI/Call source and Checking
lanes. R293 Name-source injection is not `app_result_pair`'s missing whole-Call
membership or its Checking premise. The global original source quantifier,
Effect hygiene, principality, termination and production admission stay OPEN.

Represented: arbitrary full original source roots/Position scopes in generic
adapters; both App annotations; arbitrary scoped children; retained other code
rows; actual parameter Observe fixture; raw Callee Request/Return token data;
actual native caller bind, cells/env/views, fresh Delay and Name readback.
Not supplied: full HIR-to-original/source-event interpretation, general Rust
simulation, all original callee/receiver alternatives, dictionary-mode concrete
instances, all Reach laws, whole EI interpretation or original source typing.
These omitted proofs do not remove cases from the unchanged parent.

Material source evidence: at actual CalRet `cell[3]=None`, while the final
post-run vector has `cell[3]=Some(Value4/view5)`. The Return projection uses the
captured Return vector exactly; trimming the final vector would be invalid.

## Pinned verification and complete axioms

Installed lookup: `elan which lake` returned
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Actual Lake `5.0.0-src+eb6cafb`, Lean `4.35.0`, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release, x86_64 Linux.
Project pin/manifest inspected; no external packages or changes to dependencies,
toolchain, global defaults, memory limit or shared cache. The sole cache owner
was this leaf, inside copied project `/tmp/yulang-r313-proof/project`.

Final command is retained exactly in `/tmp/yulang-r313-proof/audit-command.txt`:
`python3 .agents/skills/yulang-lean-proofs/scripts/check_lean.py --project
/tmp/yulang-r313-proof/project --lake <absolute-native-Lake> --module
YulangClosure.OriginalSourceCalleeWitnessR313 --timeout 120`, with all 22
`--theorem` arguments. Exit **0**; actual targeted build **36 jobs**, followed
by theorem-kind checks, complete printed types and all transitive axiom lists.
No new warning. Log `/tmp/yulang-r313-proof/final-main-audit-r2.log`, SHA
`5fd2c9f85ac51748a4bbabcd0b7e4bf6edb5a98b4808b732f19f795f6288013b`.
The helper's temporary audit directories were auto-deleted.

All following names have prefix
`YulangClosure.OriginalSourceCalleeWitnessR313.`:

| Theorem | Complete axiom list |
| --- | --- |
| `original_call_occurs` | `[propext, Classical.choice, Quot.sound]` |
| `original_argument_erases` | `[propext, Classical.choice, Quot.sound]` |
| `occurs_trans` | `[]` |
| `both_operand_decodes` | `[propext, Classical.choice, Quot.sound]` |
| `source_enter_saves` | `[propext, Classical.choice, Quot.sound]` |
| `actual_observe_mode` | `[propext]` |
| `observe_has_no_inherited_root` | `[propext, Classical.choice, Quot.sound]` |
| `allocated_observe_mode` | `[propext, Classical.choice, Quot.sound]` |
| `initialized_name_force` | `[propext, Classical.choice, Quot.sound]` |
| `snapshot_initialized_evaluate` | `[propext, Classical.choice, Quot.sound]` |
| `saved_matches_self` | `[propext]` |
| `request_has_no_return` | `[propext]` |
| `wrong_environment_has_no_return` | `[propext]` |
| `actual_callee_witness` | `[propext, Classical.choice, Quot.sound]` |
| `Fixture.native_source_coordinates` | `[]` |
| `Fixture.same_saved_frame_across_request` | `[]` |
| `Fixture.instruction_rows` | `[propext]` |
| `Fixture.exact_delay_operands` | `[propext, Classical.choice, Quot.sound]` |
| `Fixture.environment_extension` | `[]` |
| `Fixture.initialized_caller_snapshot` | `[propext]` |
| `Fixture.name_readback` | `[propext, Classical.choice, Quot.sound]` |
| `Fixture.actual_return_witness` | `[propext, Classical.choice, Quot.sound]` |

`lake env lean -j1 -M1024 /tmp/yulang-r313-proof/ParentApplication.lean`,
wrapped in `timeout 120` and `/usr/bin/time -v`, final exit **0**, elapsed
0.61s, peak RSS 1,034,928 KiB. Log `parent-final.log` SHA
`c1316ac5f465d80af8daae6817f4eeb771fd996b45ef35fdfc9027e116df03fd`.
Both scratch theorem types and axioms were printed; each has exactly
`[propext, Classical.choice, Quot.sound]`. Original R159 parent has the same
list; original R293 app_result_pair has `[propext, Quot.sound]`.

Nine constructor types and axioms were also printed by the pinned direct
check of `AuditConstructors.lean`, exit **0**, peak RSS780788 KiB. Its log
`constructors-final.log` SHA
`c3b06b5e4545478ba369f0815482ee210803725a665486636c449a8b7ac3220e`.
`nativeAdapter` uses `[propext]`; `SourceApply.toApplySource`,
`sourcePreparation`, `sourceNativeRead`, `captureFromSnapshot`,
`Fixture.sourceApply`, `Fixture.preparation`, `Fixture.boundCaller`, and
`calleeWitness` each use `[propext, Classical.choice, Quot.sound]`.
No sorryAx, project axiom, unchecked native-evaluation assumption or kernel
bypass. Source search of both authored files found no proof hole or bypass.

No default/full-root build, root import edit, compiler check or independent
review is claimed by this leaf. The main module is explicitly targeted even
though it is outside the ordinary root import closure.

## Retained failures, resource use and stop

`first-build.log`: wrong repository-root working directory, Lake configuration
not found; corrected to isolated project. `second-build.log`/`third-build.log`:
actual grouped-structure-field/namespace and Option-reduction diagnostics;
fixed against the actual goals. `fifth-build.log` and memory-isolation logs:
importing the full R311/R293 parent cone into the construction module exceeded
the unchanged -M1024 cap. Source/native construction now imports only R312
history; the real parent applications are checked separately in owned scratch.
The larger failed candidate is retained as `full-memory-candidate.lean`, NOT a
proved deliverable. No memory-cap increase or checker bypass.

`ninth-build.log`/`eleventh-build.log`/`twelfth-build.log`: finite vector/arena
Nat-bound and record-projection reduction goals; repaired explicitly.
`parent1.log`/`parent2.log`: section-variable inclusion and R312 wrapper's extra
Request argument; the final proof directly applies R311/R293 consumers without
adding that unnecessary hypothesis. Final main and parent logs are separate
and preserve all failures; error-log elaboration holes are not delivered proofs.

Finite grant2700s. Owned scratch directory birth 2026-11-03 04:50:36 UTC;
final audits complete by05:11:42 UTC. Startup active seconds are UNKNOWN;
this interval is scratch/check work, not a fabricated precise worker total.
Heavy checker ownership was explicitly exchanged with primary/native lane;
all commands have completed, with no background process or descendant lease.
All scratch/generated outputs are under `/tmp/yulang-r313-proof` except the
helper's automatically removed temporary audit directories. Repository writes
were limited to the exact Lean output and this handoff. Shared status, compiler,
expectations, configuration and Git were untouched.

**Writes stopped after this revision-1 handoff.** Next action is fresh independent
review of these frozen bytes, followed by primary adjudication. Any revised
source/native owner/event map is a new bounded packet, not a claimed concrete
instance supplied by this conditional construction.
