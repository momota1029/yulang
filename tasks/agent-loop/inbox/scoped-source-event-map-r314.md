# R314 source proof handoff — revision 1

Assignment: `R314-SOURCE-PROOF`; worker `/root/r314_source_proof`; leaf, no descendants.
Baseline `b7c1dd2e1`; contract `tasks/agent-loop/sprints/scoped-source-event-map-r314.md`,
SHA-256 `5938b2e97ff033cc3936f79a9fecedf984ede0be6e3f4a4b5ceb296bd559afe7`.
Requested/effective model, effort and actual session identifier: UNKNOWN.
Outcome: **REDUCED / conditional finite source correspondence**. Kernel acceptance
is recorded below; independent review and production authority are not claimed.

## Authority and unchanged parent

Read adopted `notes/design/2026-10-08-source-generalize-definition.md` §2 and
its selected construction `notes/theory/2026-10-08-source-generalize-definition-and-proof.md`
§§3.1, 3.3, 4, 5.2; `notes/design/2026-10-24-computed-call-result-constructor.md`
§§3.1–3.4 and §4. Read the source manuscript `docs/yulang-source-type-safety-ja.tex`
opening corrections, `sec:source`, `sec:all-source`; its research status is not
semantic authority. Read the inference top-level principles and the actual
original reification schema, R313/R312 definitions and R159 parent.

The unchanged parent is `YulangClosure.SourceAppAdmissionR159.app_admission_iff`:
for arbitrary sorts, inputs/readout/admissions, original kernel, environment,
Context, Mark and BOTH original source children, source App judgment requires
annotation locals and one admitted ViewLogic candidate extension with every
original App local and both source judgments in that SAME extension. No
candidate, q_c, Checking, source typing, original Return membership, independent
arm evidence or shared semantic witness is manufactured here.

Before: R313 `Fixture.sourceApply` accepted arbitrary original root/callee/map
and a caller-provided occurrence proof, even with a callee Apply instruction.
After: `OriginalScopedSourceEventMapR314.Fixture.sourceApply` constructs the
actual R313 `SourceApply` from the typed native source payload, including the
whole lambda root, nested computed callee, both operand rows and full allocated
scope. Its only external structural inputs are one Declaration coordinate,
original external Context, and untouched other program rows. These are not
claimed to establish their original source meanings.

## Frozen inputs and exact changes

Changed only:

- `notes/theory/lean/YulangClosure/OriginalScopedSourceEventMapR314.lean`, SHA-256
  `a175912fd51214ba68b1ff4c37252bf639d0fce82b106edd1c6f43b691babc83`.
- This assigned handoff path. No root import, compiler, shared task/status/index,
  configuration, dependency, toolchain, Git or other worker writes.

Native R4 input: `/tmp/yulang-r314-native/source-event-map-r4.lean`, SHA-256
`b320d208d5fa2a2b84b29e74652e5529f0e78f35453e626733770b768a74df25`;
producer handoff SHA-256
`ba64d077ce023c379ac46b1efea6f80b0056f7e93aeb272860eaecb642580230`.
R313 witness/application hashes:
`46494caab63654ad86bc16e0922d817ea1a77076e4f1d008485b049e916d197b` /
`9d0216f25c302e6242653a22fd5c23b3f62bbe810cde27ca1700543b55ddedd5`.
Original owner schema hash:
`95d9749ce93ecfc82d6423ba193a261f2725178a7e62cea469b57ae316af3d7e`.

Deterministic extraction script: `/tmp/yulang-r314-proof/embed_source.py`, SHA-256
`a83c12d9a0dd4c00cdfcc0de1d1a3a2fdbfccea2210b121da04aa47e931ae8f7`.
Invocation: `python3 /tmp/yulang-r314-proof/embed_source.py /tmp/yulang-r314-native/source-event-map-r4.lean`.
It retains exact source declarations in original order, including mutual blocks;
only generated Repr/DecidableEq deriving and the original import are removed.
The output body is embedded between BEGIN/END markers in the changed module.
Subset SHA-256: `1dfd08ba580ad0d7dfdc5123d1452e0d59eef6dcb0677e19400defbe02c8f98b`.
The manifest `/tmp/yulang-r314-proof/subset-manifest.json` identifies every
retained/omitted declaration. Retained names:

`Position, ScopeTag, RootBinding, Resolution, EffectId, EffectRow, SourceType, AnnotationType, Annotation, Formal, SourceForm, Instruction, SourceNode, sourceText, rootBinding, rootInitializer, rootFormals, nodes, runId`.

Runtime snapshot/events/value/dispatch declarations are omitted, not silently
represented by simplified data. The complete native file remains the input
artifact. `data_normalized` proves equality of the pure typed adapter with its
compact normal form; the normal form is not an assumed second source map.
Full DefId name/realm/path/ordinal participates in interning. Parameter names
and module names use disjoint finite intern coordinates. Native occurrence
ordinals are not asserted equal to pre-existing semantic Site identities.

## Checked surface and application

Main namespace: `YulangClosure.OriginalScopedSourceEventMapR314`.
`Fixture.root_decodes`, `selected_decodes`, `callee_decodes`, `argument_decodes`
compute the entire source root `lambda value => (make 1) value` and its actual
children. `anchor_computed` and `selected_occurs` use the original allocator;
they preserve the full external Context plus the actual Value formal. The
seven enclosing telescope entries are Description, lambda ViewLogic,
Invocation, Receipt, Return/rebind, Shared, body EventProof. The App's own
ViewLogic remains inside this position; none is replaced with an empty scope.

`Fixture.sourceApply` joins labels 8/9/10 to the actual Apply/Apply/Observe-Name
rows; the inner Apply joins 11/12. Other module code is retained through
`otherCode`; whole-program equality is never imposed on a truncated arena.
`Fixture.decoded_source_enters` applies the constructed record to R312
`enter`/saved-Callee, with original-root occurrence intact.
`Fixture.decoded_observe_delay` applies R313 `observe_has_no_inherited_root`,
deriving the ordinary unknown Delay metadata from the actual Observe instruction.
Both preserve the explicit `raw.program = (arena origin data otherCode).program`
premise; this is not a native Raw/event correspondence proof.

Rejection theorems cover replacing the computed callee with Name while retaining
Apply, swapping operand labels, wrong lexical scope/binding, conflated source
occurrences and a mismatched Export run identifier. The run test checks that
explicit identifier guard; it is not authentication of arbitrary Raw events.
Completeness checks require every source row to occur once in the root traversal.
The native producer owns actual parse/HIR/Machine authentication and snapshot
negative tests; this leaf did not rerun Rust or prove those mechanisms.

The schema/adapter retains Group and Ascription data. The checked positive
instance contains Lambda, two Apps, two Names and an integer; no positive
Group/ascription theorem or annotated-formal source meaning is claimed.
Unsupported forms, annotated formals and unsupported scope/resolution variants
fail closed in this finite adapter. The original 13/11/3 language and all
original independent arm quantifiers remain unchanged and unproved globally.

Separately checked `/tmp/yulang-r314-proof/R297Bridge.lean` states
`R314R297Bridge.selected_row`: actual R297 `sourceInventory` row 12 maps to the
same selected allocated subtree for every origin/external Context. Its six
canonical definitions are byte-identical extracted blocks from the final module;
`make_r297_bridge.py` and `r297-bridge-manifest.json` record the extraction.
Bridge SHA-256 `edf2fc3305abb4760ef8fd7c31e7de80473be6eb6c702be5fcb9284bdd5c166e`.
This is separate scratch evidence; a combined import/application to the tracked
module was not checked under the memory cap and is not claimed.

## Actual checker evidence

Installed native Lake resolved by `elan which lake`; no installation/default
change. Lake `5.0.0-src+eb6cafb`, Lean `4.35.0`, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
One isolated cache owner: `/tmp/yulang-r314-proof/project/.lake`.

`python3 .agents/skills/yulang-lean-proofs/scripts/check_lean.py --project /tmp/yulang-r314-proof/project --lake /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --module YulangClosure.OriginalScopedSourceEventMapR314 --timeout 120`
with all 18 repeated `--theorem` names in `theorems.txt`: **exit 0**. Exact argv:
`/tmp/yulang-r314-proof/check-command.txt`; complete printed types/axioms and
ordered whitelist receipts: `/tmp/yulang-r314-proof/check-r4.log`, SHA-256
`543747734821ccd5ea21e9d0b725477c1a48b55ec08a6be99ec4b013a3f45a81`.
The helper built the actual module/dependencies and used `lean -j1 -M1024`.
It did not run the default project target or edit the root import.

All theorem types are printed in that complete log. Complete axiom lists below
(use the namespace above; all except `follow_occurs` are in `Fixture`):

- `follow_occurs`: `propext`.
- `data_normalized`: `propext`.
- `root_decodes`: `propext, Classical.choice, Quot.sound`.
- `selected_decodes`: `propext, Classical.choice, Quot.sound`.
- `callee_decodes`: `propext, Classical.choice, Quot.sound`.
- `argument_decodes`: `propext, Classical.choice, Quot.sound`.
- `anchor_computed`: `propext, Classical.choice, Quot.sound`.
- `selected_occurs`: `propext, Classical.choice, Quot.sound`.
- `decoded_source_enters`: `propext, Classical.choice, Quot.sound`.
- `decoded_observe_delay`: `propext, Classical.choice, Quot.sound`.
- `data_valid`: `propext, Classical.choice, Quot.sound`.
- `callee_name_substitution_rejected`: `propext, Classical.choice, Quot.sound`.
- `swapped_labels_rejected`: `propext, Classical.choice, Quot.sound`.
- `wrong_scope_rejected`: `propext, Classical.choice, Quot.sound`.
- `wrong_binding_rejected`: `propext, Classical.choice, Quot.sound`.
- `conflated_occurrence_rejected`: `propext, Classical.choice, Quot.sound`.
- `different_run_rejected`: `propext, Classical.choice, Quot.sound`.
- `complete_telescope`: `none`.

`Fixture.sourceApply` (a construction, not a theorem) has its full printed type
and axioms `[propext, Classical.choice, Quot.sound]` in `construction-audit.log`;
manual audit command `lake env lean -j1 -M1024 /tmp/yulang-r314-proof/ConstructionAudit.lean`
ended exit 0. `lake env lean -j1 -M1024 /tmp/yulang-r314-proof/R297Bridge.lean`
ended exit 0; full type/axioms in `r297-check.log`, axioms
`[propext, Classical.choice, Quot.sound]`. No project axioms, sorry/admit,
unchecked native evaluation or kernel-check bypass was added. A source search
of the changed file found none (rg exit 1 = no matches).

Material failures preserved: early String.toInt? reduction did not establish
its value by rfl; a small checked decimal parser replaced it. R297+R313 imports
alone used 1,014,176 KB; combined normalization repeatedly exceeded -M1024.
R297 is therefore checked separately, while the main proof uses the identical
original allocator and a smaller import closure. Early R2 repeated-normalization
validator audits also hit the cap; they were repaired via the checked compact
normal-form equality. No cap/toolchain/manifest change was made. R1/R2 were
never delivered as source-native proof. R3 logs remain in scratch; R4 is final.
R3 measured module build: 2.64s, peak 1,047,360 KB, exit 0. Total exact lane CPU/
wall accounting unavailable; bounded 2700s envelope retained, no ongoing process.

## Open parent edge / precise next owner

**First remaining premise:** original module-binding/DefId and declaration
provenance must denote the genuine original external Context (including its
published binding meaning) and source coordinate interpretation. Owner: primary's
source/environment correspondence lane. This artifact supplies no source typing
or original `OriginalCoordinates` instance merely by allocating finite interns.

Then the actual same-run native program/Raw and event readout, complete snapshot
and environment lookup interpretation, original same-Return callee membership,
checked Function transport and actual-provider relation remain open. All-Reach
world/license/prefix evidence, independent whole-Call arms, q_c/Checking and
R159 admission in one shared extension remain open at their existing owners.
R4's raw snapshot identity fields are not a concrete original event interpretation
and are not consumed by this source-only proof. Do not infer original Call Union
membership, A/B closure, native success soundness or production promotion.

Next useful packet: establish the original module-binding/Context interpretation
and then same-run Raw/event equations on the frozen native payload; apply those
at the existing R313/R311 consumer with every remaining leaf explicit. No
whole-language or semantic expansion is authorized by this handoff.

All scratch writes are confined to `/tmp/yulang-r314-proof` (isolated project,
logs, extraction/bridge scripts, manifests, audit files). All repository writes
are confined to the two exact leased paths above. No descendants or shared-cache
writers exist in this lane. **Writes stopped; no checker/process remains active.**
Independent review, acceptance, integration and Git belong to the primary.
