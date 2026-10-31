# R3 Lean handoff — scope source join resolved; remaining inputs open

Sprint: `EFFECT-PERMISSION-NATIVE-DECODE/20261029-r3`, contract SHA-256
`c1c2cb6f30f99c08d1b59629bab428d8c7a497c4f72e560815c1bcb158a26e72`;
Amendment 01 SHA-256 `55a371cc9d85cf92466c499b0e6eae4ff8914c03299a00f9562d90e1392495fe`.
Assignment: `/root/effect_permission_native_decode_r3_lean`; handoff revision **1**.
Role: bounded Lean leaf; model/effort not independently observed. No descendants.
Baseline: `d33805eb589ac89925bacab57e362df093456fe0` plus frozen overlays.
Outcome: **incomplete source-to-model construction; remaining native-state/code inputs open**.
No new Lean declaration, theorem, proof source, or scratch file was created.
The only worker write is this handoff. This is an obstruction report, not a
counterexample or proof of impossibility.

## Scope issue resolved by pinned source; construction stays stopped

The initially reported missing raw scope encoding is **resolved by source
inspection**, as directed by Luna, rather than by redacted debug equality.
`crates/yu-hir/src/module.rs:2553` constructs the binding's
`SourceRootId::Definition(binding.definition_root)` and calls `form_ordinary`.
`crates/yu-hir/src/module/local_source.rs:968–979` passes empty root parameters;
lines 1136–1141 initialize the first formal scope to Definition(owner), and
lines 1160–1178 copy that scope into the first parameter. The fixture's `pair`
is the first and only formal. `crates/yu-solver/src/candidate_source.rs:1081–1115` and line 1339
collects nested binding scopes, then chooses the formal scope or
`AnnotationScope::for_source(owner)` as fallback. The source conversion at `candidate_source.rs:1937` named
by Luna and `candidate_effect.rs:43–45` map this Definition owner to the exact
`AnnotationScope::Definition(owner)`. Luna supplied and authenticated the
source-derived join; this leaf read the named source and records it as resolved.
The owner encoding 0 can consequently also encode this one scope identity.
No equality of hidden `DefinitionRootId { .. }` debug text is used.

Read-only source hashes for this correction:
`crates/yu-hir/src/module/local_source.rs` SHA-256
`7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1`;
`crates/yu-solver/src/candidate_source.rs` SHA-256
`96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`.

### Separate remaining input 1 — initial decoder State

`YulangClosure.FormalPermissionSourceOrigin.State` at
`FormalPermissionSourceOrigin.lean:37–45` requires `nextValue`, `nextEffect`,
`nextView`, `values`, `holes`, `effects`, `views`, `viewData`.
The frozen raw block emits none of these initial fields/table snapshots.
`candidate_effect.rs:1880–1923` records ConstructorInput and parameter row,
creates a fresh local `views` HashMap, and calls the negative constructor;
it does not record the native allocator boundary or global memo tables.

The pinned source does derive the allocator rule: native
`crates/yu-solver/src/lib.rs:10487–10517` allocates the current
`effect_bounds.len()` then pushes one row. `candidate_effect.rs:1723–1732`
allocates one row for an omitted port and one for a negative concrete port.
The four source visits and recorded origins 22/24 therefore support the
candidate abstract start counter **21** by the inspected recurrence. This is
a source-derived arithmetic candidate, not an emitted initial State or an
established native-State representation theorem. No allocator-history lemma
or exact source/native simulation was constructed or checked here.

For this all-atomic, omitted/negative-concrete slice, the actual `decodeValue`
branches at `FormalPermissionExportWitness.lean:140–167` and `decodePort` at
lines 82–107 do not inspect the other seven State fields: they preserve those
fields and only increment `nextEffect`. Their concrete native values are
therefore absent but observationally irrelevant to the intended two retained
entries. Arbitrary defaults could give a mathematical decoder witness; they
would not identify the actual native initial State. This leaf did not silently
make that choice. Luna must adjudicate an authorized abstraction/projection
or a source-derived representation argument before any renewed construction.

### Separate remaining input 2 — atomic ValueCode identity mapping

`FormalPermissionExportWitness.lean:115–116` requires `ValueCode.scalar identity`,
and line 141 returns `Shape.atom identity`. The raw source annotation gives
`Int` and `Unit` kinds; `candidate_effect.rs:1624–1627` maps them to distinct
positive/negative collected native leaves. The block emits no map from these
native leaf pairs to `Nat` atom identities. This is a missing source-to-model
encoding definition/correspondence, not proof that no such encoding exists.
`crates/yu-solver/src/lib.rs:2101–2106` looks these leaves up in a collected
`HashMap<Leaf,Term>`; the numeric native Term identities are absent from the
block. `candidate_source.rs:1332–1339` interns primitive leaves and schedules
this FormalAnnotation but does not define the Lean atom abstraction.
A fresh injective mathematical encoding could be defined if authorized;
choosing arbitrary atom witnesses alone would not authenticate native terms.
No encoding, term handles or scalar identities were invented in this leaf.

### Other decoder inputs and exact boundary

Tree shape, row positions/concrete effects, ordered paths, constructor ID,
parameter/occurrence, owner, scope join, origins, representative rows,
materialized nodes and export ports are available from the block plus pinned
source, as itemized below. Source-order lineage 0/1 is the decoder's list index,
not native witness 2/3; that distinction needs a stated correspondence but
requires no missing numeric observation. The decoded dependent `out` is to be
constructed from code/state, not supplied as an unsupported assumption.
The two decoder equations remain unconstructed. No additional absent field
has been established beyond the State/code correspondence issues above.
An actual `ValueDecoded context false s` output depends on both unresolved
choices; neither a supplied dependent output nor assumed decoder equality
would resolve them. `expectedAll` can be evaluated on known retained records,
but its required argument is **that same decoded output**
`out.entries`, not an independently selected matching list. Consequently
standalone matching snapshot/observation tables would not complete the parent
application. This is the precise shared-witness seam that remains open.

Luna directed: freeze this handoff, create no proof file, run no Lean command,
and stop. Owner for the remaining abstraction/encoding decision and any future
construction release: **Luna**. These are open premises, not a counterexample.

## Governing source and unchanged parent

Read root `AGENTS.md`, `AGENTS.pre-sprint.md`, `rules/goal-driven-sprints.md`,
Lean skill and its `references/sources.md` / `references/execution.md`, R3
contract/Amendment 01, current sprint identity, state protocol, actual Lean
source definitions, project configuration and focused native observation code.

Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§1, §3, §5: every supported original source program, every lawful finite
Simple-sub history, actual retained extrusion occurrences and actual polar
parent/copy pairs; preserve original source typing, principal coverage,
soundness, progress, termination, source scopes and one joint witness through
publication/use. Current qualification correction:
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6, using each immutable
Value-birth-level induced graph, retaining all original references.
Accepted effect policy:
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §1 and
§§1.1–1.2: composed variance, exact effect identity, actual local subtraction,
constraint-derived inflow/residual and retained symbolic dependencies.
The whole-language integration drafts `docs/yulang-whole-proof-closure-ja.md`
and `docs/yulang-semantics-and-soundness-ja.md` were consulted as maps only.
No draft adds semantic authority or discharges the native bridge.

## Existing parent-facing declaration and precise application gap

Actual source declaration, **not freshly printed or audited in this assignment**:

```lean
YulangClosure.FormalPermissionAuthenticatedSiteExport.extracted_port_and_export
  (context : Context) (tree : Annotation)
  (path : List Step) (row : Option SourceRow)
  (sourceVisit : SourceTreeVisit tree path row) (port : PortPath path)
  (s : State) (code : ValueCode) (out : ValueDecoded context false s)
  (snapshot : CaptureSnapshot) (observations : List Observation)
  (decoded : decodeValue context false s code = some out)
  (allEntries : expectedAll context snapshot 0 out.entries = some observations) :
  EffectVisit tree path row ∧
    decodeObserved context s code snapshot observations = some out
```

Namespaces opened by that module:
`YulangClosure.FormalPermissionSourceOrigin`,
`YulangClosure.FormalPermissionCaptureConstruction`,
`YulangClosure.FormalPermissionExportWitness`, and
`YulangClosure.FormalPermissionSiteTraversal`.
Exact declaration location: `FormalPermissionAuthenticatedSiteExport.lean:130`.
No instance was applied: scope is resolved by the source join above;
native-to-code/initial-state correspondence remains before constructing
`decoded` and `allEntries`.
No new theorem names/types, hypotheses or axiom results exist. Every original
parent, source/native authenticity, effect-hygiene, consumer-residual,
unequal-transport and production gate remains **OPEN**.

## Frozen raw fields and intended mapping (no constructed instance)

Evidence JSON revision 4, SHA-256 `0d1666fabccd93387c294f04b15374edab7d55cba5a83b67f6cafa7a0af8f222`.
The assignment called it rev3; its actual `revision` is 4 and its SHA
matches the assigned frozen hash. Observation: stderr bytes `[16321,46045)`,
29,724 bytes, SHA-256
`8dc5d61aee002d858cce116fc23cb85afd297395bf181ef35488aea2cb12e556`.
Byte extraction equals the JSON exact text; all four raw-file hashes rechecked.

- `source_text`, same-HIR `source_annotation`, constructor **1**, borrowed
  `annotation_identity=130671427278464`, and `ConstructorInput` remain external
  observation facts; the decoder has no field proving their authenticity.
- `owner_encoding=[(0,Definition(...))]` and `owner_export_owner=0` supply owner
  coordinate **0**. Parameter **0**, occurrence ordinal **4** come from
  `ConstructorInput` / encoded origins. Scope is encoded via the resolved source-derived owner join above.
- Source position **0** is enclosing annotation; **1** is root `[]`; **2** is
  `[Element(0),Result]`; **3** is `[Element(1),Element(1),Result]`.
- Effect identity table maps **0** to root `audit`, **1** to first-result `io`,
  **2** to nested-result `state`, with exact source-root `tuple-formal/source.yu`
  identities retained by the native table. All three variables lists are empty.
  The identical redacted debug representations alone do not prove identity;
  native table extraction/correspondence remains review evidence.
- Full source tree has **nine** nodes: explicit root row `(1,[0],[])`; the two
  explicit result rows `(2,[1],[])`, `(3,[2],[])`; six omitted rows retained.
  Ordered outer tuple children are function then `(int,function)`.
  Function arguments are `int`, results `unit`.
- Constructor visits are exactly first argument (omitted, positive, order 0),
  first result (position 2, negative, order 1), nested argument (omitted,
  positive, order 2), nested result (position 3, negative, order 3).
  Root and bare tuple coordinates are source nodes, not Function Effect ports.
- Encoded origin tuple fields are witness, constructor, occurrence ordinal,
  parameter, enclosing annotation position, path, source-row position,
  allocated row, concrete IDs. The fifth coordinate **0** is annotation
  position, not owner; exact owner is retained by the source filter.
  Origins have witness **2**, allocated row **22**, first result path, `[1]`;
  witness **3**, allocated row **24**, nested result path, `[2]`.
  `expectedAll`'s lineage 0/1 would be source-order list indices, not witnesses 2/3.
- `ParameterRow` reports `Some(1)`, owner Definition, parameter 0, base **23**,
  row **23**. This is distinct from source Origin rows 22/24 and does not
  authenticate an initial decoder state.
- Capture **4**, root **0**, live root **0**, node count **41** are observed.
  CanonicalIntern for witness 2 has original/canonical row **22/22**, negative
  node **17**, independently retained CapturedEffectRowNode **17**. Witness 3
  has **24/24**, negative node **14**, materialized row-node **14**.
- Exact-owner export tuples start with occurrence ordinal **4**, not capture
  number; capture **4** is separately supplied by CaptureOwner/CanonicalIntern.
  Export entries retain source positions 2/3, paths,
  concrete IDs [1]/[2], ports **17/14**, Negative, `Some(Effect)`.
  These could supply snapshot/Observation coordinates only after the missing
  constructor-code/state correspondence is resolved.

Represented by the raw observation: nine-node source inventory, four visits,
two concrete retained origins, identity row transport, owner-matched export.
Omitted from any claim: a Lean instance (none created), all other source
programs, symbolic/delegated code histories outside this block, changed-row
transport `r != q`, consumer residual, handler subtraction, full capture
simulation and universal native authenticity. The focused Cargo test also
calls a symbolic/delegation observation, but its success is not a second raw
concrete instance for this blocked construction.

## Audit inputs and execution status

The twelve source/config inputs below were each rehashed and compared byte for
byte with the isolated copy; all matched their frozen hashes. Scratch manifest
SHA-256: `9487eddc8415cb431c8176e2464d2a7fe8fed9b919a339f0757f5e3acb77371e`.
Scratch project: `/tmp/yulang-effect-permission-native-decode-20261029-r3/lean-project/`.
No shared `.lake` access or generated-output write occurred.

- `notes/theory/lean/README.md` → `README.md`; 53784 bytes; SHA-256 `8d27e0b90fc04eb8a0a30606a857e564e5269e8e33e72fddbf1190cb6a7072e3`.
- `notes/theory/lean/YulangClosure/FormalPermissionAuthenticatedSiteExport.lean` → `YulangClosure/FormalPermissionAuthenticatedSiteExport.lean`; 7065 bytes; SHA-256 `d6fc3e11f26350f6cf03d7afc248500778e3bf4a8ee816582630aa5f5feeeb84`.
- `notes/theory/lean/YulangClosure/FormalPermissionCaptureConstruction.lean` → `YulangClosure/FormalPermissionCaptureConstruction.lean`; 15118 bytes; SHA-256 `181d5075e2fa3ed5f4adfe4029b368461638b6ac6f62341ec165e6e3980ee13c`.
- `notes/theory/lean/YulangClosure/FormalPermissionConstructorRealization.lean` → `YulangClosure/FormalPermissionConstructorRealization.lean`; 14959 bytes; SHA-256 `70a89e7ea4589951e5f5e9323b4b2b415003c5868dc3f53ce16129fa67eafdd9`.
- `notes/theory/lean/YulangClosure/FormalPermissionExportWitness.lean` → `YulangClosure/FormalPermissionExportWitness.lean`; 15149 bytes; SHA-256 `7c01a80c8d8e868d9349a3d02ec2d465ca976edfb515e04b57161b5c9744a67f`.
- `notes/theory/lean/YulangClosure/FormalPermissionExportWitnessNative.lean` → `YulangClosure/FormalPermissionExportWitnessNative.lean`; 6719 bytes; SHA-256 `a5ccf179ef6e5396adb46c18ced108052cba4022119efd0daa0d026b4c368de1`.
- `notes/theory/lean/YulangClosure/FormalPermissionLiveCapture.lean` → `YulangClosure/FormalPermissionLiveCapture.lean`; 19049 bytes; SHA-256 `0e1bd4f2ae95e798561e014595e66ec9b6d9b342dbd2b15d0d5c9d346838c53e`.
- `notes/theory/lean/YulangClosure/FormalPermissionSiteTraversal.lean` → `YulangClosure/FormalPermissionSiteTraversal.lean`; 8761 bytes; SHA-256 `ac079ecc4c480adb4222723815b3f476469ed13b933c3994d090db0fae909207`.
- `notes/theory/lean/YulangClosure/FormalPermissionSourceOrigin.lean` → `YulangClosure/FormalPermissionSourceOrigin.lean`; 17918 bytes; SHA-256 `db37f9d83e450a450d689b9eed46311108e635eb846d268b7a3a567dcee624fd`.
- `notes/theory/lean/lake-manifest.json` → `lake-manifest.json`; 145 bytes; SHA-256 `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.
- `notes/theory/lean/lakefile.toml` → `lakefile.toml`; 311 bytes; SHA-256 `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`.
- `notes/theory/lean/lean-toolchain` → `lean-toolchain`; 25 bytes; SHA-256 `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`.

Checker source was read, not executed:
`.agents/skills/yulang-lean-proofs/scripts/check_lean.py`, pinned SHA-256
`a4f10b70297cbf4d8b5bc0c7526bc29783eaf417f1f70e53eeea341d1150dde6`.
Proposed eventual command shape only (not executable until theorem list and
bytes exist and Luna releases the separate audit):

```text
python3 .agents/skills/yulang-lean-proofs/scripts/check_lean.py
  --project /tmp/yulang-effect-permission-native-decode-20261029-r3/lean-project
  --lake /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake
  --module YulangClosure.FormalPermissionAuthenticatedNativeDecode
  --theorem <every actual new theorem, separately repeated>
  --timeout 90
```

No concrete theorem list or exact audit command is proposed for this stopped
artifact. The checker runs version/build/audit subprocesses; the sprint's
single audit means one released helper invocation with all its subprocesses
included, not an extra direct Lean probe. Its temporary audit directory is
outside the presently named scratch root by default; Luna must account for
that generated-output path before any future release.

Pin: `leanprover/lean4:v4.35.0`; manifest has no external packages. The primary
preflight reports Lake 5.0.0-src+eb6cafb / Lean 4.35.0 commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. This leaf ran **no Lean/Lake/version,
checker, build, formatter, Cargo or installation command**. Therefore fresh
actual versions, kernel acceptance and transitive axiom lists are **NOT RUN**.
No `sorry`, project axiom, reduced language, stronger hypothesis or bypass was
introduced. No independent review was performed.

Actual tools: read-only `pwd`, `cat`, `sed`, `rg`, Python JSON/byte/hash inspection;
all relevant reads/hash checks exited 0 except the initial attempted read of
nonexistent `notes/theory/lean/lakefile.lean` (exit 1). The actual TOML project
configuration was subsequently read. No Lean diagnostics or proof goals exist.

Resource bound: 400 seconds total assignment, including any later audit; stopped
at 2026-10-29T11:18:53.334608+00:00, 340.3 seconds since recorded construction release
(an upper bound on active work, including dispatch gap). No heavy process or
peak-RSS measurement was run. The 90-second audit allowance is unspent and
**not released**; the remaining assignment envelope is at most 59.7
seconds under this conservative elapsed-time accounting. No background
processes or generated files remain from this leaf. Writes are **STOPPED**
with this frozen revision; primary owns any follow-up and records.
