# R304 source effect retention — frozen handoff revision 1

Assignment: `source-effect-retention-r304`, worker `/root/effect_trace_proof`.
Parent packet: direct NEW_TASK from `/root`; baseline supplied as `72d77856b`.
No new file-backed sprint contract/hash was supplied. The current snapshot still
names R286; it was read but not used to invent current dispatch authority.
Author: `/root/effect_trace_proof`; no descendants/coauthors. Requested and
observed model/effort: UNKNOWN in this worker's received runtime metadata.
Outcome: checked **local native construction**, with source-correspondence and
R293/R302/R159 application **BLOCKED**, not closed or reduced by this packet.
Fresh independent review is NOT_RUN. No production authority.

## Actual result and parent application

`SourceEffectRetentionR304.lean` imports only the existing
`NativeContextTables`. It computes operation-view copies using the existing
`copyInput`, `Store.constructView`, `Step.reserveCopy`, and `Run`. It assumes
no desired output record, packet map, or copy-success equation.

For arbitrary original `ViewInput input` with `input.operation = some origin`,
the first published cell's copy input is derived. The result retains ordered
`allowed`, source `owner`, source `position`, and **all** `OperationOrigin`
fields (`declaration`, `occurrence`, `retainedBytes`); it takes the independently
specified new tail and has no annotation source/closed weight. The proof is
applied to the actual existing `construct_copy_run` consumer. Successful
intervening `Run` events preserve the same source cell and birth. A constructed
two-copy run yields the exact final payload. The two tail inputs remain
independent; equality of distinct FreshUse rows is not claimed.

Six checked declarations (complete types and axioms below):

- `operation_copy_input`: derives successful copy input from actual publication.
- `operation_copy_input_after_run`: derives it after arbitrary intervening native Run.
- `operation_copy_run_after_run`: applies that equation to existing reserveCopy/Run.
- `operation_copy_readback`: derives the exact constructed output cell.
- `operation_copy_run`: immediate successful native-copy construction.
- `operation_two_copy_run`: composes the two constructed copies and final readback.

This discharges the **local native operation-copy field calculation**. It is
not an authenticated execution of the nested Rust fixture. The original
operation trace is not serialized into `NativeContextTables.Store` or
`ViewInput`; the selected signed extrusion tail and each retained FreshUse tail
are not supplied by an authenticated Lean input. The general theorem therefore
has not been instantiated to the actual fixture.

The exact R302 consumer `app_source_packet_and_target` still requires original
`Checking` at the same `ViewLogic` extension and
`Meaning inputs (.trace (raw.atInterface ((state.logical data).interfaces
  ⟨mark.site, .callableImage⟩)))`.
`OriginalSourceChecking.clause` requires event coherence, observation guards,
world membership, the actual returned-value field when present, and all original
`observationFields`. Effect-family/owner/tail metadata supplies none of those
complete semantic certificates. R293's GR1 source/EvalInvoke registration,
original independent arms and licenses remain separate. R159's
`app_admission_iff` retains independent logical admission, annotation premises,
all App local premises, and both arbitrary operand derivations at the exact
extension. None is weakened or claimed proved here.

## Source evidence and precise remaining equations

The source review uses the frozen byte hashes below, not the old review's
`ba9016...` hash. No Git operation was used to assert equality to the supplied
baseline. Existing review evidence was reused only for its stated finite
Function/path/polarity/row-incidence scope; no Rust test was rerun here.

- `candidate_effect.rs::candidate_signature_value` recursively constructs all
  four Function ports. Only pointer equality with `declaration.signature`
  passes Self to the result-effect constructor. Nested functions get no Self.
- `candidate_signature_effect` handles absent defaults, rejects concrete
  negative-variance rows and multiple symbolic variables, shares variable rows,
  and caches views by actual `SourceEffectRow.position`. A positive-variance
  view's list is optional Self followed by original concrete entries in order.
  A cache hit reuses the stored view; a proof must retain that actual cache
  history rather than re-infer contents from a Function shape.
- `candidate_signature_view` stores owner/position/allowed/tail/operation origin.
  An operation view gets neither source_weight nor closed_weight.
- `candidate_copy_effect_view` clones owner, position, ordered allowed, and
  operation origin, then calls `candidate_signature_view` with the supplied
  tail. `candidate_remapped_effect_view` memoizes `(old_view_id, new_tail)`.
  The existing Lean constructor models this **cache-miss** path. A cache hit
  needs its original memo insertion/readback; no such hit invariant is claimed.
- `candidate_extrude`, `Work::EffectView`, uses the resolved child copy under
  the full signed `Key(endpoint, polarity, target)`, and preserves Support vs
  Allowance vs AnnotationMember (including member index). No-tail views are
  reused directly. Its temporary view-remap events are not in operation_trace.
- `Capture::expand` records an EffectOperand with its actual tail node;
  `Capture::intern` canonicalizes its endpoint. `Capture::expand_row` records
  local bounds; older nonlocal rows remain shared anchors. The effect payload
  can be below a Function port's row bound, not its direct Function child.
- `prepare_candidate_fresh_use` computes the tail via that captured tail node,
  its graph row index, and the same route's `rows` vector, then remaps the view.
  `RetainedFreshUseMaps.effect_operands` retains the resulting operand. Source
  View.owner, receiving BoundKey owner row, and FreshUse image row are distinct
  identities and must not be equated.

Minimal next evidence request, **R304-NATIVE-INPUT-1**, owned by Luna's source
lane, without authority to implement from this handoff: authenticate the actual
source view and its cache-miss/cached remapping edges, with these equations:

1. The view is reached from the exact slot-42 retained rewritten Function's
   effect-port row through the retained bound, preserving the complete
   `BoundKey(owner, side, endpoint)`, not found by an allowed-family search.
2. Its original fields equal the constructor's actual owner/position/ordered
   allowed/origin. For an extrusion copy, its tail is the row returned for the
   exact signed child Key. Polarity/target may split an originally shared tail;
   raw row equality across signs is not a sound substitute.
3. For each exact use route, `graph.nodes[tail_node] = Node::Row { row: k, ... }`,
   `route.rows[k] = RowKey::Effect(t)`, and the retained EffectOperand's view
   reads back `tail = Some(t)` with the same ordered payload and provenance.
   The no-tail case reads `None`; the operation weights both read `None`.
4. The source's identity encoding into the existing Nat-indexed native tables
   preserves distinct SourceEffectId, SourceRootId, SourceNodeKey, declaration,
   occurrence, allocation, and signed-copy identities. A bare id list without
   those readback equations cannot instantiate the theorem.

Exact falsifier: a retained operand reached by this exact bound/use route with
changed ordered allowed/origin/owner/position, or a tail different from its own
captured tail-node/row-map image, defeats the proposed instance. A shape match,
matching family set, or the other use's row is insufficient. These are missing
readback equations, not a newly designed certificate framework.

A separate bridge remains at
`OriginalExtrusionWork.perform (.effectView ...)`: the existing relation yields
`External.effectView`; it does not execute the NativeContextTables copy and
resume the Work machine. No source-tail semantic equivalence or complete
source checking law follows from the local field calculation. Owner: existing
extrusion/source-to-native proof lane, assigned by Luna.

## Checks, resources, and reuse

Pinned native executable:
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Observed Lake `5.0.0-src+eb6cafb`, Lean `4.35.0`, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. No package additions or pin changes.

`check_lean.py --project /tmp/yulang-source-effect-r304 --lake <above>
--module YulangClosure.SourceEffectRetentionR304` with all six `--theorem`
arguments passed (exit 0), including selected-module build and complete printed
axiom audit. Each theorem uses exactly `[propext, Quot.sound]`. The final build
covered the imported dependency cone. All 12 source hashes equal the checked
isolated project. No default whole-library build or whole-language claim.

Two checker runs: first four declarations, timeout bound 180 seconds; final
six declarations, timeout bound 120 seconds; both completed. Source search found
only actual native functions/constructors named `admit`, no proof holes or
checker bypass. One setup command initially used a relative copy path under the
Lean working directory and failed before copying; absolute-path copy succeeded.
No mathematical repair/failure occurred. No Cargo, Rust execution, Git, compiler
edit, shared-cache write, external dependency or nested CLI.

Prior work reused: NativeContextTables constructor/readback/run extension;
R293/R302's exact packet consumer; the retained rewrite/capture review's limited
finite result. Rejected: using Function shape, row incidence, or classical
packet reification as full trace membership. No new assumed target relation.

Budget: <=1200 seconds, three substantive stages (source audit, existing-native
construction/check, frozen handoff). Exact aggregate active seconds UNKNOWN;
charge the full 1200-second reservation if needed. All check processes completed.
Next in-scope action at producer stop: none; primary requested immediate freeze.
Mutual TODO: Luna may admit R304-NATIVE-INPUT-1; source/proof lanes supply the
missing readbacks before a source instance or semantic parent application.

## Paths, freeze and writer cessation

Only repository writes:
`notes/theory/lean/YulangClosure/SourceEffectRetentionR304.lean` and this inbox.
Explicitly granted scratch/cache: `/tmp/yulang-source-effect-r304/**`, containing
an isolated copied Lean project, `.lake` generated outputs, `check.log`,
`check-final.log`, `dependency-hashes.json`, `source-hashes.json`, and exact
`source-snapshot/` copies. No other new/scratch paths.
All descendant leases: none. Worker state: **STOPPED WRITING** upon this frozen
revision; no running verification process and no background work. Candidate
ready for primary intake and independent review; not independently certified.

## Frozen hashes

Artifact SHA-256: `b2f070b78c9b347db6cb3710e542a1d03db596a4a64af3915985f2bc41ff0706`.

- `/tmp/yulang-source-effect-r304/check.log`: `89319c630967b19b5049cbdde842a16851519c05690a2f0f967fe6ef7fd66f76`.
- `/tmp/yulang-source-effect-r304/check-final.log`: `75f0638a3d7eb7f68fdfbf5a67f0af1b7eab91e41d7dda39a9f94e1dc4439951`.
- `/tmp/yulang-source-effect-r304/dependency-hashes.json`: `db606db91788f84464a85e191ec53105061b049ae5de3108b6c3a6f6c0d4d871`.
- `/tmp/yulang-source-effect-r304/source-hashes.json`: `d424ad70da0a0124fce51fa0601b91e6c3fb24baf4de12580e193f6993303b74`.

All direct/transitive Lean source dependencies:

```json
{
  "notes/theory/lean/YulangClosure/SourceEffectRetentionR304.lean": "b2f070b78c9b347db6cb3710e542a1d03db596a4a64af3915985f2bc41ff0706",
  "notes/theory/lean/YulangClosure/NativeContextTables.lean": "eaf2b037af40af01ad116e1ae413a6c7d5a0023d49c8b9f1b92d29c319d2df81",
  "notes/theory/lean/YulangClosure/NativeContextExpansion.lean": "9887bef34e51678cead77eaf84a2f9b47916987ea9cffaad5d4ef74d53de2ea8",
  "notes/theory/lean/YulangClosure/NativeReplayCurrent.lean": "fdd7dfa32f944f09b2cfc7440caeff95edcfad1fd5c839094f186d27168d9088",
  "notes/theory/lean/YulangClosure/NativeMergeExpansion.lean": "f14bd35e8f7a6b9f326dadf003797c63f4a48fd0d0c0c9d68891c579560baf6e",
  "notes/theory/lean/YulangClosure/NativeReplayCoverage.lean": "e65d925ab5222fd6bbc4bf63e756701aaba1273fff677ceb052d7f66e6450b7e",
  "notes/theory/lean/YulangClosure/NativeExecutionHistory.lean": "44ad2a6d5b9ac0526ea36adc9180e0ed66e3892e48fa39aa40b20999dc7a1da6",
  "notes/theory/lean/YulangClosure/NativeValuePorts.lean": "f49bf12537633c65b4dbdcb4e739df5de5eee76cfb5ad845c8dba50cef4101fa",
  "notes/theory/lean/YulangClosure/NativeRecordPlan.lean": "3cf43fdb754748b83a6816791d640752dda491b87f7e2513a27548a950b27d43",
  "notes/theory/lean/YulangClosure/RecordBoundaryPreservation.lean": "1bde9224c1b0d568d5cc73d84a5ccc5f1157452c87ea2ff428096c1dbd50d056",
  "notes/theory/lean/YulangClosure/NativeContextReadback.lean": "321d087c8d2df5099f67beb75e4316d44114806bbfae2aa64ebda22a34bd83f2",
  "notes/theory/lean/YulangClosure/NativeDrainOwnership.lean": "d37edac29dcecc19dd90b91c3095e5385a0657310dcf08d805a8f20672872d18"
}
```

Source/parent input hashes:

```json
{
  "crates/yu-solver/src/candidate_effect.rs": "4df60eacd1ef332fa20c92db6495559073cf42de9e17a048798144813e640a56",
  "crates/yu-solver/src/candidate_extrusion.rs": "80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61",
  "crates/yu-solver/src/candidate_scheme.rs": "6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e",
  "crates/yu-solver/src/lib.rs": "429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be",
  "notes/theory/lean/YulangClosure/OriginalExtrusionWork.lean": "c419675d75a2cdf03fe5b1ba8d2eef106fea0c4f5187f9f5c06999fa734edd58",
  "notes/theory/lean/YulangClosure/NativeFreshUseValidation.lean": "951317b3617b0a399c1192291819f4dc61b4561ab80065e24c40a5c1e32a19a6",
  "notes/theory/lean/YulangClosure/ComputedCallUnionRealizationR293.lean": "50b1ce82dbd81d8c17a99461a78b77a9066094896f38e046d70fb4dd69365543",
  "notes/theory/lean/YulangClosure/SourceSignatureNativeBridgeR302.lean": "090b09fd04fac56b99b4e637786948fae750150c1e9afc38a532cf290c6f0b30",
  "notes/theory/lean/YulangClosure/SourceAppAdmissionR159.lean": "5e948a1f8a3aab66028f885ebf16b6ffeed81999039e8a5a4e9c3caf84464408",
  "notes/theory/lean/YulangClosure/OriginalSourceChecking.lean": "a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6",
  "notes/design/2026-10-08-native-signature-formation-definition.md": "e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9",
  "notes/design/2026-10-24-computed-call-result-constructor.md": "2f3a5461b6dacaa29e881ba8b3003120b912e441dd5e4c47fc4ccaa27d3b31a6",
  "tasks/agent-loop/history/20261103-operation-rewrite-capture-review.md": "54daa6836d2d03bc2f03348160fdb86774ec9bb261b090ddf00f62cb42101b8c"
}
```

## Exact theorem types and complete axiom audit

```text
YULANG_AUDIT_BEGIN YulangClosure.SourceEffectRetentionR304.operation_copy_input
YulangClosure.SourceEffectRetentionR304.operation_copy_input : ∀ (s : YulangClosure.NativeContextTables.Store)
  (input : YulangClosure.NativeContextTables.ViewInput) (origin : YulangClosure.NativeContextTables.OperationOrigin),
  input.operation = Option.some origin →
    ∀ (tail : Option Nat),
      YulangClosure.NativeContextTables.copyInput (s.constructView input) s.views.length tail =
        Option.some
          { owner := input.owner, position := input.position, allowed := input.allowed, tail := tail,
            operation := input.operation, attachment := Option.none }
'YulangClosure.SourceEffectRetentionR304.operation_copy_input' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.SourceEffectRetentionR304.operation_copy_input
YULANG_AUDIT_BEGIN YulangClosure.SourceEffectRetentionR304.operation_copy_input_after_run
YulangClosure.SourceEffectRetentionR304.operation_copy_input_after_run : ∀
  (s before : YulangClosure.NativeContextTables.Store) (input : YulangClosure.NativeContextTables.ViewInput)
  (origin : YulangClosure.NativeContextTables.OperationOrigin),
  input.operation = Option.some origin →
    YulangClosure.NativeContextTables.Run (s.constructView input) before →
      ∀ (tail : Option Nat),
        YulangClosure.NativeContextTables.copyInput before s.views.length tail =
          Option.some
            { owner := input.owner, position := input.position, allowed := input.allowed, tail := tail,
              operation := input.operation, attachment := Option.none }
'YulangClosure.SourceEffectRetentionR304.operation_copy_input_after_run' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.SourceEffectRetentionR304.operation_copy_input_after_run
YULANG_AUDIT_BEGIN YulangClosure.SourceEffectRetentionR304.operation_copy_run_after_run
YulangClosure.SourceEffectRetentionR304.operation_copy_run_after_run : ∀
  (s before : YulangClosure.NativeContextTables.Store) (input : YulangClosure.NativeContextTables.ViewInput)
  (origin : YulangClosure.NativeContextTables.OperationOrigin),
  input.operation = Option.some origin →
    YulangClosure.NativeContextTables.Run (s.constructView input) before →
      ∀ (tail : Option Nat),
        before.pending = Option.none →
          YulangClosure.NativeContextTables.IndexFits before.views.length →
            YulangClosure.NativeContextTables.Run before
              (before.constructView
                { owner := input.owner, position := input.position, allowed := input.allowed, tail := tail,
                  operation := input.operation, attachment := Option.none })
'YulangClosure.SourceEffectRetentionR304.operation_copy_run_after_run' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.SourceEffectRetentionR304.operation_copy_run_after_run
YULANG_AUDIT_BEGIN YulangClosure.SourceEffectRetentionR304.operation_copy_readback
YulangClosure.SourceEffectRetentionR304.operation_copy_readback : ∀ (s : YulangClosure.NativeContextTables.Store)
  (input : YulangClosure.NativeContextTables.ViewInput) (origin : YulangClosure.NativeContextTables.OperationOrigin),
  input.operation = Option.some origin →
    ∀ (tail : Option Nat),
      have before := s.constructView input;
      have copied :=
        { owner := input.owner, position := input.position, allowed := input.allowed, tail := tail,
          operation := input.operation, attachment := Option.none };
      (before.constructView copied).views[before.views.length]? =
        Option.some
          { birth := before.clock,
            value :=
              {
                payload :=
                  { allowed := input.allowed, tail := tail, closedWeight := Option.none, owner := input.owner,
                    position := input.position },
                sourceWeight := Option.none, origin := YulangClosure.NativeContextTables.ViewOrigin.operation origin } }
'YulangClosure.SourceEffectRetentionR304.operation_copy_readback' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.SourceEffectRetentionR304.operation_copy_readback
YULANG_AUDIT_BEGIN YulangClosure.SourceEffectRetentionR304.operation_copy_run
YulangClosure.SourceEffectRetentionR304.operation_copy_run : ∀ (s : YulangClosure.NativeContextTables.Store)
  (input : YulangClosure.NativeContextTables.ViewInput) (origin : YulangClosure.NativeContextTables.OperationOrigin),
  input.operation = Option.some origin →
    ∀ (tail : Option Nat),
      YulangClosure.NativeContextTables.IndexFits (s.constructView input).views.length →
        YulangClosure.NativeContextTables.Run (s.constructView input)
          ((s.constructView input).constructView
            { owner := input.owner, position := input.position, allowed := input.allowed, tail := tail,
              operation := input.operation, attachment := Option.none })
'YulangClosure.SourceEffectRetentionR304.operation_copy_run' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.SourceEffectRetentionR304.operation_copy_run
YULANG_AUDIT_BEGIN YulangClosure.SourceEffectRetentionR304.operation_two_copy_run
YulangClosure.SourceEffectRetentionR304.operation_two_copy_run : ∀ (s : YulangClosure.NativeContextTables.Store)
  (input : YulangClosure.NativeContextTables.ViewInput) (origin : YulangClosure.NativeContextTables.OperationOrigin),
  input.operation = Option.some origin →
    ∀ (extrudedTail freshTail : Option Nat),
      YulangClosure.NativeContextTables.IndexFits (s.constructView input).views.length →
        YulangClosure.NativeContextTables.IndexFits
            ((s.constructView input).constructView
                  { owner := input.owner, position := input.position, allowed := input.allowed, tail := extrudedTail,
                    operation := input.operation, attachment := Option.none }).views.length →
          have emitted := s.constructView input;
          have rewritten :=
            emitted.constructView
              { owner := input.owner, position := input.position, allowed := input.allowed, tail := extrudedTail,
                operation := input.operation, attachment := Option.none };
          have fresh :=
            rewritten.constructView
              { owner := input.owner, position := input.position, allowed := input.allowed, tail := freshTail,
                operation := input.operation, attachment := Option.none };
          YulangClosure.NativeContextTables.Run emitted fresh ∧
            fresh.views[rewritten.views.length]? =
              Option.some
                { birth := rewritten.clock,
                  value :=
                    {
                      payload :=
                        { allowed := input.allowed, tail := freshTail, closedWeight := Option.none,
                          owner := input.owner, position := input.position },
                      sourceWeight := Option.none,
                      origin := YulangClosure.NativeContextTables.ViewOrigin.operation origin } }
'YulangClosure.SourceEffectRetentionR304.operation_two_copy_run' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.SourceEffectRetentionR304.operation_two_copy_run
[exit 0]
PASS: YulangClosure.SourceEffectRetentionR304.operation_copy_input, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.SourceEffectRetentionR304.operation_copy_input_after_run, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.SourceEffectRetentionR304.operation_copy_run_after_run, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.SourceEffectRetentionR304.operation_copy_readback, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.SourceEffectRetentionR304.operation_copy_run, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.SourceEffectRetentionR304.operation_two_copy_run, under its printed hypotheses; axiom whitelist satisfied.
Named declarations only; ordinary-mistake check, not independent review or source correspondence.

```
