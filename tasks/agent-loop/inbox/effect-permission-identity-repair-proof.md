# EFFECT-PERMISSION-IDENTITY-REPAIR-20261028/r1 — proof handoff revision 1

Contract SHA-256: `2008579471df100926ca41be4cd6fac780a7c2cc53ae5f5b1555bdec50c19c39`.
Committed baseline: `29b85224b`, branch `yulang3`, plus the contract's frozen overlay.
Worker: `/root/effect_permission_identity_repair_proof`; registered lean_prover leaf;
active-work ACK delivered to primary in this session. Requested role/effort:
lean_prover/bounded; effective model/effort metadata UNKNOWN. Sole author, no
children. Outcome: **kernel-accepted conditional event refinement; parent OPEN;
independent review NOT_RUN by this producer; production authority unchanged**.

## Original claim, corrections and exact scope

Read root AGENTS.md, AGENTS.pre-sprint.md, sprint rules/contract, both Lean-skill
references, design authority, actual original parent and applicable corrections
before construction. Original parent:
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1, 3, 5,
SHA `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`.
It quantifies over every supported original source program, every lawful finite
construction history and every retained extrusion occurrence; retains original
source scope, joint witness/strategy, complete Call/effects and correlated
source evidence. Original typing coverage, soundness, progress, principality
and termination remain OPEN. The missing source-scoped equality lift in §5
is unchanged.

Governing effect policy:
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–5,
including current §§1.1–1.2 (SHA `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`).
Contravariant concrete annotations grant local subtraction permission; only
actual handler inflow is subtracted, symbolic dependencies remain, and independent
same-row lineages remain distinct. §6's retracted example is not used.
Top-level principles §§1–5 retain ordinary generation, accumulation and
propagation. Current qualification correction is
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6: each fixed
Value-birth-level induced graph, preserving distinct source scopes. No research
draft or old success receipt supplies semantics. `SourceProblem.InferenceSoundness`,
`SourceScopedCoverage` and `LocalLaws` in Contracts were inspected; proposition
definitions and law parameters do not instantiate the original source problem.

## Changed paths and preserved failure

Only repository writes:

- `notes/theory/lean/YulangClosure/FormalPermissionConstructorRealization.lean`:
  six case binder lists repaired; final SHA
  `70a89e7ea4589951e5f5e9323b4b2b415003c5868dc3f53ce16129fa67eafdd9`.
- This handoff.

Scratch root throughout:
`/tmp/yulang-effect-permission-identity-repair-20261028-r1/lean-project/`.
All copied inputs, generated `.lake` outputs, diagnostics, argv, wrappers, raw
logs/time and audit extractions are there. Shared cache is untouched. No root
imports/default target, compiler code, expectations, configuration, manifests,
dependencies, global defaults, questions, scheduling records or Git were changed.

Before edits, `preserved-prior/` received exact failed source
`893dcc04d23491b64230a2ebad956c3da88eb3e8b6146479a4aa616abc5f2e58`, prior
failed check-3 log `4c4be4cb64c4942f67b52a41aa53a0172800a16cd3c0d7f53ba9bfbced868f92`,
argv/time/wrapper, prior handoff and manifest; prior successful SourceOrigin log
is also copied unchanged. Fresh `Diagnostic.lean` and check-1.log retain the
same binder failure and actual generated `EffectMemo.rec/casesOn` and
`ViewEvent.rec/casesOn` signatures. Their initial State is a fixed parameter:
`hit` binds only row/view and found; `miss` binds only absent. Only the excess
State binders were removed. No theorem statement or event definition changed.

Fresh diagnostic SHA:
`59a5ff4b807b0500178dd5a4491f155f5b81a915c4e83532b05afceb17599eb3`.
Raw check-1.log SHA:
`7b74d2e210bc1cfb237d839659d789b085849ca209d5f9cea113973f8311a493`.
The failure includes `Too many variable names provided at alternative hit:
3 provided, but 2 expected` and corresponding miss errors. Failures were never
replaced by a successful log.

## Execution and complete audits

Read-only `elan which lake` resolved the installed native executable:
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Actual versions, both exit 0 in both invocations:

```text
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

Two serialized invocations, separately released by primary after frozen-argv,
no-competing-process and fresh memory checks. Each exact outer command is
`/usr/bin/time -v -o <scratch>/check-N.time timeout 60 taskset -c 0 python3 <scratch>/run-check-N.py`.
Complete immutable argument arrays are `check-N-argv.json`; wrappers set
`LEAN_NUM_THREADS=1`, TMPDIR inside scratch, and preserve combined stdout/stderr.
Pinned project arguments are `-j1 -M1024`. No dependencies installed/downloaded.

| Invocation | Actual inner command | Exit | Wall | Max RSS KiB |
| --- | --- | --- | --- | --- |
| 1 | pinned Lake version commands, then `lake env lean -j1 -M1024 Diagnostic.lean` | 1 | 4.79s | 754196 |
| 2 | bundled `check_lean.py --project <scratch> --lake <native-lake> --module YulangClosure.FormalPermissionConstructorRealization --timeout 60`, all 11 repeated `--theorem` arguments | 0 | 2.92s | 967716 |

Invocation 2 executes the version checks, `lake --no-cache build
+YulangClosure.FormalPermissionConstructorRealization` (5-job success), then the
helper's generated audit with `lake --no-cache env lean -j1 -M1024 --root=…`.
All 11 declarations are checked as actual theorem constants with complete printed
types and transitive axiom audits. Only existing read-only SourceOrigin's unused
simp argument warning at :172 is replayed; no new extension warning.

Aggregate wrapper wall 7.71s, measured user+system CPU 3.38s, maximum RSS
967716 KiB < 1 GiB. Exactly 2 of 3 allowed invocations used, 172.29s of the
180s checking bound unspent. No third check is permitted after success by the
packet's failure-and-source-change condition. Reasoning/read duration was not
separately instrumented. There is no running verification process.

Final raw helper log `check-2.log` SHA:
`dfe462498f1bc83c49dbad3ad8ef47edd7a8964e9dfe60ed7fb4230362d831f1`;
`check-2.time` SHA `0c23b6aa0a2432a317ab284b552c016e76688e90b4b4cb7c0369bb5d95184b99`.
Verbatim complete audit extraction `audit-11.txt` SHA:
`af5bfd429ff4271f82f9aa095c92a331146117f09b47301663195368ff27610b`;
reproduced below. Prefix in this table is
`YulangClosure.FormalPermissionConstructorRealization`.

| Theorem | Complete transitive axiom set |
| --- | --- |
| `effect_memo_refines` | propext |
| `signature_event_refines` | propext, Quot.sound |
| `signature_pair_event_refines` | propext, Quot.sound |
| `port_event_refines` | propext, Quot.sound |
| `port_event_birth` | propext |
| `value_events_refine` | propext, Quot.sound |
| `tuple_events_refine` | propext, Quot.sound |
| `value_events_birth` | propext, Quot.sound |
| `tuple_events_birth` | propext, Quot.sound |
| `event_origins_and_births` | propext, Quot.sound |
| `event_catalog_export` | propext, Classical.choice, Quot.sound |

The source search across the four-module changed dependency cone found only
English prose “transitions admit …” in LiveCapture's comment; no proof hole,
project axiom or bypass. Transitive audit evidence is the helper output, not
that search.

### Reused SourceOrigin receipt, unchanged

Read-only `FormalPermissionSourceOrigin.lean` SHA remains exactly
`db37f9d83e450a450d689b9eed46311108e635eb846d268b7a3a567dcee624fd`.
Reuse the prior 12-theorem receipt in
`tasks/agent-loop/inbox/effect-permission-constructor-realization-proof.md`,
“Complete accepted theorem types and transitive axiom results”; its prior raw
check-1.log SHA is
`b52baa4d14fa6d64ecc726f96c29be979781aba8cdafe7316b2ef2a1460e7150`.
That exact log is preserved at `preserved-prior/check-1.log`; all 12 complete
types/axiom blocks were copied verbatim to `reused-source-origin-audit-12.txt`,
SHA `63c8f4b28a0ca17bc4217c7e086f8cb073fc5148dd94179a9d563e6ba83ef61c`.
This is reused evidence from its real prior successful invocation, not a new
12-theorem execution receipt. No old SourceOrigin theorem was reconstructed.

## Source mapping and same-witness parent application

The checked local domain represents scoped effect-memo hit/miss; view hit/miss;
closed or single-tail delegated signature allocation, ordered positive then
negative; omitted and singleton symbolic ports; negative nonempty concrete
grants; Function source order with composed polarity; nonempty Tuple/index
shifts; opaque scalar and computed value/hole lookup. Event constructors compute
their transitions and do not take Origin or Construction conclusions as inputs.

Frozen native source references copied to scratch are the prior
`baseline-candidate_effect.rs` (`7c8e4fe5270fd45cecece80dfbbdff81aa8f294546687938bf89212325fc146b`)
and `baseline-candidate_scheme.rs` (`35c58dca3748595e273cd53bfba07da2be3fd340ec63c56f6a18adea5e514fb1`).
They supply source inspection only; the Rust lane owns the current instrumented
source and actual test receipt.

- `candidate_formal_effect_variable` :1365–1384 corresponds to EffectMemo;
  first unproved allocation is `fresh_effect_at_level(level)` :1373, including
  native State/key/identifier decoding, level/journal/resource effects.
- `candidate_signature_effect` :2256–2318 resolves tails, looks up the local
  view, allocates a port and inserts the actual bound. SignatureBound remains
  returned data: `candidate_signature_view` :2292–2305 and
  `candidate_insert_bound` :2310–2318 are open native transitions.
- `candidate_formal_effect_port` :1518–1569 corresponds to PortEvent, including
  singleton shortcut before delegation and actual negative concrete permission.
  An origin trace before checked byte accounting/permissions.push is insufficient
  to establish successful retention.
- `candidate_formal_value_pair` :1435–1508 corresponds to ValueEvents and
  TupleEvents with the same argument/result ordering, scope and complete paths.

Apply `event_origins_and_births H e member` to a decoded constructor history
`H : ValueEvents c p s shape entries t births`. For that SAME `e`, it returns
`Origin shape p e.path e.allocatedRow e.metadata`, `Owned c e.metadata`, and
`e.allocatedRow ∈ births`. Owned preserves parameter, original occurrence,
owner and scope. For a negative root, `event_catalog_export H` uses the SAME
retained entries and allocated rows in its computed finite-catalog exports.
No separately chosen row/path/metadata witness is introduced.

For the ordinary source example already present in the Rust lane's test
`formal_permission_constructor_owner_domain_graph_export_join`, the two source
paths are `[Element(0), Result]` and `[Element(1), Element(1), Result]`. Each
modeled retained entry must decode its original occurrence, scope, parameter,
owner, source-row position, path and allocated effect-row witness. A Rust trace
must then join that same witness to capture identity, canonical Effect endpoint,
node index, graph root and the exact owner's exported open-tail port. Distinct
original entries are never identified merely because permitted concrete members
match. The checked theorem preserves these two witnesses conditionally on their
actual decoded event histories. At this handoff the Rust lane's final execution
receipt is pending; this producer claims no new native observation or concrete
Lean instantiation from trace strings. The primary consumes that separate receipt.

This application removes the previous failed Lean refinement premise from the
conditional parent chain: events -> Construction -> Origin/Owned and births ->
finite catalog export. **First remaining premise `CONSTRUCTOR-EVENT-DECODING-1`:**
for each actual successful source constructor, construct this SAME Context,
State, shape, retained entries and births event history from real native stores,
without assuming Construction/Origin or success exhaustiveness. Owner: primary
source/proof lane. Required input: native successful transition/key/ID/term
meaning and allocation/view/bound updates; output: checked simulation preserving
all original witness fields; falsifier: an ordinary source-approved success
incompatible with those updates. A finite trace/test cannot discharge the
universal premise.

Subsequent gaps `CONSTRUCTOR-EVENT-CAPTURE-1`, owner primary capture/proof lane:

- Representative/graph-row indexing: EffectRow expansion's `self.row` computes
  canonical row, index and level/local metadata; Node.row still models a raw key.
- Canonical representative transport: supplied `canon` is not authenticated to
  actual session canonicalization/intrusion representatives.
- Actual row/view/tail and bound/evidence/context store extraction, interleaved
  scanner cursors, pending-pop recurrence, interned child indices and node-array
  writes remain open. Finite request lists and a model write log are insufficient.
- Exact endpoint arrival and canonical negative-root publication remain separate
  premises. Equal idxOf values can denote two absent endpoints, as the reused
  `empty_indices_no_arrival` proves.
- Capture identity, final graph root, actual negative-domain membership and exact
  owner export membership are not conclusions of event_catalog_export. Graph
  membership alone supplies neither owner-specific provenance nor the same port.

Original supported records, variants, optional fields, methods, complete Call,
source preflight/refusal handling and all effect hygiene cases remain required
by the parent and are not universally decoded by this local relation. Negative
mixed/empty explicit rows and multiple symbolic variables have no successful
PortEvent encoding here; this reports a represented-domain boundary without
shrinking the original source language. No new LocalLaws, stronger original
hypothesis, source restriction or circular typing definition was introduced.

## Frozen dependencies and stop

Direct Lean dependency hashes: LiveCapture
`0e1bd4f2ae95e798561e014595e66ec9b6d9b342dbd2b15d0d5c9d346838c53e`,
CaptureConstruction
`181d5075e2fa3ed5f4adfe4029b368461638b6ac6f62341ec165e6e3980ee13c`.
Pinned manifest `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`;
helper `a4f10b70297cbf4d8b5bc0c7526bc29783eaf417f1f70e53eeea341d1150dde6`.
Scratch frozen-manifest.json inventories source/config/authority inputs, preserved
failures, argv/wrappers/logs/time, complete audits and generated `.olean` hashes.
Its SHA-256 is `6eaddd8a8f7b423f074dcbefd007b6c799c320d4fbccba97365442fcd776421f`.

Worker **STOPPED / WRITES STOPPED** after this revision and hash notification.
No descendant, Lean/helper/Cargo process or shared generated output remains in
this lane. No further invocation is planned. Artifact is a candidate research
checkpoint awaiting primary intake, fresh independent review and integration;
all original parent, source/native, effect-hygiene and production gates remain
OPEN. A kernel audit is not independent review or semantic certification.

## Verbatim final 11 theorem types and complete axiom results

```text
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionConstructorRealization.effect_memo_refines
@YulangClosure.FormalPermissionConstructorRealization.effect_memo_refines : ∀ {scope name row : Nat}
  {s t : YulangClosure.FormalPermissionSourceOrigin.State} {births : List Nat},
  YulangClosure.FormalPermissionConstructorRealization.EffectMemo scope name s row t births →
    YulangClosure.FormalPermissionSourceOrigin.scopedEffect s scope name = (row, t)
'YulangClosure.FormalPermissionConstructorRealization.effect_memo_refines' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.FormalPermissionConstructorRealization.effect_memo_refines
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionConstructorRealization.signature_event_refines
@YulangClosure.FormalPermissionConstructorRealization.signature_event_refines : ∀
  {c : YulangClosure.FormalPermissionSourceOrigin.Context} {position row : Nat} {concrete : List Nat} {p : Bool}
  {symbolVar : Option Nat} {s t : YulangClosure.FormalPermissionSourceOrigin.State}
  {bound : YulangClosure.FormalPermissionSourceOrigin.SignatureBound} {births : List Nat},
  YulangClosure.FormalPermissionConstructorRealization.SignatureEvent c position concrete p symbolVar s row bound t
      births →
    YulangClosure.FormalPermissionSourceOrigin.signatureEffect c position concrete symbolVar p s = (row, bound, t)
'YulangClosure.FormalPermissionConstructorRealization.signature_event_refines' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionConstructorRealization.signature_event_refines
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionConstructorRealization.signature_pair_event_refines
@YulangClosure.FormalPermissionConstructorRealization.signature_pair_event_refines : ∀
  {c : YulangClosure.FormalPermissionSourceOrigin.Context} {position : Nat} {concrete : List Nat}
  {symbolVar : Option Nat} {s t : YulangClosure.FormalPermissionSourceOrigin.State}
  {ports : YulangClosure.FormalPermissionCaptureConstruction.Ports}
  {bounds : List YulangClosure.FormalPermissionSourceOrigin.SignatureBound} {births : List Nat},
  YulangClosure.FormalPermissionConstructorRealization.SignaturePairEvent c position concrete symbolVar s ports bounds t
      births →
    YulangClosure.FormalPermissionSourceOrigin.signaturePair c position concrete symbolVar s = (ports, bounds, t)
'YulangClosure.FormalPermissionConstructorRealization.signature_pair_event_refines' depends on axioms: [propext,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionConstructorRealization.signature_pair_event_refines
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionConstructorRealization.port_event_refines
@YulangClosure.FormalPermissionConstructorRealization.port_event_refines : ∀
  {c : YulangClosure.FormalPermissionSourceOrigin.Context} {p : Bool}
  {source : YulangClosure.FormalPermissionSourceOrigin.SourcePort}
  {s : YulangClosure.FormalPermissionSourceOrigin.State} {out : YulangClosure.FormalPermissionSourceOrigin.PortResult}
  {births : List Nat},
  YulangClosure.FormalPermissionConstructorRealization.PortEvent c p source s out births →
    YulangClosure.FormalPermissionSourceOrigin.constructPort c p source s = Option.some out
'YulangClosure.FormalPermissionConstructorRealization.port_event_refines' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionConstructorRealization.port_event_refines
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionConstructorRealization.port_event_birth
@YulangClosure.FormalPermissionConstructorRealization.port_event_birth : ∀
  {c : YulangClosure.FormalPermissionSourceOrigin.Context} {p : Bool}
  {source : YulangClosure.FormalPermissionSourceOrigin.SourcePort}
  {s : YulangClosure.FormalPermissionSourceOrigin.State} {out : YulangClosure.FormalPermissionSourceOrigin.PortResult}
  {births : List Nat},
  YulangClosure.FormalPermissionConstructorRealization.PortEvent c p source s out births →
    ∀ {entry : YulangClosure.FormalPermissionLiveCapture.Emission},
      entry ∈ out.entries →
        entry.row ∈ births ∧
          entry.row = s.nextEffect ∧ out.state.nextEffect = s.nextEffect + 1 ∧ entry.metadata.concrete ≠ []
'YulangClosure.FormalPermissionConstructorRealization.port_event_birth' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.FormalPermissionConstructorRealization.port_event_birth
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionConstructorRealization.value_events_refine
@YulangClosure.FormalPermissionConstructorRealization.value_events_refine : ∀
  {c : YulangClosure.FormalPermissionSourceOrigin.Context} {p : Bool}
  {s t : YulangClosure.FormalPermissionSourceOrigin.State}
  {shape : YulangClosure.FormalPermissionCaptureConstruction.Shape}
  {entries : List YulangClosure.FormalPermissionCaptureConstruction.Retained} {births : List Nat},
  YulangClosure.FormalPermissionConstructorRealization.ValueEvents c p s shape entries t births →
    YulangClosure.FormalPermissionSourceOrigin.Construction c p s shape entries t
'YulangClosure.FormalPermissionConstructorRealization.value_events_refine' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionConstructorRealization.value_events_refine
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionConstructorRealization.tuple_events_refine
@YulangClosure.FormalPermissionConstructorRealization.tuple_events_refine : ∀
  {c : YulangClosure.FormalPermissionSourceOrigin.Context} {p : Bool}
  {s t : YulangClosure.FormalPermissionSourceOrigin.State}
  {elements : List YulangClosure.FormalPermissionCaptureConstruction.Shape}
  {entries : List YulangClosure.FormalPermissionCaptureConstruction.Retained} {births : List Nat},
  YulangClosure.FormalPermissionConstructorRealization.TupleEvents c p s elements entries t births →
    YulangClosure.FormalPermissionSourceOrigin.TupleConstruction c p s elements entries t
'YulangClosure.FormalPermissionConstructorRealization.tuple_events_refine' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionConstructorRealization.tuple_events_refine
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionConstructorRealization.value_events_birth
@YulangClosure.FormalPermissionConstructorRealization.value_events_birth : ∀
  {c : YulangClosure.FormalPermissionSourceOrigin.Context} {p : Bool}
  {s t : YulangClosure.FormalPermissionSourceOrigin.State}
  {shape : YulangClosure.FormalPermissionCaptureConstruction.Shape}
  {entries : List YulangClosure.FormalPermissionCaptureConstruction.Retained} {births : List Nat},
  YulangClosure.FormalPermissionConstructorRealization.ValueEvents c p s shape entries t births →
    ∀ (entry : YulangClosure.FormalPermissionCaptureConstruction.Retained),
      entry ∈ entries → entry.allocatedRow ∈ births
'YulangClosure.FormalPermissionConstructorRealization.value_events_birth' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionConstructorRealization.value_events_birth
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionConstructorRealization.tuple_events_birth
@YulangClosure.FormalPermissionConstructorRealization.tuple_events_birth : ∀
  {c : YulangClosure.FormalPermissionSourceOrigin.Context} {p : Bool}
  {s t : YulangClosure.FormalPermissionSourceOrigin.State}
  {elements : List YulangClosure.FormalPermissionCaptureConstruction.Shape}
  {entries : List YulangClosure.FormalPermissionCaptureConstruction.Retained} {births : List Nat},
  YulangClosure.FormalPermissionConstructorRealization.TupleEvents c p s elements entries t births →
    ∀ (entry : YulangClosure.FormalPermissionCaptureConstruction.Retained),
      entry ∈ entries → entry.allocatedRow ∈ births
'YulangClosure.FormalPermissionConstructorRealization.tuple_events_birth' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionConstructorRealization.tuple_events_birth
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionConstructorRealization.event_origins_and_births
@YulangClosure.FormalPermissionConstructorRealization.event_origins_and_births : ∀
  {c : YulangClosure.FormalPermissionSourceOrigin.Context} {p : Bool}
  {s t : YulangClosure.FormalPermissionSourceOrigin.State}
  {shape : YulangClosure.FormalPermissionCaptureConstruction.Shape}
  {entries : List YulangClosure.FormalPermissionCaptureConstruction.Retained} {births : List Nat},
  YulangClosure.FormalPermissionConstructorRealization.ValueEvents c p s shape entries t births →
    ∀ (entry : YulangClosure.FormalPermissionCaptureConstruction.Retained),
      entry ∈ entries →
        YulangClosure.FormalPermissionCaptureConstruction.Origin shape p entry.path entry.allocatedRow entry.metadata ∧
          YulangClosure.FormalPermissionSourceOrigin.Owned c entry.metadata ∧ entry.allocatedRow ∈ births
'YulangClosure.FormalPermissionConstructorRealization.event_origins_and_births' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionConstructorRealization.event_origins_and_births
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionConstructorRealization.event_catalog_export
@YulangClosure.FormalPermissionConstructorRealization.event_catalog_export : ∀
  {c : YulangClosure.FormalPermissionSourceOrigin.Context} {s t : YulangClosure.FormalPermissionSourceOrigin.State}
  {shape : YulangClosure.FormalPermissionCaptureConstruction.Shape}
  {entries : List YulangClosure.FormalPermissionCaptureConstruction.Retained} {births : List Nat},
  YulangClosure.FormalPermissionConstructorRealization.ValueEvents c Bool.false s shape entries t births →
    YulangClosure.FormalPermissionCaptureConstruction.projectAll shape entries =
      Option.some
        (List.map
          (fun e =>
            { metadata := e.metadata, path := e.path,
              port :=
                YulangClosure.FormalPermissionCaptureConstruction.image shape
                  (YulangClosure.FormalPermissionCaptureConstruction.Endpoint.effect
                    (YulangClosure.FormalPermissionCaptureConstruction.Effect.row e.allocatedRow) Bool.false) })
          entries)
'YulangClosure.FormalPermissionConstructorRealization.event_catalog_export' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionConstructorRealization.event_catalog_export
```

## Verbatim reused SourceOrigin 12-theorem receipt (prior invocation)

```text
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionSourceOrigin.memo_hit
YulangClosure.FormalPermissionSourceOrigin.memo_hit : ∀ (table : Nat × Nat → Option Nat) (key : Nat × Nat)
  (next row : Nat),
  table key = Option.some row → YulangClosure.FormalPermissionSourceOrigin.memo table key next = (row, table, next)
'YulangClosure.FormalPermissionSourceOrigin.memo_hit' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.FormalPermissionSourceOrigin.memo_hit
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionSourceOrigin.memo_miss
YulangClosure.FormalPermissionSourceOrigin.memo_miss : ∀ (table : Nat × Nat → Option Nat) (key : Nat × Nat)
  (next : Nat),
  table key = Option.none →
    (YulangClosure.FormalPermissionSourceOrigin.memo table key next).fst = next ∧
      (YulangClosure.FormalPermissionSourceOrigin.memo table key next).snd.snd = next + 1 ∧
        (YulangClosure.FormalPermissionSourceOrigin.memo table key next).snd.fst key = Option.some next
'YulangClosure.FormalPermissionSourceOrigin.memo_miss' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.FormalPermissionSourceOrigin.memo_miss
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionSourceOrigin.signature_pair_closed_allocation
YulangClosure.FormalPermissionSourceOrigin.signature_pair_closed_allocation : ∀
  (c : YulangClosure.FormalPermissionSourceOrigin.Context) (position : Nat) (concrete : List Nat)
  (s : YulangClosure.FormalPermissionSourceOrigin.State),
  (YulangClosure.FormalPermissionSourceOrigin.signaturePair c position concrete Option.none s).fst.positive =
      YulangClosure.FormalPermissionCaptureConstruction.Effect.row s.nextEffect ∧
    (YulangClosure.FormalPermissionSourceOrigin.signaturePair c position concrete Option.none s).fst.negative =
        YulangClosure.FormalPermissionCaptureConstruction.Effect.row (s.nextEffect + 1) ∧
      (YulangClosure.FormalPermissionSourceOrigin.signaturePair c position concrete Option.none s).snd.snd.nextEffect =
        s.nextEffect + 2
'YulangClosure.FormalPermissionSourceOrigin.signature_pair_closed_allocation' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.FormalPermissionSourceOrigin.signature_pair_closed_allocation
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionSourceOrigin.port_origin
@YulangClosure.FormalPermissionSourceOrigin.port_origin : ∀ {c : YulangClosure.FormalPermissionSourceOrigin.Context}
  {p : Bool} {source : YulangClosure.FormalPermissionSourceOrigin.SourcePort}
  {s : YulangClosure.FormalPermissionSourceOrigin.State} {out : YulangClosure.FormalPermissionSourceOrigin.PortResult},
  YulangClosure.FormalPermissionSourceOrigin.constructPort c p source s = Option.some out →
    ∀ {entry : YulangClosure.FormalPermissionLiveCapture.Emission},
      entry ∈ out.entries →
        p = Bool.false ∧
          out.ports =
              YulangClosure.FormalPermissionCaptureConstruction.sharedPorts entry.row (Option.some entry.metadata) ∧
            entry.row = s.nextEffect ∧
              entry.metadata.concrete ≠ [] ∧ YulangClosure.FormalPermissionSourceOrigin.Owned c entry.metadata
'YulangClosure.FormalPermissionSourceOrigin.port_origin' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.FormalPermissionSourceOrigin.port_origin
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionSourceOrigin.construction_origins
@YulangClosure.FormalPermissionSourceOrigin.construction_origins : ∀
  {c : YulangClosure.FormalPermissionSourceOrigin.Context} {p : Bool}
  {s t : YulangClosure.FormalPermissionSourceOrigin.State}
  {shape : YulangClosure.FormalPermissionCaptureConstruction.Shape}
  {entries : List YulangClosure.FormalPermissionCaptureConstruction.Retained},
  YulangClosure.FormalPermissionSourceOrigin.Construction c p s shape entries t →
    ∀ (entry : YulangClosure.FormalPermissionCaptureConstruction.Retained),
      entry ∈ entries →
        YulangClosure.FormalPermissionCaptureConstruction.Origin shape p entry.path entry.allocatedRow entry.metadata ∧
          YulangClosure.FormalPermissionSourceOrigin.Owned c entry.metadata
'YulangClosure.FormalPermissionSourceOrigin.construction_origins' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionSourceOrigin.construction_origins
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionSourceOrigin.tuple_construction_origins
@YulangClosure.FormalPermissionSourceOrigin.tuple_construction_origins : ∀
  {c : YulangClosure.FormalPermissionSourceOrigin.Context} {p : Bool}
  {s t : YulangClosure.FormalPermissionSourceOrigin.State}
  {elements : List YulangClosure.FormalPermissionCaptureConstruction.Shape}
  {entries : List YulangClosure.FormalPermissionCaptureConstruction.Retained},
  YulangClosure.FormalPermissionSourceOrigin.TupleConstruction c p s elements entries t →
    ∀ (entry : YulangClosure.FormalPermissionCaptureConstruction.Retained),
      entry ∈ entries →
        YulangClosure.FormalPermissionCaptureConstruction.Origin
            (YulangClosure.FormalPermissionCaptureConstruction.Shape.tuple elements) p entry.path entry.allocatedRow
            entry.metadata ∧
          YulangClosure.FormalPermissionSourceOrigin.Owned c entry.metadata
'YulangClosure.FormalPermissionSourceOrigin.tuple_construction_origins' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionSourceOrigin.tuple_construction_origins
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionSourceOrigin.constructed_catalog_export
@YulangClosure.FormalPermissionSourceOrigin.constructed_catalog_export : ∀
  {c : YulangClosure.FormalPermissionSourceOrigin.Context} {s t : YulangClosure.FormalPermissionSourceOrigin.State}
  {shape : YulangClosure.FormalPermissionCaptureConstruction.Shape}
  {entries : List YulangClosure.FormalPermissionCaptureConstruction.Retained},
  YulangClosure.FormalPermissionSourceOrigin.Construction c Bool.false s shape entries t →
    YulangClosure.FormalPermissionCaptureConstruction.projectAll shape entries =
      Option.some
        (List.map
          (fun e =>
            { metadata := e.metadata, path := e.path,
              port :=
                YulangClosure.FormalPermissionCaptureConstruction.image shape
                  (YulangClosure.FormalPermissionCaptureConstruction.Endpoint.effect
                    (YulangClosure.FormalPermissionCaptureConstruction.Effect.row e.allocatedRow) Bool.false) })
          entries)
'YulangClosure.FormalPermissionSourceOrigin.constructed_catalog_export' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionSourceOrigin.constructed_catalog_export
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionSourceOrigin.parameter_capture_identity
YulangClosure.FormalPermissionSourceOrigin.parameter_capture_identity : ∀
  (d : YulangClosure.FormalPermissionSourceOrigin.Domain),
  d.liveRow = d.parameterBase + d.context.parameter ∧
    d.negativeRoot = YulangClosure.FormalPermissionCaptureConstruction.Endpoint.value d.shape Bool.false
'YulangClosure.FormalPermissionSourceOrigin.parameter_capture_identity' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.FormalPermissionSourceOrigin.parameter_capture_identity
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionSourceOrigin.pop_write_lifo
YulangClosure.FormalPermissionSourceOrigin.pop_write_lifo : ∀
  (canon :
    YulangClosure.FormalPermissionCaptureConstruction.Endpoint →
      YulangClosure.FormalPermissionCaptureConstruction.Endpoint)
  (s : YulangClosure.FormalPermissionSourceOrigin.Live) (e : YulangClosure.FormalPermissionCaptureConstruction.Endpoint)
  (rest : List YulangClosure.FormalPermissionCaptureConstruction.Endpoint),
  s.capture.pending = e :: rest →
    YulangClosure.FormalPermissionSourceOrigin.Live.popWrite canon s =
      Option.some
        {
          capture :=
            YulangClosure.FormalPermissionLiveCapture.Capture.internAll canon
              (have __src := s.capture;
              { keys := __src.keys, pending := rest, expanded := s.capture.expanded ++ [e] })
              (YulangClosure.FormalPermissionCaptureConstruction.children e),
          writes :=
            s.writes ++
              [(s.capture.index e,
                  YulangClosure.FormalPermissionCaptureConstruction.expand
                    (fun child =>
                      (YulangClosure.FormalPermissionLiveCapture.Capture.internAll canon
                            (have __src := s.capture;
                            { keys := __src.keys, pending := rest, expanded := s.capture.expanded ++ [e] })
                            (YulangClosure.FormalPermissionCaptureConstruction.children e)).index
                        (canon child))
                    e)] }
'YulangClosure.FormalPermissionSourceOrigin.pop_write_lifo' depends on axioms: [propext, Classical.choice, Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionSourceOrigin.pop_write_lifo
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionSourceOrigin.discovery_membership
YulangClosure.FormalPermissionSourceOrigin.discovery_membership : ∀
  (canon :
    YulangClosure.FormalPermissionCaptureConstruction.Endpoint →
      YulangClosure.FormalPermissionCaptureConstruction.Endpoint)
  (store : YulangClosure.FormalPermissionSourceOrigin.DiscoveryStore)
  (kind : YulangClosure.FormalPermissionSourceOrigin.Discovery) (index : Nat)
  (s : YulangClosure.FormalPermissionSourceOrigin.Live)
  (e : YulangClosure.FormalPermissionCaptureConstruction.Endpoint),
  e ∈ YulangClosure.FormalPermissionSourceOrigin.Discovery.requests store kind index →
    canon e ∈ (YulangClosure.FormalPermissionSourceOrigin.Live.discover canon store kind index s).capture.keys
'YulangClosure.FormalPermissionSourceOrigin.discovery_membership' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionSourceOrigin.discovery_membership
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionSourceOrigin.canonical_function_publication
YulangClosure.FormalPermissionSourceOrigin.canonical_function_publication : ∀
  (canon :
    YulangClosure.FormalPermissionCaptureConstruction.Endpoint →
      YulangClosure.FormalPermissionCaptureConstruction.Endpoint)
  (s : YulangClosure.FormalPermissionLiveCapture.Capture)
  (a r : YulangClosure.FormalPermissionCaptureConstruction.Shape)
  (ae re : YulangClosure.FormalPermissionCaptureConstruction.Ports),
  canon (YulangClosure.FormalPermissionCaptureConstruction.Endpoint.value (a.function ae r re) Bool.false) =
      YulangClosure.FormalPermissionCaptureConstruction.Endpoint.value (a.function ae r re) Bool.false →
    canon (YulangClosure.FormalPermissionCaptureConstruction.Endpoint.value (a.function ae r re) Bool.false) ∈ s.keys →
      YulangClosure.FormalPermissionLiveCapture.publish s (a.function ae r re) =
        Option.some
          (s.index
            (canon (YulangClosure.FormalPermissionCaptureConstruction.Endpoint.value (a.function ae r re) Bool.false)))
'YulangClosure.FormalPermissionSourceOrigin.canonical_function_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionSourceOrigin.canonical_function_publication
YULANG_AUDIT_BEGIN YulangClosure.FormalPermissionSourceOrigin.empty_indices_no_arrival
YulangClosure.FormalPermissionSourceOrigin.empty_indices_no_arrival : ∀
  (first second : YulangClosure.FormalPermissionCaptureConstruction.Endpoint),
  List.idxOf first [] = List.idxOf second [] ∧ ¬first ∈ []
'YulangClosure.FormalPermissionSourceOrigin.empty_indices_no_arrival' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.FormalPermissionSourceOrigin.empty_indices_no_arrival
```
