# Binder packet export trace — assignment N, r9

Status: **bounded source/export obstruction; UNREVIEWED; frozen at submission.**
Author: `/root/binder_packet_export_trace_r9`. Target:
`binder_packet_export_correspondence`. Original N1/O-NORM, O-RESULT and the
original semantics/inference proof parent remain **OPEN**.

## Outcome and exact missing edge

The inspected constructors retain authentic **term** binder/use identity and
construct one shared solver FreshUse map for a local occurrence. They do not
export the paper's **polymorphic type binder linked to a complete View packet**.
The first missing correspondence is at the source annotation/local-source
interface: `SourceAnnotationValue::Variable(Box<str>)` and effect-row variable
spellings are subsequently joined to scoped solver rows, but no inspected
constructor links an enclosing `Lambda a` type binder to an exported packet
template or to its type-application argument `T`.

This is an implementation/export gap in the selected source owners, not a
counterexample to the accepted semantics or a claim that no encoding is possible.
In particular, a spelling-only annotation is not by itself a demonstrated bug:
the actual solver adds `AnnotationScope` and retains shared rows. That machinery
solves a different, narrower representation problem. The missing claim is that
these rows and maps realize the paper's whole-packet binder opening, including
delayed shape and every latent/capture/scope coordinate.

The proposed endpoint “core export” is also a concrete disconnected seam:
the named `yu-core` constructors take shadow HIR/skeletons, not
`CandidateGraphExport` or retained FreshUse maps. Their output carries pending
structural registrations, not a type-instantiable View. The actual inspected
candidate export consumer is the playground's graph/public-type renderer.

## Baseline, authority and dependency receipts

Inherited baseline: `9b945b0bb175e8e0919d388dc720babbdf0c2464`, **not independently
verified**; no Git command was run. Contract
`tasks/agent-loop/sprints/force-producer-export-trace-20261025-r1.md` matches
`d2765f1aabb1b2f81ff65da8a2eae6a3780cefe73f4aa2da639534364c655f7b`.
No accepted decision, language meaning, quantifier or supported source domain
was changed.

Governing paper sections, from the pinned bytes: finite decorator inputs and
delayed shapes (1186–1209), Var/type-application decoration (1241), latent/capture
and common-instance obligations (1528–1541), structural instantiation and
dependency closure (1748–1774), precise type abstraction/application
(2058–2073), and source-indexed scope correspondence (2244–2263).
These require a common instance over the whole packet, retained free identities,
and `Psi(e,j)=s`; equal row/family identities cannot reconstruct that table.
The paper explicitly starts with typed syntax and does not assume an inference
algorithm generates it (1188–1192). Consequently, failure to find that generator
here does not refute its declarative typing rules.

Workflow boundaries used: root/base AGENTS; research-lab and its pre-sprint
source-evidence/lease rules; design-authority authority order and proof-obligation
economy; git-concurrency disjoint leases/frozen review; goal-driven-sprints;
top-level inference principles §§1, 3–5. Sprint/proof skills were read; this
child applies only the assigned packet and starts no team.

All eight contract source pins and paper/N1 pins matched before source claims
were adopted. Additional files are narrowly necessary caller/consumer reads,
recorded below; their digests are observed dependency pins, not independently
verified baseline-commit contents.

| Input | SHA-256 |
|---|---|
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `tasks/agent-loop/inbox/20261025-force-packet-specialization.md` | `7492d74c018645394f54559695cc0f7b3278edce2fbd34eb6f20b06504be0f76` |
| `tasks/agent-loop/sprints/force-source-realization-20261025-r8-outcome.md` | `4c63f6f55a4fd5ee2afeb83a5df575704715b7bc093a1934997b4cb4994ba5eb` |
| `crates/yu-hir/src/module/source_annotation.rs` | `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `crates/yu-solver/src/candidate_source.rs` | `57b119592a6a8d4afd42aca10c5e2bb749cfdf0fb0fdea967dd437d552a1a04e` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-core/src/shadow_derivation.rs` | `714fa4f53ee14f7a4d4e1d38ff0820157838de9c4b70a266bee1998eb2851dc2` |
| `crates/yu-core/src/shadow_source_annotation_crosswalk.rs` | `9a13b7b46d4d239d00d8f54ed93e6bc58064410bd556ab8f797242f2e87f6d5d` |
| `crates/yu-core/src/shadow_call_formation.rs` | `394c763e5b4e2de6ae692ffacf22c07db8958f00129a47f1332f238c9a8eb5eb` |
| `tools/inference-playground/src/scheme.rs` | `82019fd22ad565c753461d8962934fcfe8e6663f8a7971b4fcbc5f5067026be0` |
| `crates/yu-hir/src/module.rs` | `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646` |
| `crates/yu-solver/src/candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-core/src/lib.rs` | `3a2c2befd0dd38df3c06458a7fd918b8f32124a75d264ed51d859ec036c4ab5e` |
| `tools/inference-playground/src/lib.rs` | `45bf78af436efa50e02ca97ba3b639c11f7dd88272d87c47f2822643786653d4` |
| `tools/inference-playground/src/render.rs` | `cfdfdbc031ccc672c7eaa5b73355ec5f6bf5b1a97081e2ff9c9bb0060ab16568` |

Additional-read justification: `module.rs` owns actual HIR carrier publication;
`candidate_effect.rs` is called by the annotation actions; solver `lib.rs` owns
feature gates and transaction publication; `shadow_apply.rs` owns the actual
public graph export/fresh-use interface; core `lib.rs` owns module feature gates;
playground `lib.rs`/`render.rs` are direct export/project consumers. No runtime
normal-leave producer was investigated; that remains assignment R's method.

## Constructor derivation and actual consumers

Hypotheses for this bounded trace: (H1) HIR formation returns a supported carrier
for an admitted root; (H2) the corresponding candidate solve succeeds without
conflicts; (H3) a local-use route commits normally. These are explicit conditional
entry conditions, not a claim that all accepted paper inputs pass those phases.

1. **Authentic lexical binder/use.** `module.rs:2547–2558` invokes
   `local_source::form_ordinary` on the admitted binding and exact root.
   `local_source.rs:2732–2756,2794–2805` creates `HirLocalId { owner, ordinal }`,
   records its parse-owned binder key and stores its annotation/initializer.
   `Work::Publish` at 1325–1331 installs that same local identity; identifier
   formation at 2137–2161 copies the lexical resolution into
   `LocalSourceForm::Name`. This is a real constructor chain, not a crosswalk
   assertion. The exact source literal guarded by
   `shadow_derivation.rs:24`, `my apply f = { my step x = f x; step }`, provides
   a concrete local `step`/returned-use shape. Its final use follows this local
   identity chain if formation succeeds; no parser/compiler was executed here.
2. **Annotation to solver rows.** `source_annotation.rs:404–472` retains the
   annotation owner/position; 525–526 and 655–662 retain type/row variable names;
   663–676 resolves concrete effect declarations. There is no quantified-binder
   constructor in `SourceAnnotationValue` (140–155), or explicit type
   abstraction/application in `LocalSourceForm` (348–440).
   `candidate_source.rs:1538–1549` emits annotation/install actions keyed by the
   same local slot; 1761–1767 emits either an initializer link or `Action::Local`.
   `candidate_effect.rs:1720–1776` constructs paired annotation terms using
   `AnnotationScope::Local(the_same_HirLocalId)` and shared value/effect/view
   maps. Variable occurrences use `(AnnotationScope, spelling)` at
   1307–1325/1344–1362 and 2064–2075. Thus names do acquire contextual row
   identity; they do not acquire a paper type-binder/packet-template link.
3. **Retained scheme and use reconstruction.**
   `candidate_scheme.rs:4736–4755` installs `LocalScheme { capture_region, id,
   root, boundary }`. Local routing at 4903–4946 captures the graph and calls
   `prepare_candidate_fresh_use` once when no local-use frame exists, rejecting
   an already-published occurrence. That function (4199–4279) begins one use
   context and assigns one image per canonical source row. Its actual rule is

   ```text
   image(rep(r)) = prior image, when already mapped;
                = fresh row at use_level, if local && level > boundary && !non_generic;
                = rep(r), otherwise.
   ```

   All captured function children `[a, ae, re, r]` use the same mapped terms
   (4405–4420). Effect operands/views are remapped separately with shared maps
   (4306–4331), contexts at 4349–4366, and each structural term is memoized
   (4371–4378,4496). No supplied type argument `T` enters this API.
4. **Once-only scope of this evidence.** Bound replay consumes the existing
   frame/fresh map and advances its cursor (5070–5088), then marks completion
   (5118). Solver `lib.rs:9503–9521` commits a completed frame through
   `commit_local_use`; `candidate_scheme.rs:1484–1513` moves the same rows/maps
   into `LocalFreshRoute`, indexed by the exact occurrence. Public
   `CandidateInference::fresh_use` (`shadow_apply.rs:2055–2072`) checks ownership,
   conflicts, local identity and matching use instance before returning borrowed
   row observations. Module uses have the analogous retained constructor at
   `candidate_scheme.rs:4635–4701`. This establishes the inspected successful
   constructor path's shared-map use, not a general replay/rollback correctness
   theorem and not the paper's one-time type beta.
5. **Actual export and display consumer.** `shadow_apply.rs:2029–2053` borrows
   the retained graph only after conflict/root checks; its export has state,
   graph and source root (2549–2553), exposing nodes/rows/bounds/permissions
   (2601–2697). Playground `lib.rs:109–127` obtains it;
   `render.rs:58–59` invokes `CandidatePublicScheme::project(...).render(...)`.
   `scheme.rs:75–204` projects rows, nodes, constraints and formal permissions;
   324–345 prints local free rows as quantified names and external rows as
   shared anchors. Its production portion exposes project/render operations,
   not packet opening or type application. Displayed `forall` is not an
   executable polymorphic binder certificate.
6. **Shadow core is a separate branch.** Core `lib.rs:3–28` feature-gates every
   named module. `IncompleteDerivation::from_captured_call` takes a
   `ShadowArtifact`/`CapturedCallInput`, restricts itself to the exact literal
   above and projects term binder/capture IDs into `Node` (13–44,61–166).
   `RawStructuralArena::from_artifact` similarly borrows skeleton forms and
   annotation incidences (355–424); pending-use groups/Apply positions
   (578–625) add no solver graph input. Crosswalk construction
   (89–161) joins source ancestry and inventories calls/annotations without
   associating an annotation packet with a call. Call formation (68–76)
   wraps resolved HIR call inventory as pending stubs. These function bodies
   and field lists establish the boundary; comments and unresolved-premise
   enums are corroboration only. No core instantiation consumer was derived.

## Whole-packet coordinate audit

| Coordinate | Actual retained data | Missing correspondence to the accepted packet |
|---|---|---|
| Binder | Term/local/parameter IDs; scoped annotation name-to-row map | Consumed type binder `a`, its packet/template environment and common argument `T` |
| Profile | Source annotation and formal permission paths | Finite profile automaton/delayed annotation occurrence and type-instance interpretation |
| Family | `SourceEffectId`, operation declaration IDs; exported contribution route/instance and effect-view labels (`shadow_apply.rs:2508–2546`) | Generic family argument template and shared payload/response instance witness |
| Row | Value/effect row keys, locality, bounds, shared FreshUse image | Whole-packet qualified instance law; row equality alone supplies no `Psi` table |
| Delayed shape | Unresolved row nodes; finite structural Function/Tuple/Record/Variant enum (`candidate_scheme.rs:347–365`) | Delayed-shape template owned by the original occurrence, argument descriptor and newly visible ports |
| Latent ports | Four function child coordinates | Whole Delay/force.effect/force.result packet and its instance transport; no thunk/type-application node in this carrier |
| Capture | Lexical closure/capture IDs in shadow core; nonlocal rows retained by FreshUse | Captured View packet with its type-binder links and retained free graph identities |
| Scope/interpretation | Lexical scope enum; optional `ScopeRemap` of regions/scopes/inputs (`candidate_source.rs:176–193`); retained context/view maps | Source-indexed `Psi(e,j)=s` connected to that polymorphic binder; invocation/owner/read interpretation law |
| Identity | Parse keys, HIR brands/occurrences, row representatives, effect contribution instances | Preservation of every existing receiver/reference/event identity under actual packet type application |
| Dictionary/associated type | Retained source prerequisites/selected field metadata in solver graph | One installed dictionary/type-instance opening operation over the whole packet |

These are distinctions between represented fields and unproved bridges, not a
claim that each absent direct field must be a new independent data structure.
Graph state has additional evidence/context storage; the table does not assert
that all scope information is discarded or that internal FreshUse is unsound.

## Falsifier, limits and parent application

The exact missing owner is the **typed decorator / elaborated packet exporter**
between paper 1194–1209,2060–2073 and the selected HIR/solver/core interfaces.
No corresponding callable constructor was found in the inspected path. Its
required interface must select the binder for
`View_c((View_d(Lambda a.v))[T])`, open `a` once in every applicable coordinate
of `d`, retain `c` and free identities, and supply the delayed-shape/latent/scope
instance. Solver `prepare_candidate_fresh_use(graph, use_level, caller_region)`
does not take `a` or `T`; equating it with that interface would assume the
central correspondence being investigated.

Smallest discriminating **proposed** owner test: retain distinct `c` and `d`,
one affected abstract-type occurrence under a delayed force-result profile,
one free outer type coordinate, and two ingress entries for the same annotation
binder. Specialize with an open type descriptor such as `U beta`. The producer
must retain the outer packet/free coordinate, materialize the affected latent
shape, preserve both ingress entries and apply the instance once. A nested type
binder and a shared capture extend the same falsifier to capture/sharing. This
was not executed and is not an accepted-source counterexample. An existing
constructor taking the actual binder, `T` and packet with a concrete caller and
all these equations would falsify this bounded gap report. Merely displaying
local rows as `forall`, reconstructing rows twice consistently, or supplying
r7 with an arbitrary `inst` would not.

Method/oracle independence: this report derives field transport from constructor
bodies and actual callers. It shares the paper's selected requirements and does
not independently validate that semantics. No synthetic checker/oracle,
enumeration, seeds, ranges or mutations were used. Searches covered the eight
assigned files plus the seven named direct owners; repository call-site search
for named core constructors found test clients and the shadow protection
consumer, not an exporter consuming solver packet data. Search is bounded and
is not a proof of global nonexistence, F5 completeness or native behavior.
No matching mapop consumer was crossed. Normal-return execution belongs to R.

The new source evidence reduces N1's unknown exporter to a specific missing
typed-input/binder interface and distinguishes it from an existing successful
FreshUse row-remapping path. R7 remains applicable only after a lossless packet
encoding and its source beta/instance equations are supplied. No Lean theorem,
source safety, principality, native correspondence or production gate closes.

Recommended next action: primary reviews this frozen obstruction, then assigns
the typed-decorator owner to exhibit the missing binder/template export and
its actual type-application consumer, or records that this producer is absent
before choosing the smallest explicitly authorized construction packet.

## Checks, resources and STOP

Checks run: bounded `rg` symbol/caller searches; `nl`/`sed` source inspection;
`sha256sum` dependency comparisons. One r8 hash command initially used the wrong
historical filename and returned missing-file; the correct path above was
subsequently checked before submission. No tests, builds, Lean, native/compiler
execution, scratch output, Git operation, descendants or external contacts.
Only this leased note was written. Review is pending; this author supplies no
independent certification.

Grant: 1,000 seconds source-only, one lightweight shell invocation at a time
except batched independent reads; no heavyweight process. CPU and peak memory
were not measured. Exact launch timestamp is unavailable, so conservatively
charge the full 1,000-second grant; no returned unused budget is claimed.
Requested model/effort in the primary's current record: `gpt-6-sol` / high;
observed model/effort UNKNOWN. No model policy changes or Astra usage.
Observed clock during inspection: 2026-10-25 01:02:39 UTC. The submission receipt
provides the final observed clock and frozen output digest.

**STOP:** writing ceases before frozen review submission. No descendants or
other leased paths exist for this worker. Parent must update the runtime row
from this cessation receipt; this worker does not edit shared state.

## Commit packet

- Exact leased/changed path: `tasks/agent-loop/inbox/20261025-binder-packet-export-trace.md`.
- Baseline: `9b945b0bb175e8e0919d388dc720babbdf0c2464` (inherited, unverified).
- Dependency changes: none observed; all contract pins match. Additional direct
  dependencies and observed hashes are inventoried above for review freezing.
- Claim/review: bounded source obstruction and conditional constructor trace;
  UNREVIEWED research-only checkpoint; N1/O-NORM/O-RESULT/parent OPEN.
- Checks already run: source/caller inspection and SHA-256 comparisons only.
- Proposed one-line message: `research: trace binder packet export and missing type-instance bridge`.
- Shared-record deltas left for primary/curator: record N STOPPED and frozen
  hash, schedule fresh independent review, retain the parent OPEN with the
  typed-decorator/binder export premise, and decide the next exact owner lease.
  No task/index/authority/question/manifest/lockfile was changed; no Git action
  is requested from this worker.
