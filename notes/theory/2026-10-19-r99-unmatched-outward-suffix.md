# R99: unmatched outward request, restored handler, and missing receiving boundary

Status: FROZEN candidate source correspondence and conditional constructor
obstruction, revision 1; no independent review or observed preparation/execution.
Sole author: `/root/r99_proof`. Contract revision 2:
`tasks/agent-loop/sprints/unmatched-outward-suffix-20261019-r99-rev2.md`, SHA-256
`ca4c71fe2bf37118e216b70c186353eb090c3bef1b4d350486321501ecf9a847`.

## Parent and actual result

The finite R99 goal is the unchanged positive/paired-negative source in the
contract: a skipped inner handler is retained in the original request suffix,
an outer handler selects and resumes the request, and the resumed suffix
reaches the inner handler. The positive prediction remains Integer 23; the
negative prediction remains UnhandledRequest for declaration-owned tick with
Integer 7 and its suffix. Both outcomes are UNOBSERVED.

The inspected constructors retain the original local-binding suffix and
actually construct and enter a ForwardHandler node. However, the positive
path exposes a specific missing premise: the remapped fresh inner receiver
has no constructor-owned RootComp receiving boundary. Conditional on successful
public preparation and reaching the traced machine path, `local_grant` returns
false at that receiver and `propagate_request` returns HandlerEvidence for the
resumed other request. This is a static derivation from existing branches,
not an observed failure, reviewed theorem, or source-qualified refutation of
the general source semantics. The contracted prediction is not rewritten.

Apply this result to the parent by replacing an unspecified restoration
premise with the exact outstanding receiving-constructor/consumer seam in
§§4–5. Retention of the control suffix alone does not establish eligibility
of requests emitted after its restoration. No production change follows.

The original H statement remains the universal claim in
`2026-10-11-oracle-global-effect-hygiene-proof.md` §1: every successfully
lowered original-domain program, composed-negative annotation occurrence with
its scope/binders, actual copy/instantiation, and actual function call/output
route must preserve exact authorized contribution removal, independent
same-family contributions, symbolic tails, retained checks, provider/call
binding and residual lineage through copying/generalization. This finite
candidate does not replace any of those quantifiers. The joint assignment
`xi=(nu,K,D)`, complete Call, ordinary inference, source/native correspondence,
soundness/principality and original Simple-sub/evaluator A/B stay OPEN.
F1 and FK1 remain independent; one ForwardHandler action settles neither.
R50 remains NOT_ADOPTED; R85 remains AWAITING_USER_ADOPTION.

Authority: charter §§14–17,21; annotation integration §§1–1.2; directional
protection §§2–2.2; top-level inference principles §§1–5. The ordinary
computation package §5 describes the selected forwarding direction, while its
own Draft/adequacy-unproved status is retained. Simple-sub generation,
accumulation, propagation, levels, extrusion, qualifying intrusion and
generalization receive no altered rule, source restriction or bypass.

## 1. Exact finite inputs and identities

Use the contract's six displayed lines, LF separators and no terminal LF:

```yu
act io:
    our tick: int -> int
    our other: int -> int
my inner (thunk:[io] int) = catch thunk { io::other(p), _ -> p }
my outer (thunk:[io] int) = catch thunk { io::tick(p), k -> k 23 }
my main = outer (inner { my answer = io::tick 7; io::other answer })
```

P is 259 bytes, SHA-256
`2c5f001cb1131882c78b90d4f1ed83810d0a31cd39291df352569aa20844ba2f`.
N changes only outer's pattern `io::tick(p)` to `io::other(p)`; N is
260 bytes, SHA-256
`58fec23165d3f8ae1d2e318b4777b0d3e3e12711b8dc89b315d84e957441ee5b`.
These are in-memory contract-byte calculations, not observed test-fixture
bytes or parsed artifacts. Each program has its own source allocation/module;
printed names never identify IDs across programs.

For each separately, let F be the declaration-owned io family and T/O its
distinct tick/other member IDs. Let RI/RO/RM be the original definition roots;
tI/tO are distinct original formal IDs despite equal spelling thunk; aI/aO
are the distinct retained annotation positions. Let b be main's original
HirLocalId for answer, B its braced Block, I its tick initializer and Z its
final other application. Inner's p and outer's p/k have distinct arm-owned
CatchBinder IDs (payload ordinal 0, continuation ordinal 1). No numeric HIR,
receiver, request or runtime value ID has been observed.

## 2. Authentic producer and preparation correspondence

R88's reviewed finite construction is reused only for applicable declaration,
parenthesized annotated formal, operation-path, Catch pattern, ordered-arm and
ordinary application productions. Its U/O/S outcomes and discard-only
continuations supply no resumption premise here. R92's reviewed Block and
local-publication argument supplies the applicable original local binder,
initializer, final-expression and same-cell consumer facts. Its particular
runtime 23 arose from a live outer receiver with its own Grant; it does not
establish a fresh restored inner receiver's Grant. Its indented BindingBody
repair is unnecessary for R99's inline bodies. R91's failed admission premise,
R98's unexecuted/failed packet, withdrawn bypasses and adoption drafts are not
proof inputs.

The original named-formal constructor is `crates/yu-hir/src/module.rs:2100–2138`;
it mints tI/tO from each original root and ordinal and passes those same
parameters to LocalSource. `module/local_source.rs:596–628` copies their
source keys, IDs and annotations into Lambda and lexical Parameter entries.
`source_annotation.rs:359–386,409–440,531–587` retains each original owner and
annotation position, with outer effects=Some([F]) and primitive Int value.
`source_annotation.rs:135–314` owns family/member declaration formation;
distinct member declaration keys give T != O, both Int -> Int.

`local_source.rs:1091–1102` resolves the unique family/member declarations
for both operation expressions and patterns. `:1117–1183` retains inner's
single O arm and outer's single T arm (O in N), payload/continuation patterns,
arm order and body SourceNodeKeys. `:639–652` installs only each arm's binders
while constructing its body. `:1004–1044` resolves each thunk to its own tI/tO,
inner's body p to its payload binder, and outer's k to its continuation binder.

Main retains Apply(outer, Group(Apply(inner,B))). The braced-primary owner
`crates/yu-syntax/src/statement.rs:522–624` retains delimiters/statements;
`:1115–1160` emits the explicit semicolon as a childless
BlockStatementSeparator. `local_source.rs:1236–1365` accepts the private
zero-formal answer binding followed by final OperatorChain, records b's
original binder key and I, and emits Block([b],Z). Its Work::Initializer and
Work::Publish (`:654–709`) construct I before publishing b for Z. Thus
`io::other answer` names b, not either arm's p or a reconstructed formal.
`set` (`:818–845`) preserves actual node key/range/scope and occurrence.
This is a branch-directed source construction argument; neither a parsed HIR
nor the full parser execution has been observed by this author.

The public preparation recipe is `runtime_receiving.rs:12–38`: shared
SourceText/header, empty syntax environment/imports, LocalSource lowering,
CandidateInference::solve, no candidate conflicts, RuntimeProgram formation,
main selection, source execution roots and start. Actual acceptance is an
independent premise. `shadow_apply.rs:270–272,385–429` performs preflight,
collection and actual candidate solving; `candidate_source.rs:868–883,
1009–1021,1661–1662` retains the original computation formal and dispatches
FormalEntry/FormalAnnotation to their consumers. `candidate_effect.rs:1449–1462`
retains concrete annotation atoms as local handling permission, not a closed
inflow upper bound. These source facts prove no candidate acceptance, native
residual, joint K,D transport or complete inference result for P/N.

Independently, `program.rs:277–330,414–566` validates retained LocalSource
labels and clones those exact resolutions, patterns, bindings and source
sites. It chooses Computation/Execute from outer annotation presence, not
body usage or solved support. `receiving.rs:21–43` accepts the primitive
RootCompSchema only with matching original Lambda/formal/annotation owner.
`program.rs:570–600` schedules main's Apply, leaving the function definitions
as values fetched on demand. `primitive.rs:31–38` rejects any Lambda from the
closed-primitive universe, so P/N require positive local receiving evidence;
the whole-program primitive certificate cannot bypass the seam below.

## 3. Initial entries, request and authentic saved suffix

Assume preparation/start succeeds, normal allocation/resources suffice and
the constructed instructions above are reached. Use symbolic fresh receiver
names rather than guessed ordinals. `machine.rs:879–902` reifies each whole
argument inertly; `:1248–1267` creates actual invocations with original call
and provider SourceSites. Closure computation entry (`:980–1009`) calls
Receiving::enter and constructs original formal receipts. Outer's receiver
uO has view vO rooted at uO; executing its original thunk Name creates
execution xO. Inner's later receiver uI has view vI rooted at uI and execution
xI. Main's argument expressions are not direct-formal Names, so
`direct_formal_root` (`:1478–1495`) supplies no inherited direct-formal image;
the two receiving entries retain independent roots/receipts.

Each Catch installs an actual occurrence with its current owner
(`machine.rs:704–738`). While I executes, Frame::Local retains B, next=1,
its original lexical environment and the uninitialized runtime cell for b
(`:1884–1925`). Tick's declaration makes its payload a Value entry; its
operation invocation returns the carrier before OperationResultConsumer
executes it (`:1030–1080`). Thus the actual tick request qT is made under uI,
with Integer 7, identity T and observations of both authentic xO and xI
(`:1935–1960`, `receiving.rs:208–226`). No operation-payload receiver remains
in the suffix when qT starts propagating.

Read innermost-first, the saved suffix at outer's positive selection is:

```text
Ordinary(Local(B,next=1,environment,cell(b),recursive=false))
Ordinary(RootCompReturn(xI))
HandlerBoundary(inner Catch,inner environment,installation(owner=uI))
ReceiverBoundary(original_activation=uI)
Ordinary(RootCompReturn(xO))
```

Group instructions only forward labels and add no frame. The outer Catch
and uO ReceiverReturn remain live below this suffix. `propagate_request`
(`machine.rs:1549–1598`) validates actual handler installation and compares
resolved operation IDs in order. Inner's O != T takes the mismatch branch;
no missing Grant is interpreted as semantic nonprotection. Unwinding its
RootCompReturn ends xI; saving its CatchReturn emits the actual HandlerBoundary;
unwinding its ReceiverReturn **retires uI** and records its original ID
(`:1719–1759`, `leave_owner:1268–1300`). Outer's xO is ended before inspecting
outer's Catch. Its historical observation/receipt is still available.

Outer's T arm matches qT. Its live receiver uO has its independently created
boundary, original receipt and annotation F. `receiving::local_grant`
(`:230–325`) authenticates qT's observation, joins uO/vO's genuine receipt,
and reaches uO's image. Int payload/result compatibility succeeds under
`primitive_matches` (`machine.rs:1235–1246`). Continuation binder k triggers
actual capture (`:1607–1630`); selecting pops only outer's shallow handler
(`:1633–1640`). Its selected occurrence is not reinstalled by raw resumption.

## 4. Actual template construction, entry and original suffix

`capture_template` (`machine.rs:1309–1378`) translates the preceding saved
frames, not an invented transition list. Its nested root is:

```text
Owner(uO,
  View(xO,
    Owner(uI,
      ForwardHandler(inner Catch,inner environment,owner=uI,
        View(xI,
          Bind(original Local frame,Hole))))))
```

In particular SavedFrame::HandlerBoundary is converted to
TemplateNode::ForwardHandler at `:1348–1357`. No GlobalRead or Root
materialization frame lies in this positive capture; global closure fetches
already completed and main's root remains below outer. The immutable
template (`continuation.rs:13–46`) retains the tick declaration and qT's
original event as lineage, the original lexical references and runtime cell;
it snapshots no store or active-handler configuration.

The selected arm binds p=7 and k=Continuation(template). Applying k to 23
creates a new continuation-call receiver uK (`machine.rs:900–913`).
ResumeArgument validates Int response, pushes ResumeReturn and starts entry
with a fresh control map (`:748–818`). Entry traverses outside inward:

1. Owner(uO) borrows the still-active uO, preserving the resumer as previous
   owner. View(xO) creates a fresh execution occurrence of the **original**
   vO/receipt and a RootCompReturn frame.
2. Owner(uI) finds uI inactive. `enter_template:1403–1436` clones its call/provider
   descriptor, calls new_invocation to mint fresh uI', and records uI -> uI'
   in this per-entry control map. It never reactivates historical uI.
3. ForwardHandler resolves owner uI to uI', checks exact current/live owner,
   and mints a fresh handler occurrence with the original inner code and
   lexical environment (`:1439–1457`). This constructor path really exists.
4. View(xI) invokes only `receiving.execution(xI.view,xI.receipt)` and pushes
   the new execution plus RootCompReturn (`:1460–1467`). It does **not**
   remap the original view/receipt, call Receiving::enter, or allocate a
   receiving boundary/receipt for uI'. Bind restores the original Local
   frame, and Hole returns 23 into it.
5. Local fills that same cell(b) with Value Integer 23, extends its original
   lexical environment with b, and runs original Z (`:1099–1159`). Z reads
   that original cell, applies declaration O, and makes fresh request qO with
   Integer 23 under uI'. qO != qT; its observations come from the replayed
   current executions and its own event, never qT's old event.

This reaches the restored inner Catch, but retention/reinstallation has not
proved its eligibility.

## 5. Exact remaining premise and paired outward path

At qO, unwind removes its local RootCompReturn execution and exposes the
fresh inner Catch. Its operation ID O matches. Installation validation
succeeds because owner=uI' is current/live. Then the closed-primitive bypass
is unavailable and the positive `local_grant` query is mandatory
(`machine.rs:1580–1598`). `receiving.rs:240–255` first requires a boundary
whose receiver equals uI'. There is none: Receiving::enter registered uO and
uI during closure computation entry; the fresh continuation call and template
Owner create invocations but invoke no Receiving::enter. The View branches
only authenticate/replay old view/receipt pairs (`receiving.rs:193–205`).
Consequently the binary search returns Err and local_grant=false before any
image walk. `propagate_request` then returns
`RuntimeUnavailable::HandlerEvidence(inner SourceSite)`; `Machine::step`
(`:496–516`) converts that to Unavailable. This is conditional on the
unobserved public preparation/reachability premises, not a reported run.
It is neither an authentic semantic negative-protection certificate nor
permission to change the source prediction or weaken handling semantics.

N differs only at outer's pattern. Both inner and outer see O != T and
therefore forward the same qT without capture or arm execution. The unwind
retains both HandlerBoundary entries, original Local suffix, ended view
frames and original receiver boundaries. `stop_unhandled_request`
(`machine.rs:1763–1776`) stores request.suffix and observations unchanged and
returns T, original payload 7, original event/source and a ContinuationHandle.
`continuation_depth` (`:471–475`) exposes only saved-frame count: a positive
depth test supports nonempty retention, not exact suffix identity or future
resumability. No external response consumer runs N's saved suffix here.

## 6. Parent application, falsifier and mutual TODOs

The useful finite result is an actual source-to-ForwardHandler construction
plus an exact receiving obstruction at its consumer, rather than another
conditional theorem assuming the missing Grant. It advances the parent by
identifying the first unsupported ownership premise; it closes no universal,
native, A/B or production gate. Native inflow/residual projection, source
typed incidences/receipts with joint K,D, generalized/freshened providers and
witnesses, arbitrary saved contexts/foreign continuations, F1/FK1, R67 and
adoption remain separate obligations. Tests of this finite path cannot supply
those proofs.

| Request | Owner, first missing evidence and exact falsifier |
| --- | --- |
| R99-CONSTRUCTOR-REVIEW-1 | Luna assigns a fresh independent reviewer of these frozen bytes/source pins. Falsifier: an omitted actual entry creates a RootComp boundary for uI', uI stays active at entry, or the traced frame/template order differs. This author is ineligible to certify the result. |
| R99-RUNTIME-1 | Luna owns the single contracted test command after its frozen-output/spec gates, if still authorized under the contract's stop rules. It must preserve both original predictions and any failure. Concrete discriminant: positive completes with Integer 23 versus reaches HandlerEvidence (or fails earlier preparation); negative must preserve T/payload 7 and a saved suffix. Successful completion would falsify this static path analysis and requires the exact missed constructor to be identified; it cannot be presumed. |
| R99-NATIVE-1 | Original native/source owners retain annotation/formal construction (`candidate_source`, `candidate_effect`), constraint solving/transport (`shadow_apply`) and downstream residual/lifecycle consumers. First missing evidence is authentic typed/native correspondence, not a runtime nonempty-suffix count. Falsifier: permission substituted for inflow/residual or original/fresh receiver/provider/witness IDs collapsed. |

No implementation repair proposal or production TODO is issued. Next action
inside this leaf lease is freeze and stop. Any repair, new semantics or new
lease returns to Luna outside R99; this packet authorizes none.

## 7. Frozen dependency bytes

All SHA-256 values below were observed read-only. The six contract source pins
matched; the concurrently leased new runtime_unmatched.rs is not a dependency
of this constructor derivation. R88/R92 closeouts supply review/applicability
receipts only within their stated premises. Historical proof authors are
`/root/r88_proof` and `/root/r92_proof`; H's author/status remains its own
source header. Existing compiler/source authorship is unchanged and not
inferred from runtime or model labels.

| Dependency | SHA-256 |
| --- | --- |
| `tasks/agent-loop/sprints/unmatched-outward-suffix-20261019-r99-rev2.md` | `ca4c71fe2bf37118e216b70c186353eb090c3bef1b4d350486321501ecf9a847` |
| `tasks/agent-loop/sprints/unmatched-outward-suffix-20261019-r99.md` | `322118be5e2be88e1e48f051f0401cff3985ca6fee5dbf9e0c17f3011b4dff24` |
| `tasks/agent-loop/inbox/20261019-r99-spec-review.md` | `22345dace26352e639023887d4bd79d4382fd807e267725db521dbb5b6946079` |
| `tasks/agent-loop/inbox/20261019-r99-spec-delta-review.md` | `58ed0dcbaeeb3b3f793eb4cc9a828e28c1fb46b2f0af4a44fed98a180c6db12c` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-10-02-ordinary-computation-semantics-package.md` | `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `f11c6594e43c29fbfdbca1638b5c548cecc12a5beb192cac743e60f022c1cc73` |
| `notes/design/2026-09-29-intrude-effect-hygiene.md` | `509628603a93d94a2e3ac11c4e80e016469882672a1d45b3b261fa4321964800` |
| `notes/theory/2026-10-11-oracle-global-effect-hygiene-proof.md` | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| `notes/theory/2026-10-19-r88-ordered-selection-source-bridge.md` | `185eff03dfcef4cd9ea346434d60e34b39fcc0f34d46641b160decb58f0f1782` |
| `notes/progress/2026-10-19-r88-closeout.md` | `e190f71dc28010b59a8ccd973d42c7f146622b15cb59df87b96394a6de081bd9` |
| `notes/theory/2026-10-19-r92-indented-binding-body-correspondence.md` | `95b4f651f132c289264e331b580264359f71f0c7da62db7f935972577732463d` |
| `notes/progress/2026-10-19-r92-closeout.md` | `5ddddc68b64ce7e24abee7afe1352ed6dc74ac3a22d8d57b2c3d1646a4a88568` |
| `crates/yu-syntax/src/statement.rs` | `fe8ba4e144b0c3ea5c8f451dddea42f718e9c3087aa77bb81447c61a9d213797` |
| `crates/yu-hir/src/module.rs` | `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a` |
| `crates/yu-hir/src/module/source_annotation.rs` | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| `crates/yu-hir/src/module/local_source.rs` | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` |
| `crates/yu-solver/src/shadow_apply.rs` | `5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb` |
| `crates/yu-solver/src/candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` |
| `crates/yu-solver/src/candidate_effect.rs` | `6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0` |
| `tools/inference-playground/tests/runtime_receiving.rs` | `6ff65fc977c88837ec279b84088a6c2d89ebfc7f78915e7ac985904fcaa26bf2` |
| `tools/inference-playground/src/runtime/program.rs` | `484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11` |
| `tools/inference-playground/src/runtime/primitive.rs` | `97485b9439357497aaf3f19555b1d87eef4aabc955b3a2815f23cf49a65c0153` |
| `tools/inference-playground/src/runtime/machine.rs` | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| `tools/inference-playground/src/runtime/receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| `tools/inference-playground/src/runtime/continuation.rs` | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |

## 8. Checks, resources and cessation

Checks: read-only source/authority inspection, branch-directed finite
derivation, byte lengths and SHA-256. No compiler/parser/solver/runtime
execution, tests, build, model checker, external contact, Git, scratch or
descendants. Source preparation, runtime outcomes and coverage beyond this
finite path remain UNOBSERVED. No independent certification was performed.

Worker `/root/r99_proof`, session
`current-conversation-2026-10-19-r99-unmatched-outward-suffix`.
Requested Sol/high; observed model/effort UNKNOWN/UNKNOWN. Initial revision-1
read-only launch stopped with no edits on Luna's instruction; revision-2 fresh
launch read at 2026-10-19 05:01:40 UTC. The 600-second total proof cap is not
renewed by this restart; both read-only intervals count. Exact freeze/elapsed
receipt and this artifact's hash are in the handoff. Sole new paths: this note
and `tasks/agent-loop/inbox/20261019-r99-proof.md`; no other paths or authors.
After freezing the handoff this writer stops, with no unresolved descendant
lease, and claims no continuing work while awaiting Luna intake/review.
