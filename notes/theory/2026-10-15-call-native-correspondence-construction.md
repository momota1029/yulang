# Complete Call to native construction: bounded correspondence and first obstruction

Date: 2026-10-15
Status: unreviewed bounded constructive bridge/obstruction; frozen on handoff
Job: H1-G, constructive leaf
Baseline: `b336999a148eaee7779f80e0a18e9e79e2cd8394`
Branch: `research/simple-sub-intrusion`
Exclusive output: this file only
Parent status: H1/H2/U OPEN; H3/P disabled; no production authority

## 1. Frozen objective, quantifiers and exclusions

The unchanged parent quantifies over **all originally admitted shallow Catch**
instances, their original scrutinee, formal and arm binders, actual providers,
complete Call and future interfaces, raw resumptions and residual lineages,
under one original scoped assignment `sigma`. Consumed, protected, unmatched,
outside-arm and resumed contributions remain distinct. This note neither
restricts that domain nor supplies a satisfying whole-program assignment.

The bounded question is which arrows from the selected source Call constructors
to current native constructors and the typed-evidence consumer follow from
their actual definitions. For each authentic collected Apply `c`, keep its
original owner, lexical/formal/capture route, source scope and checking origin.
The local construction hypotheses are successful LocalSource formation and
resolution, enabled candidate graph effects, successful fallible native
admission, and an actual positive/negative Function pair where Function dispatch
is discussed. These hypotheses describe a conditional static constructor path;
they are not a claim that any illustrative whole source is admitted or runs.

Required complete correspondence would instantiate, at those same indices,
the actual emitted original record

```text
Idx(e) = (B,X,xi,Delta_e;
          d_f,A_f,R_f,u_f,u_x,c,u,U_e,beta,p0,p_out(c),ElimOrigin),
xi = (nu,K,D), beta = (d_f,R_f),
```

its authentic `Q_e` and `FrameCall(e,Q_e)`, and relate their actual receiver,
entry/body/designated-consumer/return and output-dependent future interface to
the native ports and exact typed evidence. Every interpretation uses the same
`sigma` on the entire original tuple, with original binders and scopes retained.
No independent per-port witness choices are permitted. A universal statement
about such a `sigma` does not assert an inhabitant exists.

Excluded premises: complete emitted Gen-Call-0 membership, complete C0,
actual execution or receiving boundary, received/captured/returned typed paths,
matching Receive/Observe, live roots, exact normal-return expiry, and any
satisfying whole-program assignment. These are not smuggled in through
successful comparison, scalar source IDs, raw row equality or a decorated
Draft machine. The conclusion below is the justified static prefix and first
missing edge, not the parent theorem, source execution, soundness or
principality. No endpoint reconstruction or executable probe is used.

## 2. Governing source meaning is already selected

The exact governing sections are:

| Source | Governing content used here |
| --- | --- |
| Original Call formation, `notes/design/2026-10-07-original-call-formation-definition.md` §§2–4 | `OSig-Demand` and `OC-CallEff` on actual emitted records; exact eight projections; `Inv` root interpreted by complete `J_call(d;xi) = ExecuteCallable` |
| Complete Call contributions, `notes/design/2026-10-07-complete-call-contribution-definition.md` §2 | Receiver `C-Inv`/`InvMem` distinct from complete `C-Call`/`CallMem`; actual returned provider, whole argument, current configuration, full alternative/future interface and original evidence |
| Source interfaces, `notes/design/2026-10-08-call-source-interface-definition.md` §§3–4; `notes/theory/2026-10-08-call-source-interface-construction.md` §4 | Dependent `FrameCall` callee/whole-carrier/actual-provider receiver/return/future/arm/source slots; O0 supplies only one receiver edge |
| `notes/theory/2026-10-07-owned-call-contribution-construction.md` §§3–5 | Exact receiver witness and whole-Call witness retained verbatim, with independent typing; structural callee Bind and its distinct pending suffixes; authentic `SpecCall_e` |
| Inferred call views, `notes/design/2026-10-05-inferred-function-call-views.md` §§1–3 | One source contract and joint assignment; static slot differs from activated receiver; actual provider role/entry unchanged |
| Directional addendum, `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` §§2–4 | Omitted protected variable's original upper output-effect introduction only; no provider/lower backflow or automatic nested-result protection |
| Charter, `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` §§13–15 | Corresponding typed-value transport and expiry; outside selection/arms; current-state raw resumption without shallow-handler reinstallation |
| Top-level inference principles, `notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1,1.1,3 | Native constraint construction/accumulation/propagation, not execution or solved-type prerequisites; retain source correspondence |

In particular, unfolding the selected complete operation gives

```text
EvalCall(Q_e,h) = CalleeRef_e(h) >>= S_h
S_h(actual_f,C1) = ExecuteCallable(actual_f,WholeArgRef_e(h),C1; ...).
```

The receiver is the actual callee result in its current configuration, not the
checking demand `U_e`. Its invocation root includes entry, body, designated
consumers and native/invocation return delimiters, excluding preceding callee
computation. `FrameCall` separately retains the complete Call result and the
future interface dependent on that tuple's actual output provider. Opaque
alternative clauses keep their original whole evidence and licenses; they
need not be executions. `CallMem` retains the original whole-operation witness
before observation projection. These selected definitions resolve source
meaning; they do not assert current compiler implementation correspondence.

The reviewed H1-F inputs are
`notes/theory/2026-10-15-receiver-entry-source-derived-map.md` and
`notes/progress/2026-10-15-receiver-entry-derived-map-falsifier.md`. Their static
versus executing-receiver distinction and source/native obstruction are carried
forward. No conditional transport theorem is restarted here.

## 3. Direct native constructor derivation

All code locators below refer to the pinned baseline.

**D1 — Actual syntax and binder identity.**
`crates/yu-hir/src/module/local_source.rs:115–180` stores each expression's
`occurrence`, `source`, `scope` and `form`. Apply retains separate `callee` and
`argument`; Lambda retains `LocalSourceParameter` and `body`. Parameter and
CatchBinder resolution are different constructors. At `:640–684`, empty call
syntax creates an explicit Unit argument. Thus `cb()` is an Apply with a Unit
child, without identifying its inference endpoint with the Unit leaf or an
empty whole computation contract.

**D2 — Registered formal and native root.**
`candidate_source.rs:273–285` creates `FormalRegistrationInput` with owner,
Lambda index, parameter identity, original annotation scope and parameter
recipe position. Parameter Names use that parameter endpoint and register their
actual lexical occurrence (`:298–304,327–334`). Annotation absence retains
`OmittedFormal { owner,lambda,formal,position,scope }` at the Lambda
(`:382–397`). At initialization `:747–775`, the recipe position must still name
that same parameter and have no prior native root; the constructor stores its
positive native Value root once. This is the precise static root retained by
`CandidateSourceCall::native_registered_root` (`candidate_call.rs:228–235`).
It is not the semantic complete `R_f` with its original whole interface merely
because its provenance agrees.

**D3 — One actual Apply recipe and its native negative Function.**
`candidate_source.rs:604–621` retains `CandidateRelation::Apply` and one
`ApplySourceInput`, including original owner/expression/child indices, source
level, recipe index, callee/argument Value and evaluation-effect endpoints,
result/application-effect components, checking occurrence and cause. The
recipe refers back through `source_input`; wrapper paths carry the same formal
Name registration where supported.

`shadow_apply.rs:1432–1451` checks that recipe and input agree before admission.
At `:1464–1496`, write the actual fresh invocation-effect row as `i_c`; the
constructor builds

```text
U_c = Function4(a_c+, Earg_c+, i_c-, r_c-)
f_c+ <: U_c.
```

The raw terms are exactly `NativeInterface.argument`, `.argument_effect`,
`.invocation_effect` and `.result`; `.demand` retains `U_c`, `.callee` retains
`f_c+`, and `.invocation_row` retains `i_c`'s raw ordinal. The source input
also retains `.callee_effect` and `.application_effect` (`:1521–1525`). For an
authenticated omitted-formal route, `.introduction` stores the original
omission/registration/Name, checking/cause, complete *native* demand and exactly
`FunctionField::ResultEffect`/`i_c-` before constraint admission (`:1497–1525`).
This word “complete” describes all four native Function fields, not semantic
complete Function admission or the full original Call interface.

The owner then records/adopts the Value constraint and calls
`constrain_live_value` (`:1531–1544`); graph effects add
`Ecallee_c <: Eapplication_c` and `i_c <: Eapplication_c`
(`:1566–1584,1590–1613`). These are generation and actual propagation calls,
not only a collection of inert constraints. Their invocation does not prove
all-path completion/replay or semantic satisfaction. Row inclusion records no
ordered callee/receiver suffix or returned-provider future telescope.

**D4 — Observer authenticates precisely that static output.**
`candidate_call.rs:340–535` reborrows the original HIR and checks owner,
Apply/child indices, checking/cause, original scopes, native Function fields
and port polarities, raw invocation row, formal Name route, registration/root,
and exact omission/introduction match. A successful observation returns those
borrows, not an emitted original record or receipt. In particular, it validates
the registered root as a positive Value port; this is not independent original
semantic typing or a complete source-root relation.

**D5 — Lambda and Function4 consumer.**
`lib.rs:11254–11420` constructs the Lambda's positive Function from its actual
domain/body/result endpoints. With graph effects it adds entry-to-returned and
body-to-returned constraints (slots 3 and 4), and retains
`InferredEntryOrigin { lambda,entry,returned,occurrence,cause }` for slot 3.
Where the raw omitted domain is authenticated, it retains
`FormalConstruction { source,domain,domain_child,function }`.
`candidate_context.rs:157–171,274–282` explicitly distinguishes these from an
entry certificate, callback contract and runtime receipt.

When propagation exposes an actual positive Function `L` against negative
Function `U`, `lib.rs:12551–12579` constructs exactly four children:

```text
Argument:       U.argument+       <: L.argument-
ArgumentEffect: U.argumentEffect+ <: L.argumentEffect-
ResultEffect:   L.resultEffect+   <: U.resultEffect-
Result:         L.result+         <: U.result-.
```

`lib.rs:12594–12617,12695–12728` retains/admits/enqueues these children;
`candidate_context.rs:2778–2825` retains a `Dependency::FunctionPort` with
`Swap` on the argument fields and `Preserve` on the result fields. An Apply
against a variable alone accumulates bounds and may extrude; it does not yet
justify this paired-Function dispatch. Neither FunctionPort dependency nor
solver return-ready state denotes an executing receiver or source return.
For the original Value Apply seed, `candidate_context_source/seed:2683–2738`
constructs IDENTITY absent a closed Allowance; execution at IDENTITY returns
false (`:2964–2972`). No new receiver/protection operation follows from D3.

**D6 — Storage lifecycle does not fill the semantic gap.**
The input starts with `native: None, introduction: None` in D3. D3 fills it
before fallible constraint admission and rejects double filling. Public
candidate source observation revalidates the stored carrier
(`shadow_apply.rs:302–305`). Candidate completion transfers `candidate_calls`
into frozen inference data (`lib.rs:17633–17639`);
`finish_candidate:10389–10395` asserts no closed types or public schemes.
These facts concern private inference storage. A successful suspension must
retain accepted facts and continuations under the top-level principles, but
this note proves no complete replay or failed-route restoration theorem.
Neither inference completion nor typed-drain acknowledgement can stand for
normal runtime receiver expiry.

## 4. First missing edge: native source-record interpretation

The derivation stops between D1–D4 and instantiation of the original `e` and
its complete operator interface. There is no established map in these owners

```text
authentic LocalSource Apply + retained native source/Function4 fields
  -> actual original Gen-Call-0 instance at B,X,xi,Delta_e,
     with its original complete demand/ElimOrigin and authentic Q_e/FrameCall.
```

This is an unsupplied source-to-native relation, not an absent source Call
definition. `candidate_call.rs:135–175,269–300` explicitly returns all original
Gen-Call-0 coordinates as required and includes pending suppliers
`OriginalGenCall0`, `ArgumentReifyAndWholeCarrier`, and
`ReceiverDispatchAndCompleteResultFutureInterfaces` even when all static
observations succeed. Formal routes also retain the separate pending whole
registration/introduction/exposure suppliers. A recipe's negative Function is
not sufficient to discharge any of those complete semantic interfaces.
Already `OriginalGenCall0` is unsupplied; authentic `Q_e`/`FrameCall` and
execution evidence are additional obligations, not inputs silently granted by
the static occurrence correspondence.

The separate core route confirms the boundary without resolving it:
`crates/yu-core/src/shadow_call_formation.rs:1–39,41–80,200–277` retains
`PendingResolvedSourceCallStub` and `SymbolicGenCall0`; successful symbolic
generation still lists `EmittedGenCall0Membership`, original B/X/xi/types/scopes,
`CompleteEmittedOriginalCallClauseAndJointWitness`, complete invocation
interpretation and legal whole-tuple substitution as unresolved. Its symbolic
`signature_root`/`call_effect` do not produce original semantic witnesses.
The checked-in crosswalk test at
`shadow_candidate_call_formation_crosswalk.rs:318–404` authenticates one captured
source topology and exact operand identities, expressly keeping the complete
original clause/joint witness and invocation interpretation unresolved. It
also asserts returning `step` creates no invocation. This worker did not run
that test, and its static asserted scope is not evidence for the relay source.

The mathematical Gen-Call-0 source construction in
`notes/progress/2026-10-06-source-call-generation-construction.md` §§4.2–4.4
already gives the original singleton static schema, retaining scope/capture and
distinguishing `ElimOrigin` from runtime Flow/Observe/receipt. Applying that
schema requires its actual source-elaboration premises. A native rooted Value
port alone does not independently establish the complete original typed
interfaces or their same-assignment interpretation. Its §5 also explicitly
labels the further decorated certificate as supplied rather than generated.

**Exact owner:** source/operator elaboration at
`candidate_source.rs`'s Apply/registration construction and
`shadow_apply.rs::admit_candidate_fact`, with the interpretation/export seam
currently exposed by `candidate_call.rs::PendingCallConstruction`. The original
theory supplies the semantic target; `yu-core::shadow_typed_evidence` is a
downstream conditional consumer, not the source of the missing interpretation.
No complete record is assumed and no source impossibility is claimed. The
bounded inspection does not prove no other implementation could supply it.

## 5. Relay keeps two calls and one assignment

Use only an illustrative constructor locator, without asserting admission:

```yulang
my relay cb = catch cb() { v -> v }
my provider ignored = 1
my answer = relay provider
```

`C_in` is `relay provider`; `C_cb` is `cb()`. D3 at `C_in` relates the supplied
provider through the receiving relay Function's **Argument** child. D2/D3 at
`C_cb` relate the original formal cb to `U_cb` with Unit argument and its own
`ResultEffect` introduction. `C_cb`'s checking occurrence is not the receipt
of provider by relay at `C_in`. The two native interfaces use different
application occurrences and result rows while sharing the actual formal/
provider constraint graph. Under any original interpretation all of them
must be evaluated by the same `sigma`, including original `nu,K,D`; they
cannot be satisfied by independently selected marginal witnesses.

The Catch value binder statically aliases the original scrutinee endpoint
(`candidate_source.rs:418–425`). This does not produce a returned latent typed
path, nor copy `U_cb.ResultEffect` protection onto effect positions inside the
returned value. Captured Names similarly retain static registration without
becoming execution receipts. Charter §13 and directional §§2–4 require the
independently corresponding typed signature path for every such transport.

## 6. Exact downstream typed consumer and suffix requirements

The following requirements remain **downstream of the first missing edge**;
none is a hypothesis used to derive D1–D6.

`yu-core/src/shadow_typed_evidence.rs:26–84` accepts a supplied common context,
typed ports `(view,position)`, profiles, Flow, observations and receipts and
validates wiring. Its view denotes `(value,signature,evidence root)` (`:151–158`).
`query_conditionally:92–148` finds an endpoint only when the exact event witness
matches Observe and the same port has a Receive with the candidate's owner.
It follows Flow from the selected profile port and additionally requires
membership of candidate handler, candidate owner and the profile boundary's
immutable `original_receiver` in their respective current active root arrays.
The result is `ConditionalStatus::Assumed`. `AssumedBoundary`, `AssumedProfile`,
`AssumedReceive` and `AssumedConfiguration` (`:160–218`) are all caller inputs.
No examined HIR/solver construction instantiates this query's required packet.

The complete Call's callee-pending suffix and receiver-argument-pending suffix
remain different. Source §4.2 of the owned construction gives, respectively,

```text
Request(q,C,k_f) >>= S_h
  = Request(q,C,(response,C'). k_f(response,C') >>= S_h)

Request(q,C,k_arg) >>= S_after_entry
  = Request(q,C,(response,C'). k_arg(response,C') >>= S_after_entry).
```

The second suffix retains typed rebind/body/native-return/designated-consumer/
invocation-return without replaying entry receipt. Current `C'` is used, and
the shallow selected handler is not reinstalled. Native effect-row inclusion
does not establish those ordered operational equalities. The returned/future
provider remains dependent on the actual arm/output, including alternatives;
the native Result field alone does not instantiate that complete interface.

`candidate_effect.rs:806–863` constructs raw continuation Function ports from
response and original scrutinee endpoints; it retains entry and provisional
conservative full-S effects. Its own comment says exact suffix effects may be
empty and full hygiene remains OPEN. This is not a saved executable-span,
historical-receiver/current-root or exact delimiter interpretation. The three
required cases therefore remain separate: resuming while the saved receiver
is live; running saved code after it expires; retaining historical receiver
identity while a distinct current receiver executes. Normal-return alpha
followed by beta entering the same static `C_in` also remains unqualified.
Draft borrowed enter/leave is one proposed realization of these cases, not an
adopted native mechanism or a premise of this note.

## 7. Economy audit and one next action

H1-F's constructive and falsification methods already left this source/native
premise open. This packet follows the owning fields and both native/symbolic
source-record interfaces directly; it reaches the same premise earlier than
any runtime token calculation. It is **not progress on parent proof closure**.
Another transport lemma assuming FrameCall, profile/receipt/current roots, or
another supplied-token checker would leave the premise unchanged.

Under `rules/compiler-engineering.md`'s economy audit, the required same-source
complete Call/typed-evidence interpretation is A/B, because effect hygiene and
ordinary inference depend on it. Static provenance retention is already
available at the source owners; it eliminates some D reconstruction, but a
certificate cannot manufacture the independently missing complete semantic
typing/dispatch/interface interpretation. No C characterization or D label
retires this parent requirement. No new source restriction is justified.

**One next action:** the primary should assign the owning native Call
elaboration seam a concrete same-`sigma` interpretation obligation for its
existing complete-demand and whole-carrier ports, against the selected
Gen-Call-0/FrameCall interfaces, before adding any receiver/profile operation.
That packet must exhibit the actual original formation/interface evidence or
name its missing native producer; it must not begin by supplying that evidence
as an assumption. This is an owner/interface action, not a fourth equivalent
typed-transport proof. H1/H2/U stay OPEN; H3/P stay disabled.

## 8. Checks, resources and omissions

Commands used: read-only HEAD/status inspection, bounded `cat`/`sed`/`rg`, and
Python stdlib SHA-256 comparison against `git show <baseline>:<path>`. Initial
aggregate captures truncated; decisive authority/code ranges were reread
narrowly. All 30 direct dependencies listed below matched the assigned baseline
byte-for-byte at comparison. No changed dependency was consumed. Artifact
whitespace and exact write-scope inspection passed. At the submission recheck,
HEAD had advanced concurrently to
`ce6c54932a7ce7536bb8e9e29b6b6ad9b51ccc6c`; all 30 dependencies still matched
the assigned baseline. Only this leased path was written by this worker; the
other visible untracked falsifier belongs to the concurrent lane.

One constructive leaf; no descendants or reviewer contact. Allocation at most
25 minutes, early stop at first missing source/native premise. Exact elapsed,
CPU/RSS use unmeasured. Zero tests, builds, Cargo, semantic probes, measurements,
performance samples or Git mutations. Primary retains verification ownership.
Requested route: configured `prover`, normal Sol/high. The callable schema
contains `prover`; inspected config registers it with unpinned model/effort and
Sol/high subagent defaults. Observed effective runtime model/effort: **unknown**;
no runtime metadata was supplied to this leaf. No Astra override or nested
launch was attempted.

Unverified: illustrative source parsing/admission/execution; existence of any
complete satisfying assignment; all-source Gen-Call-0/FrameCall emission;
semantic whole-carrier compatibility; complete provider/role/phase/future/arm
interfaces; original license/admission and attachment witnesses; actual typed
paths, profile/event/receipt/root formation; normal expiry and raw re-entry;
all-path propagation/replay/generalization; abnormal publication; general
hygiene, soundness, principality and F5/production cutover. No failure or
impossibility of these properties is established here.

### Dependency SHA-256 at the pinned baseline

```text
a0a114b589e8920af8e8fd871d15f63d68b735fc1a553f5a89952b1eab8489e5 rules/orchestration-budget.md
8b418f8ed02606205ecdfedcf5da72dae074e1c799237b8cc034fdfbd71ab7a1 rules/agent-orchestration.md
3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69 rules/research-lab.md
e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1 rules/design-authority.md
4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9 rules/compiler-engineering.md
2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6 rules/git-concurrency.md
993d4c2a7743669b4c7a6c46f054c4caae492873f0a5f20a1ea566ebf9dea3c1 .codex/config.toml
485a26c7409e16c692ad10095031ab0e7084726ec5da5666082b3bbc4a5daf98 .codex/agents/prover.toml
4940e031b83d3d0315f17beb51ba2e952ec64ae7d57d9ae0d086024c7305ca9f notes/design/2026-10-07-original-call-formation-definition.md
4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e notes/design/2026-10-07-complete-call-contribution-definition.md
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c notes/design/2026-10-08-call-source-interface-definition.md
278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98 notes/theory/2026-10-08-call-source-interface-construction.md
ead206bff341c82993acbaecda25ae1d3a760397796bbbbb53ba3ef917a53fb1 notes/theory/2026-10-07-owned-call-contribution-construction.md
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1 notes/design/2026-10-05-inferred-function-call-views.md
6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7 notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed notes/design/2026-09-29-scc-intrusion-redesign-charter.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81 notes/design/2026-10-11-yulang-inference-top-level-principles.md
6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073 notes/progress/2026-10-06-source-call-generation-construction.md
82fbf7019eb37f8c4506f39953f902530f28a1a7141db1c2501afd40388353df notes/theory/2026-10-15-receiver-entry-source-derived-map.md
547fd989d61791f2e3c91d270ac9aafe53aaca2f451dd03ed68a3d0bd5fc05d6 notes/progress/2026-10-15-receiver-entry-derived-map-falsifier.md
afc91346af535529f973421bdbe2a43520c98946097cae545e4ae1a665146074 crates/yu-hir/src/module/local_source.rs
32a6d875b9e89af8192cf017fbeccc95e9648223490d72de64a6957c97aa6e1b crates/yu-solver/src/candidate_source.rs
cc5778b936a5495182c08d4853ab9ef006d079df5e169dd94df629c2d82f3199 crates/yu-solver/src/candidate_call.rs
831dc28b977a5e01e6f0ef0faa795495d78ecb2cc01678db48e9cf7ea5132eac crates/yu-solver/src/shadow_apply.rs
6301ca80eec137df3f2c2c44e2edaa7dbdf1ed7a78c69617228888e63654e461 crates/yu-solver/src/candidate_context.rs
f414efa7efdb17644f4dfa6b0bba621c1bb7cccd0f83735c33a0acb875da6b91 crates/yu-solver/src/candidate_effect.rs
e902da1c9a7f0fb4dcd806c87563d1ae46d35bbb999e69b7fee51c3c0f6e4bf5 crates/yu-solver/src/lib.rs
dabcbd07b2d1baace0227cb94164db871fdadc1089b1854b396dfb464d26ce95 crates/yu-core/src/shadow_typed_evidence.rs
394c763e5b4e2de6ae692ffacf22c07db8958f00129a47f1332f238c9a8eb5eb crates/yu-core/src/shadow_call_formation.rs
08ecb92d2aebc15a4ae2102b977d24acc34889cea59d1fb6ed16cd7c3c82af7d crates/yu-solver/tests/shadow_candidate_call_formation_crosswalk.rs
```

## Commit packet

- Exact leased/changed path: `notes/theory/2026-10-15-call-native-correspondence-construction.md`.
- Baseline: `b336999a148eaee7779f80e0a18e9e79e2cd8394`.
- Changed dependency hashes: none; all 30 direct inputs matched baseline.
- Honest review status: unreviewed research-only bounded construction and
  obstruction; no theorem, parent gate or production status promotion.
- Checks already run: static constructor/consumer/source inspection, baseline
  dependency equality/SHA-256; final artifact whitespace and lease inspection.
  No executable semantic check.
- Proposed checkpoint message: `research: pin complete Call to native source-record obstruction`.
- Shared-record delta left for primary/curator: selected source complete Call
  and receiver meaning already exists; native static ports/registration/raw
  invocation provenance are retained, while complete original record/operator
  interpretation remains the first unproved bridge. Do not substitute typed
  query assumptions or solver completion for that bridge. Preserve H1/H2/U
  OPEN and H3/P disabled. Shared task/index/theory records were not edited.
