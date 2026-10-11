# `invoke`: direct Build-to-native correspondence attempt

Date: 2026-10-11
Baseline: `67b8119ca22313dc3e8d5ede623ae19dc2a65425`
Status: bounded source/operational characterization and minimized obstruction;
original normal-inference theorem OPEN
Claim class: A/B source correspondence; no theorem closure or counterexample
Authority: existing selected source definitions and the primary's frozen packet
Review: producer-frozen, independent review pending; no self-certification
Exclusive lease: this file only

## 1. Objective, authority and frozen target

Derive the complete source-rule program `Build(S,T)` for the actual resolved
source `my invoke f = f 1` into its implemented native Simple-sub constraints,
without taking `Fam_delta[mu_delta]` or `EmittedGenCall0` as supplied evidence.
The result below does **not** complete that construction. It locates a missing
original local application in the formal-entry construction and traces the actual later scalar
construction and activation owners so that neither can substitute for it.

The governing inference policy is the Authoritative top-level principles
`notes/design/2026-10-11-yulang-inference-top-level-principles.md`, §§1–5 and
Evaluation. Source definitions are selected by
`2026-10-08-source-generalize-definition.md`, §§2–4, specifically its linked
`2026-10-08-source-generalize-definition-and-proof.md`, §§2–6. Its L1–L5
require independently specified complete local declarations and laws;
selection of Generalize does not supply absent local applications.
The six pre-Call API choices in
`2026-10-10-original-registry-constructor-adoption-proposal.md`, §§1–3,
are adopted in their stated fragment. Its §2 explicitly retains actual
declaration correspondence. No compatibility theorem with a separately fixed
foreign registry is added as a premise of this attempt.

Freeze `S` with its actual lambda `L`, unannotated formal `d_f`, resolved Name
`u_f`, literal `a` with payload `1`, and Apply `c`. Retain the actual
`Resolve(u_f,d_f)` and `ArgumentChild(c,a)` edges. Fix the original binder tree
`T` and the original joint `B,X,xi=(nu,K,D)` and lexical/scope maps; these are
the original source coordinates, not newly allocated theorem binders. The
formal's ordinary Desc scope precedes its invocation challenge. Event fields,
body proof choices, Shared and ViewLogic fields remain where their actual
owning rules introduce them. Names below abbreviate projections of those
contexts and do not elaborate any undisplayed telescope.

The required target retains the following quantifier order and conclusions:

1. For this source and its original fixed anchors, construct one complete
   source/native relation and generalized public presentation before selecting
   a client assignment, challenge, history or independently valid public view.
2. Preserve the independent declarative source judgment of Generalize §3 and
   `Build(S,T)` §4 in both directions, on one original-scoped assignment and
   evidence strategy. All original independently admitted whole carriers,
   actual callable decompositions, compatible contexts, finite developments,
   pending/future observations, guards and licensed alternatives stay in scope.
   A source primitive or local constructor retains its genuine L1–L5 laws;
   supplying the desired complete application is not an extra hypothesis here.
3. Generate, accumulate and activate the local Call obligations, including
   whole argument checking, same actual returned provider and its own entry,
   receipt, designated Force/consumer, ordered Bind suffixes, complete result,
   effects/protection, admission and future-provider obligations. Transport
   the same witnesses and residuals through generalization and lawful use.
4. Establish normal progress/termination and source soundness, and supply
   required principality at the actual public export. The principal order is
   the existing `2026-10-07-actual-export-synthesis-round3.md`, §3.1: one
   computed `P_S`; for each independently valid finite public `V`, one ordinary
   map graph fixed before public solutions/challenges/histories; compatible
   original-scoped strategies for all those solutions. Its source-adequacy,
   ALL_VIEW and PROJECTION inputs are not assumed established here.

This freezes a target, not a proved statement. The baseline does not contain
a separate fully elaborated theorem named “normal-inference theorem”; the
packet's required conclusion is read with the existing explicit source and
principal judgments above. No printed `invoke` scheme is postulated.
Exclusions: no source restriction or mandatory annotation; no Value-entry
implies Pure law; no native Term/row/occurrence ID cast to a semantic witness;
no independent marginal witnesses; no collapse of provider, attachment,
license or residual lineage; no replacement of complete Call by scalar success.

## 2. Actual source constructors and exact emitted scalar fragment

All positions in this note refer to the baseline, not a moving worktree.
The reachable private entry is `CandidateInference::solve`
(`shadow_apply.rs:79–114`), with candidate collection and `run_candidate`.
It accepts the retained LocalSource sidecar after its own preflight. This is
not ordinary HIR/default acceptance: ordinary Lambda collection separately
classifies its body in `lib.rs:1047` onward, and private finish explicitly
produces no closed public schemes (`lib.rs:10361–10373`).

`yu-hir/src/module/local_source.rs:257–322` constructs the lambda, retains the
actual parameter source/scope, installs its lexical resolution and places the
body under that parameter. Lines 553–563 retain the actual Apply children;
649–664 retain resolved Name and literal. These are source syntax/incidence
outputs, not a typed complete entry or an admitted whole carrier.

The solver collector (`candidate_source.rs:187–246`) allocates one formal
recipe, retains its lambda/parameter owner, and makes every resolved formal
Name refer to that same `CandidateEndpoint::Parameter`. Registration starts
with `native_root: None`; initialization supplies the actual positive native
parameter row (`:543–559`). It does not register an original semantic root.
The depth-first schedule visits callee, argument, Apply, then Lambda, with
source scope and numeric level retained (`:254–286,330–350,369–380,394–411,
445–459`). It executes the actual fact/Apply/Lambda/link owners at `:660–671`.

Let `alpha` denote the actual parameter value row; `s` the literal value row;
`beta` the Apply result value row; `ae`, `ce`, `re` the literal, Name and Apply
evaluation effect rows. Let `e` be the Apply's fresh invocation effect row.
Let `i` and `j` be the Lambda's fresh entry and complete invocation effect
rows, `l` its construction evaluation effect, `v_L` its value component, and
`r` the definition root. These names denote native rows only.

The current LocalSource path emits/submits these source-owned constraints:

```text
literal a:  Int+ <= s-; s+ <= Int-
            BottomEffect+ <= ae-; ae+ <= EmptyEffect-
Name u_f:   BottomEffect+ <= ce-; ce+ <= EmptyEffect-
Apply c:    alpha+ <= NegativeFunction(s+, ae+, e-, beta-)
            ce+ <= re-; e+ <= re-
Lambda L:   BottomEffect+ <= l-; l+ <= EmptyEffect-
            i+ <= j-; re+ <= j-
            PositiveFunction(alpha-, i-, j+, beta+) <= v_L-
root link:  v_L+ <= r-
```

Literal bounds come from `candidate_source.rs:336–350`; Name purity from
`:369–380`. The Apply owner is `shadow_apply.rs:1304–1443`: it validates the
retained source input, allocates `e` at the application effect row's level,
forms the negative four-port Function, stores `NativeInterface`, admits
provenance and invokes `constrain_live_value`; both effect links separately
invoke `constrain_live_effect` (`:1446–1468`). Lambda purity is collected at
`:978–987`; the Lambda admission owner (`lib.rs:11233–11369`) now allocates
`i,j`, submits both effect links, retains an inferred-entry origin, and
submits its positive Function. The root link is collected at
`candidate_source.rs:492–498` and executed at `:665–668`.

The current Lambda ports are **not** the historical fixed empty-argument-effect
ports displayed in `2026-10-10-candidate-graph-call-correspondence.md`, §2.2.
That reviewed note supplies its bounded historical result, not permission to
use its old exact Lambda equation at this newer baseline. The equations above
are read directly from the current owning constructors.

`term.rs:1126–1182` checks the four child kinds/polarities: positive Function
`[V-,E-,E+,V+]`, negative Function `[V+,E+,E-,V-]`. This establishes the native
sorts and source incidence. It supplies no complete semantic Function
descriptor, original entry telescope or provider membership.

## 3. Accumulation, actual activation, and lifecycle coverage

`lib.rs:11945–11955` selects the candidate typed drain. For a row/structure
inequality, dispatch calls the candidate extrusion and bound owner
(`:12407–12490`, `candidate_extrusion.rs:808–837`). Thus the Apply demand is
inserted as an exact upper of `alpha`, with physical bound/evidence ownership;
it is not eagerly solved or discarded for lack of a provider.

When the opposite lower is present, `candidate_replay_bound`
(`candidate_extrusion.rs:763–804`) enumerates the actual opposite bound list,
constructs the pair from the inserted and existing bound at the same row,
records its replay relation and drives the child. This also operates when a
later lower arrives: the owner inserts it and replays the retained upper.
Fresh-use restoration has a saved count, actual emission, replay completion
and live canonical index (`:697–760`), rather than treating storage alone as
execution. These are actual native consumers; their evidence is not a source
Call witness.

For an actual native positive Function lower with ports `(A-,AE-,RE+,R+)`
reaching the retained negative demand, `dispatch_live_item`
(`lib.rs:12493–12541`) constructs exactly:

```text
s+ <= A-       ae+ <= AE-       RE+ <= e-       R+ <= beta-
```

The candidate Function dispatch (`:12643–12666`) admits then enqueues each of
the four children. `candidate_function_port_admit`
(`candidate_context.rs:2557–2608`) retains a dependency to the same parent,
swapping its context on Argument/ArgumentEffect and preserving it on
ResultEffect/Result. The typed drain then transports, checks context and
dispatches those work items, and processes completion/acknowledgements
(`lib.rs:12207–12310`). There is no branch that reduces this pair to a value
port alone. This traces native activation from actual owners, rather than
postulating transitions in a checker.

The bare source has no provider lower for `alpha`. It therefore retains the
latent demand; it does **not** execute all four children or a runtime Call at
definition time. The above activation trace is conditional on an actual
native lower arriving and successful processing. Existing tests inspect real
provider arrival for the extended source `invoke id`
(`tests/candidate_graph_call.rs:334–361`); they were read, not rerun, and are
not a counterexample or a complete semantic bridge for the frozen source.

For this one nonrecursive source, all source components and formal rows start
at level one (`lib.rs:10048–10103`; `candidate_source.rs:254–286,532–542`).
Lambda and Apply fresh effect rows use those actual levels. No local
initializer raises a level. Candidate extrusion preserves a row whose level
is no greater than the receiving target (`candidate_extrusion.rs:90–94`);
only a genuinely younger row creates a polarity copy/parent (`:112–123`).
Consequently this source creates no extrusion parent. Intrusion still has an
actual consumer, but its empty-parent branch returns without equality
(`candidate_intrusion.rs:358–372`); qualifying parent/copy equality requires
the same actual dependency SCC (`:477–486`). No intrusion case is invented
for this source.

The actual SCC owner executes the source schedule before capture and stages
every member graph (`candidate_scheme.rs:842–917`). Capture uses boundary zero,
retains actual local-row bounds, orientation and evidence (`:301–324,567–635`).
Use-time recapture is at `:947–963`; one canonical row map is allocated before
bound reconstruction (`:1008–1019`); every retained bound goes through physical
restoration and its transported relation/evidence (`:965–976,1221–1266`).
The receiving root route follows replay (`:1268–1303`). These owners explain
native bound sharing/transport; they do not implement the full Desc/Shared/
ViewLogic/EventProof closure of source Generalize. Public graph export rejects
recorded conflicts (`shadow_apply.rs:123–130`) but publishes no complete public
scheme or independently validated Call relation.

## 4. Formal Entry-Value dependency gap

`Build(S,T)` §4 is not defined to emit only these inequalities. It recurses
through every original source rule, conjoins its complete local relation and
evidence clause and retains every actual binder/owner. To derive its Lambda
body, the original lexical telescope must first be formed by the actual
formal entry. Empty captures and the unannotated Value role/Desc are available;
the complete entry is not derived from them.

The actual original consumer is Entry-Value in
`2026-10-07-call-input-construction-proof.md`, §3.2:

```text
Capture(E,L,E_cap;edges), ParameterOrigin(L,d_f,Value(A_f),r_f),
original received-carrier port and designated entry view,
original receipt/rebind ports
--------------------------------------------------------- Entry-Value
Entry(L,Value(A_f),E_cap,E_body;
      Receive; Receipt_L; Force_entry; Rebind)
E_body = ValueBind(E_cap,d_f,r_f,A_f,that entry/rebind origin)
```

Here `r_f` is an original typed root, not the native row `alpha`. This complete
Value-entry application is required to derive the body Name rule at the actual
`d_f`. Its `ParameterOrigin` and complete port declarations, with their actual
ordered parameter/scope/license maps, have no established supplier in the
inspected construction cone. This locates a missing dependency in the formal
entry; it does **not** establish that Entry-Value is the earliest unavailable
original application. The displayed premises do not expose the complete
dependent introduction signatures for `ParameterOrigin` or the ports, and
their relative introduction order is unresolved. No hidden parameter or first
hidden field is invented here.

In the adopted interpretation, `Header-Parameter` supplies the source header,
Value role, Desc and intrinsic root. Its `Declare-Owned-Port` and
`Assemble-Value-Entry` rules in
`2026-10-10-source-owned-original-registry-construction.md`, §4.1, explicitly
consume complete local declaration applications and scope maps. Adoption §2
requires these applications to be furnished at their actual binders. The
baseline's `FormalRegistrationInput` contains owner, lambda, parameter,
recipe position and native root (`candidate_call.rs:16–22`); it has none of
the complete entry declarations. The later inferred-entry origin retains
Lambda/native effect incidence (`lib.rs:11286–11302`), not Receive/Receipt/
Force/Rebind formation. Neither object discharges Entry-Value's premises.

Entry-Value's conclusion occurs before the body Name rule in the **original
source derivation**, because that rule resolves a binding in `E_body`. The
lexical HIR Name can resolve without this typed telescope, and the native
collector can use `alpha` without it; hence the Apply demand exists despite
the missing source-derivation dependency. Code order and source semantic
premise order are different here. Removing the literal and Apply leaves the
same formal-entry dependency gap; it is not an Int-special-case or a
provider-arrival failure.

Minimum next evidence: supply the complete actual `FormalOwner-Ports` and
ordinary Value-entry introduction chain at this selected source interpretation,
including the origin, received-carrier, receipt, designated one-layer Force,
Rebind and all original dependent scope/license fields. Give the actual
introduction dependency order, each complete ordered application at `d_f`,
and its precise native generation/consumer interpretation. If those
declarations already exist elsewhere, return their exact owner and full
applications.
If they are genuinely absent, the primary must resolve the missing original
local definition through its existing authority path. Another registry layer,
an assumed completed port package or a synthetic telescope does not supply it.

## 5. Packaging necessity and the later Call cut

`Fam_delta[mu_delta]` is notation for a whole local declaration application
in the adopted recipe API, not a new semantic premise required merely by
the original normal-inference statement. A direct native proof could dispense
with that notation and its separate raw-registry representation layer if it
established the same complete original local rule and lawful consumers. The
required whole declaration and ordered application cannot be dispensed with.
Within the **currently adopted** owner API, Declare-Owned-Port is the available
constructor for this fragment and it still takes that application. Neither
necessity of this particular representation nor an alternative complete
native supplier has been proved. No selected API choice is withdrawn here.

Likewise the particular wrapper name `EmittedGenCall0` is not necessary for
every original Call: `2026-10-07-original-call-formation-definition.md`, §1,
explicitly leaves Calls without that record with their old child derivations.
Its adopted OSig-Demand/OC-CallEff route (§§2–4) nevertheless operates only on
actual complete emitted records. A native four-port Term is not such a record.

The stronger original Code-Call consumer
(`2026-10-07-call-input-construction-proof.md`, §3.4) independently requires
the actual complete Application origin, child Code derivations, Call-owned
Reify origin and whole argument carrier, VIncl origin for the same callee,
WholeArgCompatible origin at the whole carrier image, complete result port
and the actual provider's ordered suffix schema. It explicitly says that bare
Gen-Call-0 does not manufacture these additional origins. `Build` must retain
these original clauses even if an alternative presentation avoids that wrapper.

The native `ApplySourceInput`/`NativeInterface` are not those clauses;
`pending_construction().suppliers()` still lists original registration,
formal/exposure, Gen-Call-0, Reify/whole carrier and receiver/complete-result/
future interfaces (`candidate_call.rs:81–128,224–244`). This enum is evidence
of the API boundary, not itself a proof that no supplier can ever exist.
The inspected actual emitter stores only the source/native operands traced
in §2. Selected contextual Function membership (§§2–3) can eliminate a
**genuine** complete checked challenge to the same actual provider's acceptance
and observations; scalar Int/effect bounds do not form that challenge.
Selected complete Call contributions (§§2–4) still require authentic whole
operation and independent C0. Selected q2 Reify direction still requires
the actual child/registry/catalogue inputs and keeps `J_lit` distinct from
old `J`. These later obligations are not closed or made the first cut.

## 6. Proof economy, checks, limitations and frozen handoff

Two routes were examined: direct original Build/Entry-Value formation, and
the actual native collector/drain/replay route. Both leave the complete local
entry application untouched. Economy audit under `compiler-engineering.md`,
Natural compiler behavior and proof-obligation economy: this is A/B, needed
for original soundness and intended ordinary inference. It is not optional C.
No owning compiler phase in this inspected cone first constructs and then
discards the complete semantic entry, so calling it D would invent evidence.
The header, native root and inferred effect origin are retained; preserving
them alone cannot recover an unprovided whole local law. Stop this packet at
its owner rather than attempt a third equivalent representation proof.

No complete Build-to-native construction or source-qualified counterexample
was obtained. Missing declarations/consumers do not prove source rejection,
incompatibility or impossibility. The parent remains OPEN. No source soundness,
complete Call, effect hygiene, public principality or full termination theorem
is inferred from the operational trace. Its scalar activation trace assumes
actual native opposite-bound arrival and successful processing; it does not
prove all original providers lower into native Functions. Abnormal semantic
reflection, all compatible future clients and public extraction remain unproved.

Checks: baseline `git show <SHA>:<path>` and `git grep`/`git ls-tree` for
bounded locators; numbered source slices via `nl`/`sed`; lease absence checked
with `test ! -e` before writing. Read the prescribed orchestration/research/
authority/compiler/Git rules, role registration and prover config, current
task/handoff and design index. Thirty direct authority/source dependencies
were compared byte-for-byte with baseline blobs using a sequential Python
SHA-256 audit: all matched. Some broad output captures truncated; decisive
rule and source portions were reread in bounded slices. No repository-wide
absence census is claimed. Existing tests were inspected only. Zero builds,
tests, Oracle runs, probes, measurements, child launches or Git mutations.

Runtime: assigned leaf `/root/invoke_build_simple_sub_proof`, role `prover`;
requested `gpt-6.1-sol` / `high`. Config declares that default and no prover
model/effort pins; effective runtime model/effort metadata is unavailable
(unknown). No Astra override or reload claimed. Budget: one bounded leaf,
30 minutes wall time; first recorded clock 04:19:57 UTC, dependency audit
04:24:00 UTC. CPU/RAM were not measured; only lightweight read/hash/write
commands ran. No shared verification process was started.

Next action: primary obtain/elaborate the actual complete ordinary formal
Value-entry declaration/application at `d_f`, then assign its original-to-native
local generation/consumer proof. Keep the later Code-Call, semantic and public
gates OPEN; do not request another conditional registry-packaging lemma.

### Commit packet

- Exact leased path: `notes/theory/2026-10-11-invoke-build-to-simple-sub-proof.md`.
- Baseline: `67b8119ca22313dc3e8d5ede623ae19dc2a65425`.
- Changed dependency hashes: none in the 30-path pre-write comparison;
  integration owner must recheck its frozen dependency snapshot.
- Review: unreviewed research-only obstruction/operational trace; independent
  review pending; no closure certification, production conformance or authority.
- Checks already run: pinned rule/source/test reads, lease absence and 30-path
  byte/hash audit; no test/build/probe or performance check.
- Proposed research-checkpoint message:
  `research: locate invoke Build-to-native formal entry obstruction`.
- Shared-record deltas left for primary/curator: link this direct source-rule
  cut from `tasks/current.md` and relevant theory navigation; distinguish
  dispensable wrapper notation from required complete local entry/Call laws;
  preserve parent normal-inference/Call/source/principal gates OPEN. No shared
  task, index, theory-status, question, compiler or configuration file changed.
