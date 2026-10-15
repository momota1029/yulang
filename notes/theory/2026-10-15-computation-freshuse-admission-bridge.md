# Computation forwarding: native FreshUse admission bridge

Date: 2026-10-15. Status: independently reviewed research derivation; bounded
source-to-physical-admission result, with the original general bridge OPEN.
Baseline: `13a8e36eb595e97b5667230c7463fdb09aed67b8`.
Branch: `research/simple-sub-intrusion`. Exclusive lease: this file only.

Independent review: `compiler_referee` freshuse_bridge_review reviewed frozen
SHA-256 `9bc051f7d0c88b5fbff5ba77cc3842b2316d22a874a92a6b4df5d2d668333859`
against the pinned baseline with no findings. Closure is the isolated first-use
physical-admission supplier and its conditional scalar implication. General
copied/merged providers, later recapture, dynamic evidence and global soundness
remain OPEN. This status paragraph adds no proof premise or broader claim.

## Frozen objective, quantifiers, and exclusions

The parent is [forwarding preservation](2026-10-15-computation-forwarding-preservation.md)
§§6–7: for every successfully captured/freshened native direct-Name
Computation-formal provider in the original source fragment, establish ONE
authentic use map carrying the original registration/Name/body edges
`e_t <= e_n <= e_R` and `e_n <= e_t` into the actual compared provider,
and the real Function/Apply consumers giving `e_A <= e_out`. A stored edge,
queued child, completed replay, and successful source execution are different
facts. Original source declarations, formal binders, scopes, providers,
attachments, witnesses, and residual lineages remain fixed. The whole-language
hygiene/soundness/principality/complete-Call parent remains OPEN.

This pass establishes a source-generated subcase, rather than assuming the
mapped inequalities. Fix a finite resolved source module with an ordinary
unannotated binding whose initializer is exactly
`Lambda(t : [S] Int, Name(Parameter(t)))`, for finite concrete resolved S,
without a symbolic row variable. It may be a top-level definition or a local
initializer, and its first incoming/local use occurs after its initializer
finishes. For the bounded result, before that capture there is no other use,
assignment, recursive reference, enclosing ascription, or transport of this
binding's value; no earlier failed attempt or retained extrusion parent can
mutate its private constructor closure. These are the source/history bounds
of this lemma, not proposed language restrictions. The actual argument at the
use may carry additional effects; S is not an incoming cap.

Quantify over every finite successful native constructor/freshening execution
of this subcase, at arbitrary initializer level l and actual use level k.
No Graph, row map, mapped bound, replay child, permission profile or satisfying
typing is supplied as a premise. Successful formation and finite completion
are conditional execution hypotheses, not claims of availability, termination,
conflict freedom, or accepted publication. The conclusion concerns actual
physical mapped admission and subsequent scalar constraint implication, not
execution of every effect or realization of dynamic protection/receipt/Force.

The concrete ordinary source shape is already present in the reviewed
[permission construction](2026-10-15-computation-formal-permission-construction.md)
§1: `my bridge (thunk:[io] int) = thunk`. That prior artifact supplies an
authentic source example and its original registration; it is not used as
evidence that this pass executed the compiler. Local binding formation is
covered at its actual source schedule below. General higher-order escape,
already copied/merged providers, symbolic formal effects, binding annotations,
recursion, and later recapture after arbitrary uses remain outside this bounded
derivation and inside the original obligation.

Authority: top-level inference principles §§1–5 and Authority and integration;
the selected ordinary unhandled-effect forwarding decision; the cited parent
§§6–7. Workflow: agent-orchestration Model routing / Proof delegation;
research-lab Evidence quality; compiler-engineering proof-obligation economy;
git-concurrency disjoint-file mode. No new semantics or implementation decision
is adopted. Method: direct generation/level/storage/capture/restoration/consumer
trace, followed by a separate signed-copy attempt for the remaining parent.

## 1. Original source construction gives a reachable local edge closure

`candidate_source.rs:566–578` registers the original parameter/Lambda and
selects Computation from the outer effect annotation. At `:651–724`, ordinary
source traversal assigns the Lambda parameter and its direct Name body the
same level l: visiting a Lambda does not increment its body's level. A Block
initializer is visited at its parent level plus one (`:725–731,782–794`),
and its Install saves the parent level as generalization boundary
(`:795–815`). A top-level root and its body start at level one
(`lib.rs:10078–10135`, `candidate_source.rs:651`). Therefore l is above the
capture boundary (0 for a definition, l−1 for this local initializer).

Initialization (`candidate_source.rs:1164–1199`) allocates the registration's
e_t at the parameter level l. Name action construction (`:912–923`) uses the
original resolved Parameter(t); execution (`:1304–1307`) selects that same
registration. `candidate_effect.rs:1157–1167` admits and synchronously constrains
both directions `e_t <= e_n`, `e_n <= e_t`. Lambda slot 4
(`lib.rs:11300–11381`) allocates e_R at parameter level l and admits/constrains
`e_n <= e_R`. Slot 3 is absent for this Computation formal. Formal Int checking
retains `Int+ <= v_t <= Int-` (`candidate_effect.rs:1185–1230`); it does not
replace the returned v_t by an unrelated Int leaf or cap e_t by S.

These are actual source actions, not only retained store facts. Candidate
`constrain_live_item_with_inferred_entry` enters `run_candidate_typed_drain`
(`lib.rs:12026–12038,12239–12261`); its steps reach dispatch before successful
return. For the three effect-row constraints the source context is identity:
`candidate_context_source` only creates a nonidentity prefix for an Allowance
upper (`candidate_context.rs:2864–2871`); these uppers are rows. The scoped
Call-site special cases in `candidate_context_seed` do not apply to this Name
or Lambda occurrence (`:2872–2938`). Thus they are not consumed as checks.

Equal levels choose the first row/row branch of `candidate_apply_effect`
(`candidate_extrusion.rs:876–900`), physically storing direct uppers:

```text
e_t.direct_upper_rows contains e_n
e_n.direct_upper_rows contains e_t and e_R.
```

Insertion is explicit at `:442–620`; it retains an admission, pushes its
physical slot and emits the evidence record. Function formation and linking
its positive constructor to the initializer/root row use level l on both
sides, so structural extrusion stops at its rows (`:90–94`) without producing
parent/copy pairs. In this isolated first-construction closure no prior parent
is available for intrusion to merge. This derives the untouched local closure
needed below from this source/history subcase. It is not an assumption that
arbitrary native rows remain local forever.

The source schedule finishes those actions before publishing the local scheme
(`candidate_source.rs:1250–1295`), or before SCC member capture/publication
(`candidate_scheme.rs:904–1005`). This establishes original execution before
capture, separately from fresh execution.

## 2. Capture reaches the actual Name edges from the provider

Capture starts from the authentic live root (`candidate_scheme.rs:766–806`).
The local root's exact positive Function lower is included by `expand_row`
(`:604–660`). Function expansion interns all four real children, including
negative AE=e_t and positive RE=e_R (`:499–553`). `row` marks e_t local from
the derived level l above boundary and unchanged nongeneric metadata
(`:314–339`); fresh/collected construction initializes non_generic=false.

Expanding e_t's direct uppers captures e_t<=e_n, interning e_n. Expanding the
newly reachable e_n captures e_n<=e_t and e_n<=e_R
(`:662–706`). The outer pending/row loop continues until all added rows and
endpoints are expanded (`:803–837`). No inverse search from RE, assumed graph
connectivity, or independently selected Name witness is needed. Captured
`Bound` contains the original `source_bound`, side, endpoints, original relation
and evidence snapshot (`:557–602`). Deduplication can coalesce identical
endpoint/relation records; it cannot remove the existence of each of these
three directed edges. This conclusion is record coverage, not all physical
admission multiplicity or general opposite-incidence coverage.

## 3. ONE map physically restores all three edges before root publication

Both actual DefinitionUse and LocalUse immediately recapture their live scheme
root (`:1017–1038,1468–1495`). `prepare_candidate_fresh_use` creates one use
identity, rows vector, canonical_rows memo and terms vector (`:1057–1103`).
Each local source representative gets one fresh row at k; all occurrences
reuse that entry. Structural Function reconstruction reads precisely those
same rows/terms (`:1189–1242`). Let mu be this actual map. The provider's AE
is mu(e_t), its RE is mu(e_R), and both captured occurrences of e_n use
mu(e_n). There is no comparison to the original e_t here.

`begin_candidate_fresh_bound` reads those same tables and retains original
orientation, source BoundKey, antecedent snapshot, mapped relation and common
use origin (`:1333–1379`). It calls `candidate_begin_bound_restoration`, which
physically inserts the mapped bound BEFORE retaining a restoration handle
(`candidate_extrusion.rs:695–714`). Hence the actual mapped storage contains

```text
mu(e_t) <= mu(e_n), mu(e_n) <= mu(e_t), mu(e_n) <= mu(e_R).
```

This is the missing mapped-admission premise derived for this subcase. It is
not inferred from success or the mere existence of a ReplayOperationId.

The DefinitionUse loop drives every captured bound restoration before returning
the root (`candidate_scheme.rs:1040–1054`), then routes and retains it
(`:1381–1427`). LocalUse retains one FreshUse and advances next_bound only
after the current restoration completes; only after all bounds does it link
the root and set complete (`:1616–1653`). Production local routing has no
injected pause. These orderings exclude exposing this use's root before its
three mapped bounds are inserted/restored.

## 4. Recorded, queued, drained, and consumed remain distinct

Insertion above does not assert that the same scalar edge is separately
enqueued as a typed task. A restoration with no opposite bounds retires with
zero children. A restoration with saved count N selects current canonical
opposites sequentially; every selected replay is fully driven with provenance
before advancing (`candidate_extrusion.rs:717–802`). A queued child alone is
insufficient: `candidate_context_drive_replay` with provenance reports an error
unless owned child consumption completes (`candidate_context.rs:3547–3611`).
Typed terminal return follows diagnostics and acknowledgement delivery
(`lib.rs:12667–12744`). Therefore successful restoration gives completion of
the children it actually selected; it does not prove that live indexing selected
every historical physical incidence in arbitrary shared/merged cases.

In the displayed closure the three restored effect edges are direct uppers.
An actual later contribution/lower bound meeting one of them activates its
ordinary replay; the next edge remains physically present for the next meet.
Until such a meet, latent inclusion is retained rather than solved eagerly.
This scalar implication requires no claim that an unused argument executes.
General contextual residual replay is not supplied by these row inclusions.

Actual Function dispatch (`lib.rs:12591–12633,12747–12782`) creates all four
port tasks with contravariant argument/AE and covariant result/RE. It admits
each port's relation before enqueue. Effect dispatch admits evidence before a
current-pair cache return (`:12417–12432`); `pair_is_current` requires the
processing relation's current intrusion generation (`:11542–11553`). Cache
reuse does not skip FreshUse's preceding physical bound insertion. This proves
the relevant control order; validity of all possible cache generations and
contextual dispositions remains part of the original parent.

When the compared Function is the freshly reconstructed provider (as in this
untransported use seam), its actual AE/RE port tasks are
`e_A <= mu(e_t)` and `mu(e_R) <= e_C`. The use row and fresh provider rows
are at k here, so linking this provider to that row needs no further polar
copy. `shadow_apply.rs:1541–1572,1652–1670` takes the whole actual argument
effect as demand AE and admits `e_C <= e_out`. Thus in every satisfying
interpretation of THESE actually admitted scalar constraints,

```text
e_A <= mu(e_t) <= mu(e_n) <= mu(e_R) <= e_C <= e_out.
```

No global solver soundness, complete Call denotation, arbitrary-model native
adequacy or principality is inferred from that constraint implication.

## 5. Remaining parent seam and second method

The second route follows actual signed extrusion instead of assuming that
the compared provider is this untransported source Function.
`candidate_extrusion.rs:5–12,90–170,225–267,334–382` memoizes by
`(endpoint, polarity, target level)`. Positive Function copying visits AE
negatively and RE positively; selected bounds follow that same polarity.
Consequently a FreshUse rows map over the CAPTURED graph is not by itself
one map from the ORIGINAL registration/Name graph to the ultimately compared
Function. The original template lemma cannot simply substitute the captured
provider's four fields into all original Name bounds.

The precise missing premise is: for each source-qualified copied/merged
provider that can actually reach comparison, the signed parent/copy links,
selected copied bounds, qualifying intrusion equalities and subsequent capture
jointly retain an AE-to-body-to-RE scalar route for that SAME original provider
and use; each required nonidentity check/replay has its actual disposition.
Owners: `candidate_extrude`/`candidate_insert_copied_bound`,
`candidate_intrusion::finish_candidate_extrusion` and settlement/merge,
then `Capture::expand_row` and the consumers above. The original-to-captured
provider correspondence must precede application of the FreshUse map.

No source-qualified successful missing-edge trace was constructed. The signed
copy observation is an obstruction to this proof shortcut, not a counterexample
to native inference and not evidence that those copies are reachable in every
direct-Name source. Broader recapture/shared-row/merge and failure-reuse claims
are unverified. No compiler repair is justified by this pass alone.

Proof-obligation-economy audit before another equivalent attempt: this route is
A/B for ordinary preservation and natural forwarding, with a D component if
the exact original-provider/copy correspondence is later reconstructed from
shape. The constructor already retains signed parent occurrences and bound
transport causes. First consume those existing records to prove or refute the
joint route; do not add a second registry or restriction. If their original
provider association is genuinely absent, propose retaining it at extrusion's
existing phase output, after independent adjudication. This audit changes no
parent status and is not proof progress by itself.

One next action: source-qualify the first direct-Name provider that undergoes a
nontrivial polar copy, then derive its joint AE/body/RE route from those exact
existing parent/copy and copied-bound records. A successful missing route is
the falsifier for an authorized owning implementer repair; otherwise the
derived correspondence extends this lemma without another assumed-map proof.

## 6. Failure boundary, evidence, and commit packet

All conclusions above require the particular operation to finish successfully.
Errors propagate before returning the fresh root or setting LocalUse complete;
incoming/local operations run in route transactions
(`lib.rs:16572–16589`, `candidate_scheme.rs:1468–1478`). Source synchronous
execution drops its source frame on error (`candidate_source.rs:1208–1218`).
These establish the local return/publication barriers, not a fresh proof that
every failed transaction restores all semantic owners or that arbitrary failed
state is safe to retry. No full restoration requirement is introduced.

Requested runtime: `gpt-6.1-sol` / high. Observed model/effort metadata: unknown.
The actual prover file omits pins; config declares Sol/high agent defaults.
No Astra, nested agent, hot reload, executable probe, test, build, benchmark or
Git mutation was used. One static proof pass used two distinct methods; only
this note was written. Primary remains verification/integration/review owner.
Producer handoff status was unreviewed; independent closure is recorded above.

Read checks: `rg`/`sed`/`cat` on the named source owners and governing records;
`git rev-parse HEAD`, `git branch --show-current`, narrow `git status`, and
SHA-256 dependency capture. No compiler execution. Resource use: sequential
lightweight read/hash processes; zero heavy processes or measurement samples.
The bounded pass does not establish parser acceptance for a new example,
arbitrary source reachability of signed copies, full replay coverage, dynamic
owner/path transport, runtime behavior, soundness, required principality or F5.

Commit packet: exact leased path
`notes/theory/2026-10-15-computation-freshuse-admission-bridge.md`;
baseline as above; no changed input dependency detected at capture. Proposed
checkpoint message: `research: derive direct computation FreshUse admission bridge`.
Primary/curator deltas: record this bounded physical-admission supplier; retain
the original general mapped-admission/copy bridge OPEN with the exact owner in
§5; the required fresh independent proof review is now recorded above.
No task/index/theory-status record was edited here.

Frozen direct dependency SHA-256:

```text
b0f7778934a37ec9c642f7e6232cb61e37a1b0768f6af92556cf873f6b2a69f7  crates/yu-solver/src/lib.rs
90db34173d366ed826b34492da0fb2f1c5422b1b41e43fcda14892ec8415e7ab  crates/yu-solver/src/candidate_source.rs
deee5a0892b02bc9ee23a1f2a35c76175094c558ed7dfb2cf55a7e115ac54225  crates/yu-solver/src/candidate_effect.rs
436687cbc8c4ea372d0066f3f8a8e46cfc28223ade163f49864cd3c5039c60e6  crates/yu-solver/src/candidate_scheme.rs
2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b  crates/yu-solver/src/candidate_extrusion.rs
9f71c8c40d6850bffccb27d7393bf6219f0ceca5cf1fe1e738073ea943706083  crates/yu-solver/src/candidate_context.rs
2158e7377686189ed90d8b8d8803dbb446368abb52b7e0cb24b2282ebe41007c  crates/yu-solver/src/candidate_intrusion.rs
28112e3a8b04bff3abbed0bf7496a4e49300384e7e943ee8a71f4eff3a100294  crates/yu-solver/src/shadow_apply.rs
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md
7766aff08cedde1ebc796b8927cd1d44f459df72a632e0c0d35d4bfcd28d335e  notes/theory/2026-10-15-computation-formal-permission-construction.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
c544ed3c7b83686a740aa43b1db92d901de31a3b197f81f90a4c9dbdae561134  notes/design/2026-10-15-callback-identity-forwarding.md
```
