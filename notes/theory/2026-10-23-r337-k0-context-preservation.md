# R337 — ordinary K0 context preservation

Status: **source-based proof candidate, awaiting independent review**. Author:
`/root/r337_k0_context_prover`; no coauthors or descendants. This is a finite
successful-prefix induction over the pinned implementation, not an execution
probe or a proof of native solution preservation, termination, or full A/B.

## Parent, inputs and claim

The original parent is the unchanged full Yulang2/Simple-sub source/native A/B
objective. This packet supplies exactly the ordinary context/metadata premise
left OPEN by the R336 review. The source domain is the existing `ValidK0` of
R336 revision 4, including its authentic HIR membership, ordinary mode, empty
outer environment, single nonrecursive definition, and excluded source forms.
No additional source restriction is introduced here.

Frozen sprint contract:
`tasks/agent-loop/sprints/r337-k0-context-lifecycle-20261023.md`, SHA-256
`0d71e3c740aa3d48667e3a9d62d15b835084a432e394fe79cc30d2b9d4cc9a3e`.
R336 closeout commit: `cca4ec6e530917f2e6dbc492c747ce8a2f79e9d4`.
Compiler baseline: `17e57af2c4605d7084c7d76792b115674776bbe2`.
R336 revision-4 note SHA-256:
`4bcbe71ec9f2372baca884e3db737c16fc19ad2a51103965ade5ca4c2ecf4973`.
R336 independent review SHA-256:
`d03b7a23bcec2bd0575bf391342f92353b46b840cbcfa70deea7500786fd892e`.
The user's audit SHA-256 is
`b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`;
its sections 4.1–4.5 and G/D1 are the governing proof target.

Write `I=ContextId(0)` and `F0=ScopedFlow { transformer:0, demand:None }`.
For every finite reachable successful construction prefix of authentic
ordinary `ValidK0(s)`, the candidate theorem is:

1. `scoped_enabled=false` and every retained relation has scoped flow `F0`.
2. No source pair or subsequently generated pair/bound contains an Allowance
   endpoint. In particular no closed Allowance supplies a source context.
3. Every retained relation's context and its `post_check_context` are `I`;
   context execution creates no discharge or nonidentity residual.
4. The actual source, admission, bound, rewrite, decomposition, replay,
   canonicalization and transport transitions preserve these properties.

“Successful prefix” does not assert whole-solver success or exclude cyclic
bounds. It includes completed successful constructor/driver steps, their
intermediate publications, and ordinary diagnostics steps that continue after
a recorded value incompatibility. It makes no publication claim about a
resource-failed private attempt. No fair schedule, saturation, model existence,
or runtime termination premise is used.

## Strengthening needed for a noncircular induction

Define the native effect endpoint carrier

```text
E0 = { EffectRow(r) | r is an allocated Effect row }
     ∪ { BottomPositive, EmptyNegative }.
```

The joint invariant `J` also tracks:

- every Effect position in a collected/live Function term, work item,
  retained relation, bound, origin pair, or captured K0 graph comes from `E0`;
- the live effect algebra has no views, contributions or capture-incidence
  records, and the context state has no weights or nonidentity context nodes;
- the context state has no nondefault scoped-flow/transformer entries,
  discharge entries/residuals, or active `checking_filters`;
- processing handles, typed-drain children, replay children, and bound
  attachments, whenever present, refer to existing relations satisfying `J`.

The carrier restriction is a statement about native constructors, not about
semantic valuations. An Effect row can still receive any finite symbolic
subset of the R336 universe Ω consistent with its inequalities. In particular
this proof does not replace arbitrary latent entry/return effects by ∅.

We prove `J` jointly by induction on the actual sequence of successful native
mutations/source actions. The support-carrier and empty-view conjuncts justify
source identity; source identity and default flow justify all relation
constructors; identity execution prevents discharge from breaking the next
step. Thus no conjunct is assumed merely because it is the desired result.

## Base and authentic source reachability

`CandidateInference::solve` selects `solve_mode(hir,false,false)`
(`shadow_apply.rs:1584–1585`), and the ordinary collector keeps candidate
Values and graph Effects enabled (`1823–1824`). The plan retains the mode bits
(`lib.rs:1016–1020`). `start_candidate_graph` starts a fresh default
`GraphState`, initializes only the effect brand, and copies the scoped bit
(`candidate_scheme.rs:2263–2288`; `candidate_effect.rs:303–313`). Therefore
views, contributions, contexts, weights, flows, filters and discharges start
empty, and `scoped_enabled` is false. In the inspected production owners its
only assignment is this startup copy.

The authentic collector admits the following K0 action family:

| Source form | Actions/native constructors relevant to `J` |
| --- | --- |
| Unit/Bool/Integer/String literal | `Fact`: base Value atoms, Effect-bottom/empty and expression rows |
| Parameter Name | exact formal endpoint; pure Name Effect facts; no `Module` or `Local` use |
| Simple annotation-free Value Lambda | `BeginLambda`, child actions, `Lambda`, `EndLambda`; two fresh Effect rows, positive four-port Function, pure creation facts |
| Apply | child actions and `Candidate(Apply)`; one fresh invocation row, negative Function, and Effect-row inclusions |
| Else-complete If | child actions, Boolean demand, branch Value and Effect inclusions |
| Group | child actions and `Candidate(Group)` Value/Effect inclusions |
| Binding-free Block/StatementBlock | child/prefix actions, final Group and prefix Effect inclusions |
| Definition output | `Link` from semantic body endpoint to root Value row |

Source evidence is `candidate_source.rs:1094–1114,1131–1137,1280–1369,
1558–1573,1632–1655,1724–1755,1824–1827,2038–2098,2164–2165`, and the
action consumers at `2425–2473`. Parameter annotations, unit/record patterns,
local bindings, nonparameter Names, operations, primitives, ascriptions,
where clauses and other excluded forms are exactly the branches that would
add the other actions. Annotation-free formals are registered as Value;
`FormalEntry` is nested under an actual annotation, and `FormalNameEffect`
requires Computation role. `BeginLambda`/`EndLambda` change only the lambda
depth. The omitted-formal and directional-introduction records are inert
source/native evidence; they do not execute a scoped demand.

The Lambda constructor (`lib.rs:11557–11700`) uses only registered Value rows,
the body's endpoints and fresh Effect rows. `retain_inferred_entry`
(`candidate_context.rs:1536–1547`) appends row/occurrence provenance only.
Apply (`shadow_apply.rs:4085–4158,4207–4224`) likewise uses existing endpoints,
fresh invocation Effect and the four-port demand. Ordinary endpoint
translation (`lib.rs:11815–11842`) maps effect leaves/rows to `E0`. These
constructors introduce no view, weight, contribution or Allowance.

This checks more than “no concrete effects occur.” The view/signature
constructors that can generate Allowance in
`candidate_effect.rs:859–902,2147–2273` require annotation/operation/primitive
actions or an already retained view. The relevant source actions are absent;
the remapping cases have no initial view to copy. `candidate_register_capture_bound`
(`673–684`) requires an existing Allowance with a tail and therefore cannot
bootstrap capture incidence from `E0`.

## Native preservation cases

### Source context and relation publication

`candidate_context_pair` canonicalizes representatives without changing an
endpoint's constructor. `canonical_effect` changes only `EffectRow(r)` to
another `EffectRow` (`lib.rs:13491–13497`). For any pair in the induction,
`candidate_closed_allowance` returns `None`, hence
`candidate_context_source(pair)=I` (`candidate_context.rs:3361–3372`).

`candidate_context_seed` starts with `F0`; the demand/release block is guarded
by `scoped_enabled` (`3394–3418`). The formal variant adds only formal
provenance. `candidate_context_admit` obtains `I` for both the child and any
synthetic parent pair (`3458–3479`). `relation`/`relation_with_sources` inherit
the processing relation's flow, or default when there is none (`3025–3035`).
The processing relation already satisfies `J`.

`relation_with_scoped` either reuses an identical key or publishes that exact
pair/context/flow (`3062–3093`). A default flow uses `ScopedFlowId(0)`.
There is also a defense against interning a new nondefault flow while scoped
mode is disabled. The proof does not rely on that rejection for progress:
all reachable arguments here are already `F0`; the flow tables stay empty.
Sources, origins, attachments and evidence keys can grow independently without
altering these context/flow arguments.

### Whole-Value rewrite and all Function ports

`candidate_context_value_rewrite` recomputes the local source context from a
Value pair, hence obtains `I`. It copies the parent's `F0`; its demand-root
rewrite is skipped because `demand=None` (`3483–3503`). Actual structural
extrusion/rebuilding selects existing ports or reconstructs them from existing
ports and rows; it cannot introduce a new effect endpoint constructor.

For `candidate_function_port_admit` (`3505–3568`), the parent's
`post_check_context` is `I` by induction. Argument and ArgumentEffect record
the `Swap` *dependency operation*, but a structural `Swap` node is allocated
only if the inherited context is nonidentity. That guard is false. Result
and ResultEffect preserve `I`. The local source context is also `I`, so no
PrefixLeft composition is performed. Parent demand is absent, so neither
`stamp_input` nor `protect_body` is called. All four children use `(I,F0)`;
their Effect endpoints are selected from Function ports already in `E0`.
Dependency orientation and four-port variance remain unchanged.

Tuple/record/variant port admissions (`3572–3667`) also preserve `(I,F0)` if
called with carrier-preserving children, since their local/inherited contexts
are `I`. Authentic K0 supplies none of these structural roots, so their native
dispatch branches have no K0 producer. This robustness observation is not an
extension of the source domain.

### Bound construction, physical storage and transport

`candidate_apply_value/effect` select a row owner and existing endpoint bound;
they add no new endpoint constructor (`candidate_extrusion.rs:1115–1176`).
When an Effect pair has no row owner, `candidate_check_effect_operand`
(`candidate_effect.rs:1225–1294`) returns immediately for BottomPositive;
its Support expansion and contribution/member checks require operands absent
from `E0`. It therefore cannot bootstrap an operand or view. Existing
incompatible Value atoms only produce diagnostics, which create neither.
Physical bound admission and replay use these endpoints. The bound relation
owner is `candidate_bound_origin_with_evidence`
(`candidate_effect.rs:530–552`); ordinary mode calls
`candidate_context_bound` even for the evidence-cause variants.

`candidate_context_bound_for` (`3898–3937`) either uses the retained processing
parent or reconstructs the origin relation using `candidate_context_source`.
In either case its parent is `(I,F0)`. The checked-Allowance-bound branch is
unreachable from `E0`, but would also select `I`. Otherwise it uses the parent's
`post_check_context=I`. `bound_scoped_payload_for` returns `F0` immediately
when scoped mode is disabled and the parent flow is default (`3043–3060`),
including cross-sort structural derivations. The child is `(I,F0)`, and
`attach` retains that child without mutating it.

Transport with evidence (`4318–4332`) takes the parent's post-check context.
`transported_scoped` changes only a present demand's root (`2866–2878`), so
it fixes `F0`. Plain transport and bundle transport (`4300–4316,4334–4358`)
copy the same parent context/flow; bundles are inert source provenance.
`candidate_transfer_bound_origins` (`candidate_effect.rs:685–728`) iterates
exact existing fibers and separately re-admits diagnostic origins. Each
executable child uses the transport lemma, and every ordinary diagnostic
re-admission uses the bound-construction lemma. This proves context/flow
preservation even if a fiber association is absent; it makes no coverage claim
and does not manufacture a missing lineage.

R336's reviewed L0 excludes new higher-level row copies and their qualifying
parent/copy intrusion in K0. Independently, any canonical representative
transport here maps rows to rows and selects/copies existing Function ports.
View-remapping or `IncomingAllowance` extrusion cases
(`candidate_extrusion.rs:179–224,337–386`) require an existing view or
capture-incidence entry, both absent under `J`. Thus using L0 does not conceal
an alternative Allowance creation route.

### Replay, canonicalization and execution

`candidate_context_begin_replay` iterates actual lower/upper retained fibers
(`3992–4069`). Both contexts are `I`; its explicit `I,I` case returns `I`
without allocating `Replay(I,I)`. Both flows are `F0`, so
`compose_scopes(0,0)=0` (`2816–2824`) and the upper demand is `None`. Every
replay child is `(I,F0)`, regardless of replay-head progress, source-set union,
incoming-use flag or duplicate dependency keys. Replay consumers and typed
drains select existing children and restore an existing processing handle;
they do not invent contexts (`4097–4227`; `lib.rs:14301–14418`).

`candidate_context_transport_task` (`3767–3785`) reuses the parent for an
unchanged key or copies its post-check context and flow after representative
change. `candidate_context_canonicalize_bounds` (`4230–4249`) uses the same
transport lemma and then an `(I,F0)` derived child. This remains valid for
third-owner bound incidence. Representative equality preserves endpoint
constructors and cannot turn a row into an Allowance.

`candidate_context_execute_relation` first sees flow transformer 0 and scoped
mode disabled, then returns `Ok(false)` at `key.context==I` (`3800–3826`).
It never enters `candidate_zero_word_filters`; it creates no checks,
`checking_filters`, discharge entry or residual. Consequently
`post_check_context` (`3297–3301`) returns the relation's `I` on every next
step. This is the inductive discharge case, rather than an assumption that a
filter has already been discharged. The typed drain continues with ordinary
dispatch; context identity does not skip Value/Effect propagation.

### Capture, retained inputs and fresh-use boundary

K0 does perform boundary-0 root graph capture (`candidate_scheme.rs:2904`).
Capture traverses existing shapes/bounds; `context_payloads(I)` supplies no
weight (`candidate_context.rs:1696–1726`), and default flow supplies no latent
demand (`candidate_scheme.rs:2680–2695`). `E0` becomes graph rows or pure
leaves (`1935–1988`), never `Node::EffectOperand`. Root capture therefore
introduces neither an executable view nor a new context. Retained-input
inspection follows identities/evidence and is read-only for these fields.

The exact K0 domain has no module/import/local/role/member/operator use, hence
no source action invokes incoming/local fresh instantiation. This follows from
the actual Name-resolution and binding cases, not from an assumption that a
general scheme carries identity. For completeness, the production fresh-use
constructor has the expected preservation property for a graph captured under
`J`: its operand/view loops are empty, context roots are all `I`, and
`rename_fresh_contexts` maps `I` to `I` without allocating a context node
(`candidate_scheme.rs:4307–4367`; `candidate_context.rs:1573–1664`).
`begin_candidate_fresh_bound` obtains this exact mapped root
(`candidate_scheme.rs:4615–4624`), and
`candidate_context_fresh_transport_scoped` explicitly chooses `F0` in ordinary
mode (`candidate_context.rs:4278–4290`). An arbitrary caller-supplied
nonidentity ContextId is not covered by this constructor alone: the authentic
caller/rename route is necessary. No such arbitrary input is admitted by K0.

Administrative bookkeeping, diagnostic replay, source depth, memo completion,
replay acknowledgements, processing save/restore, source-set interning, and
evidence attachment only copy/select existing endpoints or relation handles,
or update fields outside `J`. Any rollback to a saved prefix satisfying `J`
preserves it by deleting new entries/restoring old ones; no full rollback or
capacity-restoration theorem is needed or asserted.

These cases exhaust the production relation/context constructors and their
relevant authentic K0 callers in the pinned owners. By the joint induction,
`J` holds at every stated prefix, yielding all four target claims. This is a
source-derived proof candidate: independent review must still challenge the
constructor/caller census before Luna accepts closure.

## Application, falsifiers and remaining obligations

If independently accepted together with the primary's separate source census,
this result supplies the exact ordinary default-flow/no-Allowance/context
lifecycle premise left OPEN in R336. Combining it with R336's reviewed L0 and
constructor induction yields that D1 package under the original authentic
complete-construction, single assignment `ρ⊨H(C_s)`, and `Reifiable₀(ρ)`
premises. The root judgment still uses the authentic body-to-root Value Link
and Value subsumption, and reports the body's Effect endpoint; no root Effect
row is introduced.

It does not prove that a completed native graph preserves/contains every
source constraint, cache or temporal/fiber coverage, model existence W,
termination Z, G-completeness, export witness transport, actual-machine D3,
principality, full A/B, catalog correspondence or production authority. Those
parents retain their original quantifiers and owners. In particular the old
Value-only restoration theorem's identity assumption is not enough to reuse it
for mixed Value/Effect K0; this packet discharges only identity metadata.

The decisive falsifier is an authentic `ValidK0` source and successful native
constructor prefix reaching the first non-`E0` effect endpoint, view/weight,
nondefault flow, nonidentity context or discharge mutation. A hand-built
`ContextId`, fabricated scoped demand, annotated function or imported scheme
does not meet that source qualification. A missing reachable caller that can
create one of these is a blocking census finding even without a runtime probe.

Mutual TODO `R337-J-REVIEW`: Luna freezes this artifact plus the primary census
and appoints a fresh non-contributor. Required inputs are these exact source
pins and the authentic K0 entry/action crosswalk; expected output is an
independent complete-mutator disposition or first source-qualified falsifier.
No implementation change is requested. If review finds an omitted owner, Luna
owns any dependency/lease revision before further writing.

## Dependency manifest and execution receipt

All following SHA-256 values were read and matched locally; these are source
bytes, not executable transition observations.

| Pinned file under `crates/yu-solver/src/` | SHA-256 |
| --- | --- |
| `candidate_context.rs` | `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5` |
| `candidate_effect.rs` | `d156fdbf0300387a5aa036053a2cc7eeb6312a803aaf38838e30dd2731ca4945` |
| `candidate_scope.rs` | `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a` |
| `candidate_source.rs` | `0dc798e48e70505093e52b31b2569e3b2d8ff1dee663095176aaf547ccb3289b` |
| `candidate_call.rs` | `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f` |
| `candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |

Worker/session: `/root/r337_k0_context_prover`,
`291c0520-43ca-4741-a760-f56a1f641e33`. Requested model/effort:
`gpt-6.1-sol` / `high`; observed model/effort: `UNKNOWN` / `UNKNOWN`.
First clock: 2026-10-23 04:24:43 UTC. Grant: 1,200 seconds, charged in full
on assignment, no renewal or carryover. Source inspection and byte hashing
only; no tests, Cargo, builds, execution probes, Git or external contact.
Only this artifact and the one assigned inbox file were created; no scratch
paths or descendant leases. The final inbox receipt records the stop clock,
artifact hash and explicit writes-stopped state. This candidate is pending
independent review/integration and grants no production authority.
