# Adversarial source test of formal-local directional view introduction

Date: 2026-10-06
Baseline: `38dab1fb926f819d1b2a25835d990d32b3915038`
Status: frozen producer/falsifier research; independent review pending
Claim class: source-constructor placement discriminator and bounded failed
             falsification of the repaired fragment constructor
Semantic/implementation authority: none
Exclusive lease: this note and `tools/research_directional_source_view.py`

## 1. Result

The concrete new attack concerns **which path receives the formal-local
fragment before Value entry**. The argument carrier's computation effect and
the returned callable's invocation effect are different source positions.
For the exact approved nested component, `f` has the outer source interface
`Value(A_f)`. Its whole received argument has interface `Comp(E_arg,A_f)`.
The directional upper fragment is at a Function output position in `A_f`.
Before Force/rebind, that position is therefore under `result.call.effect`,
not the carrier's root `effect` position.

A factory client makes this distinction concrete. Its computation emits
`q_make` and then returns a callable `v`; a later call to `v` emits `q_call`.
Flattening the formal's upper position onto the argument-carrier effect port
assigns the fragment to the factory event and loses its matching returned
Function path. The repaired candidate instead embeds the fragment under the
carrier **result** path, then removes that prefix at Value-entry rebind.
It survives this attack.

The known source outer-interface/entry skeleton and original upper Function
elimination can generate that dependent path map before solving. It is too
strong to say that the map itself must be assumed as `SourceViewInst` merely
because the latter judgment has not been published. This investigation finds
no counterexample to the repaired constructor within this fragment. It does
not prove semantic totality of the full seed/refined relation, carrier/context
admission, the recursive generalized supplier, or production conformance.

## 2. Governing sources and exact source envelope

The authoritative source is the exact candidate

```text
my apply f = { my step x = f x; step }
```

Its [nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–3 fixes the outer formal, returned local function, same captured `f`, and
later use. It does not certify current parsed/typechecked acceptance.

The [inferred-view decision](../design/2026-10-05-inferred-function-call-views.md)
§§1.1–5 fixes one shared source callback contract without requiring a written
annotation, the selected unannotated formal seed/view, original source
identities and `xi=(nu,K,D)`, and preservation of actual provider role/entry.
The [directional user decision](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
§§2–4 marks original upper `c`, creates no new lower/provider `g` protection,
and retains independent lower protection.

The conditional [typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
§§5–7 supplies the outer Value entry and whole-argument carrier skeleton,
Force/rebind/result paths, and evidence-preserving checking. The reviewed
[source-call construction](2026-10-06-source-call-generation-construction.md)
§§3–5 generates the dependent Function output address and Name/capture map
schemas without solved shape. Its `TypedCallCert_Dec` still consumes typed
decoration premises. [Typed-boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
§6 supplies ordinary typed path structure, indexed packet image, boundary
introduction, and the distinct roles of receipt and observation.
[Charter](../design/2026-09-29-scc-intrusion-redesign-charter.md) §13 supplies the
binding transport/expiry direction; §§22–23 keep every derived variable-level
comparison guard in force.

The factory client is a mathematical source graph using the existing
Request/Return/Call constructors and an independently typed callable/provider.
Its particular operation declaration, carrier typing and open-client admission
are hypotheses. There is no asserted raw Yulang factory program, new syntax,
accepted production fixture or interpretation of arbitrary imports. The
source-base envelope is [source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
§§3.1–3.4; its constructor/admission certificates remain separate.

## 3. The discriminating source-constructor derivation

Register the ordinary unannotated formal, preserving its inferred root:

```text
Gamma(d_f) = Value(A_f)
seed k from actual absence of annotation at d_f
step's Name f resolves/captures that same d_f, A_f, R_f
original source Call f x generates upper U_i at R_f
p_i = its original complete-invocation output-effect occurrence
Dir-Protect generates delta_i at p_i
```

These are the registration/Name/Call premises of the reviewed
[joint source judgment](2026-10-06-directional-joint-source-judgment.md) §§3–4.
An existing lower precedes or accompanies the upper without becoming a new
protection producer. This static derivation does not consume the factory's
solved callable shape or a successful pending comparison.

At an actual invocation of `apply`, the source outer interface determines
the whole-argument result skeleton:

```text
argument carrier: Comp(E_arg,A_f)
carrier computation observation: argument.effect
returned Function observation:  argument.result.p_i
ordinary Value entry: receipt -> Force -> RebindResultPath -> body
```

For every dependent typed path `p` in the result value domain, define

```text
EmbedResult(p) = result.p
RebindResultPath(result.p) = p
RebindResultPath(effect) is undefined
```

This is ordinary typed path prefixing/projection. No effect membership,
endpoint value equality or event-family equality participates. The composition
is identity on this domain, so it transports the original source occurrence
index and receiver reference unchanged.

| Source event/position | Correct pre-rebind fragment path | Flattened fragment at carrier effect |
| --- | --- | --- |
| Factory request `q_make` at `argument.effect` | No incidence from this fragment | Wrong incidence |
| Returned callable path `argument.result.p_i` | Matching prospective result incidence | Missing incidence |
| Rebound formal path `p_i` | Prefix projection retains fragment | Root computation mark has no result image |

This table concerns profile-path incidence, not a blanket event protection
claim. A later `q_call` additionally needs its actual executing-view
observation, same-view receipt and live original receiver. In particular,
ordinary execution of this exact component returns `step` and ends the
`apply` invocation; a later call after that expiry retains the raw profile
but gains no activation-scoped protection from the expired receiver.
The discriminator does not keep that activation alive or infer visibility
from static path membership.

The two requests can have the same operation family and the upper/lower
effect endpoints can have equal denotations. Their computation/result and
source upper/lower occurrence indices remain distinct. A function's creation
computation and its future invocation are different source computations even
if the same underlying callable value is returned.

## 4. Repaired candidate: what can be generated without SourceViewInst

The candidate under attack is:

```text
1. Register source formal/seed and generate original tagged upper delta_i.
2. At original formal receipt r_A, introduce a formal-local fragment whose
   path is EmbedResult(p_i), retaining original beta,u_i,k,sigma and xi.
3. Force the designated argument carrier according to actual Value entry.
4. On return, project EmbedResult(p_i) to p_i at formal rebind; retain the
   actual returned provider packet as a separately tagged source.
5. Capture/read that same typed formal view by the existing binding image.
```

The known outer source role generates step 2's path schema. The original
upper constructor supplies `p_i` with its Function output sort dependently
on `U_i`. Their composition does not require the source type to be solved,
the complete profile to be enumerated, or a new copy of the actual callable's
private environment. It may emit independently interpreted constraints on
the same joint witness before their satisfiability is known. Accordingly,
an argument that this map cannot be generated because a completed
`SourceViewInst` was not already available would be circular.

This is a dependent map over the demanded formal view, not an assertion that
every unconstrained provider descriptor in `A_f` already has that Function
path. Under a well-formed joint realization, carrier/result typing and the
same-decorated-value Function obligations must establish its typed domain.
If those obligations fail, the emitted schema is still generated but no
well-typed executable instance follows. An inclusion witness cannot itself
create the boundary; the candidate uses the original formal source policy
for introduction and retains inclusion as a separate constraint.

The receiving invocation already exists in the ordinary entry skeleton.
A formal-local boundary records that original receipt's source contract;
it does not create an additional invocation or an actual Handler entry.
The direction supplied by the user is compatible with such an introduction.
No alternative current-authority-consistent interpretation forbidding this
constructor has been exhibited here.

The [completion-parametric theorem](2026-10-06-directional-profile-completion-factorization.md)
can use this generated schema fragment by fragment once its independent
typed realization is established. It still quantifies over compatible
original completions and asserts no compatible-completion existence.

### Coverage attacks on the repaired constructor

**Effectful, suspending and divergent argument carriers.** The boundary may
be prospectively indexed at `result.p_i` before the carrier returns. Its
root computation requests remain at `effect`. If Force suspends or diverges,
there is not yet a rebound formal value/view or a `q_call` observation. A
construction that insists on an actual returned callable at receipt would
exclude admitted divergent carriers, contrary to source-contract §3.3.
The schema can avoid that error by retaining dormant result-path evidence
and materializing the rebound view only on an actual Return. This is a
coverage condition on the candidate, not a discovered contradiction.

**Actual provider evidence.** Rebind has at least two separately indexed
sources: the factory's actual returned-value packet and the original formal's
upper fragment. Project the corresponding paths in each without rewriting
the provider's original occurrence labels or deleting independent provider
protection. `K` retains predicate identity under the one original `nu`; `D`
and lineage retain their corresponding sources. Adding the upper fragment
does not add a lower mark, even if its transported target path matches a
provider path or endpoints coincide.

**Several upper uses with one captured root.** Embed each source-tagged
`p_i` into the same original result domain. Matching a common signature path
does not merge the distinct `u_i` or authorize choosing a separate `U_i`,
profile completion or `xi` per port. If independently interpreted whole-use
constraints are incompatible, the joint relation may be empty. The constructor
must preserve that emptiness rather than stitch individual witnesses.

**Generalized uses and recursive lower-first information.** The result-prefix
map commutes with a supplied whole source-origin renaming, fixing captured
imports and retaining lower packets. This law is a transport consequence,
not construction of that supplier. Every derived comparison still re-enters
the variable-level guard; a prefix map licenses no forbidden extrusion or
new source seed. For arbitrary recursive predicate arguments, source
constructor equivalence must be checked before taking the designated fixed
point. A final-solution comparison alone does not establish this law.

The last four paragraphs identify tests a producer must satisfy. They are
not proofs of arbitrary recursive/generalized source coverage.

## 5. Exact remaining semantic test; failed shortcuts are controls

The useful residual is the **paired receipt/Force/rebind constructor lemma**.
It must prove that the original unannotated formal's independently interpreted
seed-view judgment and the proposed formal-local result-path introduction
describe the same whole source relation, including active consumers:

```text
for original scopes, shared xi,w and arbitrary recursive arguments X:
  OriginalFormalReceiptSeed(xi,w;X)
    iff exists_original_scopes z.
          IntroduceResultFragmentThenEntryRebind(xi,w,z;X)
```

Here the left side already carries the selected source protection meaning.
It must not be defined as a bare provider view lacking that meaning simply
to manufacture a counterexample. The right side's boundary/view witnesses
are shared with all actual entry, provider/result and later-use predicates.
The constructor must establish carrier/result well-formedness and typed
packet preservation for independently admitted source carriers, rather than
create admission by successfully checking the decorated target.

The [full relation note](2026-10-06-directional-full-relation-and-gate-delta.md)
§4 gives the correct original-scope joint-extension criterion. Its DREL-1
inlining result then handles active protection predicates and recursive
operators. An append-and-erase bijection for boundary records alone does not
prove this paired constructor lemma: a consumer can inspect the boundary's
placement, as the factory discriminator demonstrates. Conversely, that
discriminator is not a counterexample to a correctly placed constructor.

The following previously settled failures were used only as controls:
copying a public callee view onto private provider bindings; replacing the
original receiver with a later captured-closure invocation; reconstructing
upper provenance from equal values; treating capture alone as typed packet
attachment. They are already excluded by typed-boundary §6 and the existing
frontier notes. None is presented as a new principal finding or another
reason to reject the repaired formal-local candidate.

There is no claimed semantic independence theorem, undecidability result,
new required user decision, full all-view admission/principality result,
or production inclusion. Callback B and Option A/2 remain unchanged;
production-only alternatives need not have source-base constructors.

## 6. Executable envelope and exact verification

[research_directional_source_view.py](../../tools/research_directional_source_view.py)
is a standard-library path-placement model for the displayed constructors.
It generates the selected static formal/Name/Call association, prefixes its
upper path using the whole-argument result skeleton, and tests correct versus
flattened placement. It tests rebind projection, original receiver/occurrence
retention, equal upper/lower endpoint denotations, and a supplied Boolean
protection-sensitive kernel. It does not implement Yulang handler visibility,
dynamic typed receipt, the factory's admission or source-view totality.

The literal expected path/incidence table is independent of the candidate
functions, but both share the stated typed constructor interpretation. This
is source-constructor characterization, not independent validation of that
interpretation. Unlike the earlier seven-input supplied-record scheduler,
there is no `At` input, closed-scheme certificate, record delivery schedule
or ten-mutation repeated inventory model.

Command, from repository root:

```sh
timeout 60s python3 tools/research_directional_source_view.py
```

One bounded pilot and one final check passed, in one Python process each,
with an internal 256 MiB address-space cap, 55 CPU-second cap and external
60-second wall cap. Memory availability was inspected before the pilot;
no heavy compiler/build process was started. The process inventory command
failed in this environment, so it provided no reliable concurrency evidence;
the probe remained tiny and strictly single-process. No process pool,
Cargo invocation, random search, parser, Oracle execution or production
acceptance test ran. Local Markdown-reference, whitespace and pinned-input
byte checks accompany freeze. No broad suite was warranted by research-only
source-path files.

## 7. Frozen dependency and integration packet

Consumed semantic inputs were byte-equal to the pinned baseline at freeze.
The source contract and source-call documents were narrow dependency reads;
there was no expansion to unrelated Oracle or production implementation.

| Input | SHA-256 |
| --- | --- |
| directional addendum | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| inferred call views | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| typed-boundary realization | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| typed-computation core | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| charter | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| nested-block addendum | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| source contracts/common allowance | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| source-call construction | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| completion factorization | `f3a1261968db9edac0c8841151d90c35fc1cf9649c00bd7beb5d18f748239d4d` |
| full relation/gate delta | `9360bc36839d76c5c10354a4996249fe5b7a5a16f648b619ed685327c6ac695f` |
| joint source judgment | `fc459dfac03693f426dea575585a0d20d7a075f8c7ac27be9fd2e67a150466c1` |
| earlier source-relation falsification | `8dbf4dc55481398d2f882903eab23d56aad0efb7f618c9a095e2ff425c3a437c` |
| earlier source-relation checker | `0018aa71e721bd8a3de29a89faf601238284cd67605ae7219baed2c12cab4cbb` |

Commit-ready paths, contingent on primary lease/diff adjudication:

- This note and `tools/research_directional_source_view.py` only.
- Baseline: `38dab1fb926f819d1b2a25835d990d32b3915038`.
- Status: unreviewed producer/falsifier research. No independent certification.
- Proposed subject: `research: test directional formal fragment result-path placement`.
- Proposed shared-record delta: distinguish generated result-prefix map schema
  from source-typed paired constructor totality; record the factory-placement
  discriminator and failed falsification of the repaired local candidate.
- Shared records deferred to primary/curator: `tasks/current.md`,
  `tasks/research-lab.md`, `notes/design/INDEX.md` and theory maps.

No production code, current expectations, questions, authoritative design,
shared-status path, other worker output, Git index or branch ref was changed.
No children were launched. Freeze ends this lane; further experiments require
a concrete changed premise or accepted review finding.
