# Native negative residual equation: payload transformation obstruction

Date: 2026-10-12
Status: frozen, independently reviewed bounded algebra derivation
Claim class: constructive bounded algebra lemma and exact source-owner obstruction
Parent native negative residual equation and original hygiene H: OPEN
Baseline: `62864a09433a012f7739dbf49a57535a70979ba6`
Branch: `research/simple-sub-intrusion`
Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Producer: primary-assigned prover leaf; no delegation
Exclusive lease: this file only

## 1. Frozen obligation, binders and exclusions

The original H quantifiers remain those in
[global hygiene proof](2026-10-11-oracle-global-effect-hygiene-proof.md) §1:
original successfully lowered source programs, actual composed-negative
annotation occurrences, original scopes/binders, actual copies and actual
call/output routes. No independently chosen provider, contribution, witness,
tail or residual replaces an actual originating one.

For each actually reached composed-negative concrete annotation instance
`(o,a,sigma,s,C,x)` and actual residual-producing Row-upper demand
`d = u <: Row(I,t) @ chi`, derive jointly the branch predicate and
`(lambda,J,kappa,g,beta,pi_t)`, with live consequences

```text
F_lambda = u <: Row(J,g) @ beta
P_lambda = g <: t        @ pi_t
```

`s` is the occurrence's set-wide attachment identity, with distinct resolved
member operands/ordinals; `lambda` is this constructor's residual lineage.
`x` is the original annotation binder. `t` is the actual demanded Row tail;
`t=x` is not assumed. Any further `g <: x` consequence needs the actually
established directed/contextual connection from `t` to `x`. `I` is the actual
upper head vector, not automatically annotation set `C`. The context `chi`
retains its original operation order, shared child identities and parents.
Applicable source lower fibers retain their own origin/context associations.

Required conclusion includes checking the actual receiver and active payloads
before consuming a filter, attachment-local subtraction preserving an
independent same-family contribution on the same identified row, separate
lineages, both relations' activation, and applicable current/future lower
delivery. Identify filter-only branches with no gamma. Naming or storing the
relations, or assuming complete replay, does not meet this conclusion.

Shared hypotheses for static facts: the pinned bytes; resolved source operands;
normal completed owning calls before exhaustion. Actually reached consumers
are required for operational claims. No negative constructor, recipe,
source/route license, residual transformation, arbitrary policy consistency,
complete queue drain, soundness or principality is assumed. The bounded lemma
in §3 fixes its separate algebra interface explicitly; it does not narrow H.

Exclusions: compiler/tests/expectations/shared-record writes; builds, tests,
Oracle execution, executable probes, Git mutation, semantic adoption,
concrete-formal enabling, source restrictions, model escalation and delegation.
Complete Call, capture/freshening, levels/extrusion, qualifying parent/copy
intrusion, generalization, normal progress, soundness and required principality
remain unproved. The withdrawn callback scheme supplies no expected output.

## 2. Authority and direct construction attempt

Governing sources:

- [Annotation hygiene integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
  §§1–4: composed polarity, original symbolic connections, local subtraction
  and independent contribution preservation.
- [Attachment/admission](../design/2026-10-10-contextual-attachment-admission-design.md)
  §§3–6, particularly source lines 88–96, 106–122 and 133–145: exact shared
  contexts, set identity, checks, residual feedback/projection and replay.
- [Residual lineage selection](../design/2026-10-10-contextual-residual-lineage-selection.md),
  “Selected policy”: distinct constructor identity and every applicable
  current/future lower meeting every retained recipe.
- [Top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
  §§1–5 and “Authority and integration”: native Simple-sub construction and
  necessary abnormal-path safety; full restoration is not a premise here.

The transition contract specifies responsibilities and required retained
outputs. Its Concrete-residual clause does not give an equation calculating
`J`, `kappa`, `beta` or `pi_t`. In particular, neither that clause nor the
Negative-wrapper clause says to substitute `WithoutLeftFilter(chi)` for the
payload subtraction. To test whether the missing operation nevertheless
follows by composition, this pass inspects the actual six ContextExpr
constructors and their actual evaluator, rather than supplying another
recipe-installation/replay assumption.

The established inputs are the reviewed
[Oracle N/F/R source derivation](2026-10-12-oracle-negative-stack-filter-source-proof.md),
[Y3 construction obstruction](2026-10-12-y3-negative-effect-construction-bridge-proof.md),
[finite transition](2026-10-12-y3-negative-residual-transition-proof.md), and
[negative-filter owner equation](2026-10-12-negative-filter-rule-proof.md).
Their operational limitations are retained. No prior conditional lemma is
promoted to a native equation.

## 3. Constructive lemma: contexts do not transform surviving PUSH families

**Local statement, independently reviewed within its stated scope.** Fix any finite
ContextExpr DAG accepted by `State::fold_context`, and any fixed admissible
detached weight environment `W`. Admissible means each left entry has a family
exactly when its PUSH count is positive, as checked by `append_left`; all
referenced handles exist. Assume `evaluate_context(root,W)` returns normally.
For every active left entry `(id,pops,pushes,A)` in its returned value, with
`pushes>0`, some supplied weight in `W` contains an active left entry with the
**same id and same family A**. Family equality is the actual finite set
equality of `DetachedPushFamily`, not contribution or attachment equality.

Define the fixed inventory

```text
Inventory(W) = { (id,A) | an active left entry of some W[j] has id and family A }.
```

The lemma is `active_payloads(Eval(root,W)) subset Inventory(W)`. It permits
arbitrary counts, all six expression constructors, arbitrary bracketing and
repeated/shared children. It does not require zero words, identity contexts,
one attachment, one recipe, or distinct nominal families. It makes no claim
that the supplied detached inputs are emitted by source constructors.

**Append primitive.** `candidate_context.rs:1153–1179` examines one incoming
left entry at a time. If its id is absent, insertion copies the incoming
entry. If the id is present, two nonempty family values must compare equal or
the call fails. Count cancellation computes new POP/PUSH counts. A surviving
PUSH selects `current.family.or(incoming.family)` and copies that family;
it never intersects/subtracts its members. Zero total counts remove the
entry. Thus successful append preserves the union of the two input inventories.
`append_right` at 1180–1191 changes only POP counts. `right_to_left` at
1193–1197 introduces only POP entries with no family and zero PUSH count.
`mix` at 1199–1212 uses those primitives and may move a PUSH-free result back
to the right; it creates no new PUSH payload. These observations prove the
primitive preservation lemma for arbitrary counts.

**Induction on the actual DAG.** `fold_context:1439–1485` checks that every
child precedes its parent, evaluates shared children once, and presents
Replay's ordered children as `[lower,upper]`. Hence well-founded induction
uses the actual child results, with no independent marginal evaluation.

| ContextExpr / actual evaluator lines | Inventory consequence |
| --- | --- |
| Identity, 1491 | Empty active inventory. |
| PrefixLeft, 1492–1498 | Append the fixed prefix then the child; intersect only the separate filter. Primitive preservation applies. |
| SuffixRightPops, 1499–1508 | Copy the child's left entries and change right POPs only. |
| Swap, 1509–1515 | The output left is made from incoming right POPs; no surviving PUSH. |
| BothFromRight, 1516–1519 | The output left likewise contains POPs only; copying the same right input does not create a payload. |
| WithoutLeftFilter, 1520–1522 | Copy the child and set only its separate filter to All. |
| Replay, 1523–1528 | Copy lower; append upper's left; intersect filters; append upper's right then lower's right; mix. Each primitive preserves inventory. |

Every constructor therefore preserves the stated inclusion. This completes
the bounded source induction. It is not a checker/probe and assumes no
unimplemented residual transition. `BothFromRight` here is only the inspected
detached evaluator's behavior; no certificate/source authorization follows.

**Corollary.** If every supplied active payload at id `s` has family `{E,F}`,
where resolved nullary `E != F`, no such successful context evaluation yields
an active PUSH at `s` with family `{F}`. Cancellation can remove the whole
PUSH or change its count, but cannot partially transform its payload. Extra
filter sets, unrelated weights at different IDs, swapping, correlated sharing
and extra replay nodes do not change this conclusion. Supplying a new weight
already containing `(s,{F})` would evade the premise by assuming the missing
payload construction; this corollary says nothing against such an independently
proved owner operation.

## 4. The exact Oracle operation absent from that composition

All Oracle source locators below are at the pinned Oracle revision, read with
`git show`; no execution ran. The negative result constructor at
`signature_effect.rs:162–178` produces `Stack(Var(x),FILTER(C))`, without
PUSH/POP entries. `effect_row_stack:382–421` separately builds one set-wide
PUSH id for the resolved atom vector; registration is at 434–439. Those
facts do not establish a reached Row-upper demand.

For a demand actually reaching `row_effect.rs:88–234`, its residual branch
derives the following from the owner, not from a stipulated replay grammar:

```text
L0       = L with its checked filter replaced by All
J        = collect(intersect actual upper heads I with active payloads in L0)
Lr       = subtract families(J) from each active left payload of L0
beta     = identity                       [Oracle emission only]
kappa    = the resulting residual weight Lr [Oracle operation only]
pi_t     = directed_mix(Lr,R)              [Oracle emission only]
F        = u <: Row(J,g) @ identity
P        = g <: t        @ directed_mix(Lr,R)
```

Head checking and filter clearing are at 120–131; intersection/collection at
153–155, 794–815 and 1005–1089; residual weight construction at 174–179 and
1190–1216; both emissions at 216–233. The payload transformation preserves
each stack id and its leading POP/PUSH counts, transforming its family through
`subtract_effect_families:1219–1273`. Matching invariant type arguments create
their own obligations. Those obligations are not assumed discharged.

For the nullary operational input `L0=PUSH_s({E,F})`, `R=identity`, `I=[E]`,
and `t` not equal to source `u`, the owner retains `J=[E]` and constructs
`Lr=PUSH_s({F})`. There are no payload arguments to compare; `E` matches
the actual head and `F` does not. This follows directly from the SetMany
branch at 1244–1259 and the reconstruction loop at 1206–1213.
`effect_row_stack:398–420` supports the original two-atom payload construction.

More generally, on finite nullary payloads the inspected loop derives exactly
`(id,p,n,S) -> (id,p,n,S minus families(J))` for every active entry, while
retaining its POP/PUSH counts and attachment id. This is a derivation of the
Oracle operation, not a proposed denotation assumed for Y3. It introduces no
new nominal effect atom, although the resulting payload set may differ from
every supplied payload set. Its body transforms supplied stack payloads; it
does not classify independently stored concrete lower fibers as belonging to
those payloads. That separate association is the decisive missing hygiene
premise.

This is an **operational input discriminator**, not an authenticated full
source-program trace or a counterexample to H. No claim establishes that
those operands meet at one actual source-generated demand. Its precise use
is narrower: an exact representation of this Oracle payload transformation
using only contexts over the original weight inventory is ruled out by §3.
The actual Oracle owner performs a family operation that the current Y3
expression composition lacks. In particular, `WithoutLeftFilter` is not it.

The inspected Oracle branches also prevent an unconditional gamma rule:

| Reached branch | Owner action, no residual gamma allocation |
| --- | --- |
| Initially empty weights, 96–118 | Existing-lower reduction or ordinary Row upper storage. |
| Only a filter remains before checks, 120–143 | Check heads, clear filter, then ordinary Row upper storage. |
| Source equals actual tail and right is empty, 145–149 | Return. |
| No retained heads, 156–171 | Emit source-to-actual-tail under directed mix. |

These are Oracle branch facts, not adopted Y3 omission or admission rules.
The nonempty-retained branch may reuse Oracle's residual cache at 180–202;
Y3's selected policy instead preserves separately constructed recipe lineages.
Neither the cache nor the displayed equation proves attachment-local removal
of independent contributions or supplies a native projection to binder `x`.

## 5. Exact bridge and minimal owner blocker

The approved contract and current owners leave the following decisive premise:

> A source-owned native residual operation must construct the selected
> payload/contribution transformation from the actual checked `(I,t,chi)`
> and attachment/route license, retaining the original attachment identity
> and shared input. It must determine the correlated `J/kappa/beta/pi_t`
> and install both live relations under a separate constructor lineage.

**Decisive same-family discriminator.** Fix actual distinct lower fibers
`f_a,f_b` on the same identified source `u`, with endpoints `q_a,q_b` at the
same resolved `E`. Required local subtraction licenses `q_a` on this actual
annotation instance/route; the independent `q_b` must survive. The needed
authentic discriminator is the actual construction/propagation association
between `(s,a,sigma,route)`, this fiber's endpoint/origin, and its ordered
context, retained through the operation selecting heads to remove. An
attachment id, context id or source representative alone is not that
association. This paragraph identifies the missing premise, not a new
independently supplied eligibility relation.

The concrete owner facts are sharper than saying there are no identities:
`Contribution` at `candidate_effect.rs:140–144` stores effect, source origin
and instance; allocation at 864–886 takes only effect and origin, with no
attachment/route argument. `AnnotationMember(v,m)` retains a view/member,
and `View:166–174` may retain its source weight, so that case does carry a
useful source association. However `candidate_check_effect_operand:929–947`
reduces either endpoint to nominal effect membership and never reads that
association as subtraction authority. The ContextExpr nodes retain weight
and ordered child IDs but no existing residual operator performs this
fiber-to-attachment selection. No actually emitted negative operation supplies
the missing link, since the constructors reject it.

Joint bound evidence is also already present:
`candidate_bound_origin_with_evidence:420–470` passes bound, origin, relation
and cause together; `BoundEvidence::admit` at `candidate_context.rs:530–578`
groups by `(BoundKey,RelationId)`. This must not be replaced by the Cartesian
product of separate origin/context lists. Its OwnerEmission branch explicitly
records missing ordinary-seed/processing antecedents at 534–538; transport
and replay records retain additional coverage gaps at 588–622. These records
do not authenticate that `q_a`, rather than `q_b`, is subject to the selected
attachment operation. Proving finite `S minus H` cannot close this premise.

Thus the precise missing source rule is the owning negative/paired
constructor's actual operation and its fiber-to-attachment/route selection
at Row reduction. It must exhibit the authenticated distinct consequences
for `f_a` and `f_b`, then derive `H`, `J/kappa/beta/pi_t` from those same
inputs. The existing qualitative §4 residual responsibility already permits
an exact internal operation preserving that authority; permission to extend
the private grammar is not the blocker. Oracle-to-Y3 correspondence and
this discriminatory operation's correctness are the blockers.

An equivalent representation may implement this operation without copying
Oracle weights. This note chooses no new enum case, carrier layout, semantic
relation or universal inverse theorem. The established obstruction is to
obtaining the operation merely by composing the six existing ContextExpr
nodes over original payloads. The exact native rule still needs proof from
its owning construction; the qualitative residual clause does not calculate
it. Changing a shared original weight in place would also need proof that
other authentic uses retain their original inputs.

The owning seams are:

| Owner | What the inspected source actually supplies / what remains missing |
| --- | --- |
| `candidate_effect.rs:1034–1070,1507–1538`; `candidate_source.rs:98,117–132` | Negative concrete guards, before the general tail lookup; no native executable negative constructor. This is nonreachability, not a vacuous proof over admitted actions. |
| `candidate_context.rs:113–137,2174–2215` | Live words are zero-length. SourceUnitPush and its materialization are dormant/detached; the latter supplies no live relation or transformed residual payload. |
| `candidate_context.rs:178–204,1487–1533` | Exact six-node algebra and its detached evaluator; §3 localizes the missing family transformation. |
| `candidate_context_execute_relation:2744–2812` | Supported zero-word filters check/register on the actual lower, before retained discharge. Validator 2613–2709 does not execute nonempty PUSH payload reduction. |
| `candidate_apply_effect:840–863`, `candidate_check_effect_operand:888–956` | Level-selected insertion/replay, concrete allowance acceptance or unmatched forwarding; no gamma plus correlated F/P constructor. |
| `candidate_replay_bound:763–805`, `candidate_context_begin_replay:2911–2982` | Reached replay uses ordered lower/upper inputs and exact context fibers. It does not emit the missing residual operation or establish source attachment licensing. |

Oracle `bounds.rs:3213–3255,3285–3315` checks already stored/future lowers
through named filter registration/insertion owners. Completed lower insertion
at 704–741 separately checks filters and applies replay actions. These are
actual calls, but neither they nor two stored native relations establish
recipe activation or complete replay. Every applicable source lower must
still meet every distinct recipe with authentic context/origin association;
the selected lineage policy is a requirement, not an installed watcher.

An independent same-family contribution must not disappear merely because
its nominal family is in `J`. §3's operation obstruction does not supply
the decisive license or prove survival. Provider and call identity,
gamma-upper feedback, copies and generalization remain outside this local
derivation.

## 6. Proof-obligation economy and stop

The earlier replay route needed an assumed installed recipe; native
head-versus-tail dispatch lacked attachment discrimination. This direct
algebra route now proves that rebracketing the existing context operators
cannot produce a partial PUSH-family subtraction from unchanged inputs.
That removes one proposed route; it does not prove the original equation.

Under `rules/compiler-engineering.md` “Natural compiler behavior and
proof-obligation economy”, actual local subtraction, independent contribution
preservation and ordinary current/future delivery remain A/B. Recovering the
attachment/license/demand from equal rows or families would create D debt.
The annotation and residual construction own these facts; retain their joint
evidence and prove their actual operation there. The payload operation is
missing construction, not merely a lost fact that another record certifies.
No new all-view characterization or another conditional replay lemma closes it.

Stop at this exact owner blocker. One next action: the primary assigns the
native payload/contribution transformation equation at the negative
constructor/Row-demand seam, with the partial-family discriminator and
same-row independent-contribution survivor, for proof/design adjudication
before broad dependent implementation. Keep preflight disabled, original
H/soundness/principality and all related implementation gates OPEN.

## 7. Checks, resources and runtime

Static commands only: `cat`, `sed`, `nl`, `rg`, `wc`, read-only `git
rev-parse`, `git branch --show-current`, pinned `git show`, and an in-memory
Python SHA-256/baseline/link/whitespace pass. No build/test/Oracle execution,
executable probe, measurement, Git mutation, extra worker or shared-file write.
The only written path is this lease. Some large initial captures truncated;
the algebra and Oracle transformation used here were read in bounded excerpts.

Resource variance: the initial read-only batch launched four simultaneous
short shell commands despite the assigned one-lightweight-process limit;
this was disclosed to the primary. Subsequent top-level reads/checks were
serialized. No long-lived or heavy process ran. Allocated wall limit: 30
minutes; handoff occurs within it. CPU/RAM and cumulative subprocess count
were not instrumented; no compliance beyond these observations is asserted.

Requested routing: `gpt-6.1-sol` / high. `.codex/config.toml` registers prover
and selects Sol/high defaults; `.codex/agents/prover.toml` omits both pins.
Observed runtime model/effort metadata: unknown. No Astra, override effect
or hot reload is claimed. Independent `compiler_referee` review confirmed the
bounded inventory lemma with no blocking or major findings. Its one minor
terminology finding was repaired: Oracle subtraction introduces no new nominal
effect atom, while the resulting payload set may differ from every supplied
payload set. Review does not close the native equation or its source/attachment
premises.
Writes stop at this handoff.

## Commit packet

- Exact completed lease: `notes/theory/2026-10-12-native-negative-residual-equation-proof.md`.
- Baseline: `62864a09433a012f7739dbf49a57535a70979ba6`;
  Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none at the recorded static comparison; complete
  identities below. The primary must recheck before integrating a moving HEAD.
- Claim/review: unreviewed constructive bounded algebra lemma and exact
  missing-operation handoff. No source-qualified H counterexample, native
  residual equation, theorem promotion or production conformance claimed.
- Checks already run: narrow source reads, pinned dependency comparisons,
  whitespace and relative-link check; no execution/builds/tests.
- Proposed checkpoint message: `research: derive native residual payload transformation obstruction`.
- Shared-record deltas left for primary/curator: record §3's input-inventory
  invariant and the missing partial payload transformation; preserve the
  distinct demand tail `t`, attachment/route license and both live emissions;
  retain original OPEN gates. No shared record was edited.

### Frozen direct dependencies

Complete-file SHA-256 values; all Y3 dependency bytes matched the baseline.

| Dependency | SHA-256 |
| --- | --- |
| `.codex/config.toml` | `dae388e4e811c346727ec6688472c7fcf6341ddc5466168cfaa03fdcc0b8e17a` |
| `.codex/agents/prover.toml` | `485a26c7409e16c692ad10095031ab0e7084726ec5da5666082b3bbc4a5daf98` |
| `rules/orchestration-budget.md` | `a0a114b589e8920af8e8fd871d15f63d68b735fc1a553f5a89952b1eab8489e5` |
| `rules/agent-orchestration.md` | `3b1e9c5a083ae4257d3d8ad4bacadf55adf07997d0b02c10bcbec4ccda3258be` |
| `rules/research-lab.md` | `3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69` |
| `rules/design-authority.md` | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` |
| `rules/compiler-engineering.md` | `4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9` |
| `rules/git-concurrency.md` | `2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6` |
| Annotation hygiene integration | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| Attachment/admission design | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| Residual lineage selection | `d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98` |
| Top-level inference principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| Original H note | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| Oracle N/F/R note | `b34465d7132259284389eb04507705239b46b40d6788f70567f3f58447689133` |
| Y3 negative construction bridge | `1a58d1134091e0b91acaf8014baca3a43f72b7764889ff15bbb3c382cd6245e6` |
| Finite residual transition | `4a29e91ed916ecb87584f063e4c5885f7e19cb6a5706357c64e4557bc1ca2893` |
| Negative-filter owner equation | `9052ecb544ae378fe63c958023e564bdf0edc185e18aec74a07a9973f452f9f2` |
| `candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| Oracle `row_effect.rs` | `080472bb5dcb3f724e808ff745c6fba304cc7ea2574b8f8eb3e3466964e937c2` |
| Oracle `machine/bounds.rs` | `c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7` |
| Oracle `lowering/signature_effect.rs` | `9eec35dcbe721cec20b8cab302c409ec0bc014781a36d5287a781a6cb9fe50ce` |
