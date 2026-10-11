# Oracle nested annotation: scheme identity and the quantification boundary

Date: 2026-10-11
Status: frozen, independently reviewed bounded research derivation; original H remains OPEN
Claim class: source-derived transport lemmas, exact selection characterization,
and a minimized unproved source-liveness premise
Primary baseline: `54be89efe7ae5060f72173c88292b1a60437b9bd`
Oracle source baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle checkout: `/tmp/yulang2-oracle-read`
Exclusive lease: this note only; leaf, no delegation

## 1. Frozen objective, scope and dependencies

Governing sources are [annotation policy](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–2, its withdrawn callback result §6, [original H](2026-10-11-oracle-global-effect-hygiene-proof.md)
§1 and generalized-observation premise §5, and [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. The inputs are the frozen [fresh-use source audit](../progress/2026-10-11-oracle-returned-callback-fresh-use-bridge.md)
and [qualified probe](../progress/2026-10-11-oracle-qualified-returned-callback-probe.md).
Their earlier Y3 baselines remain historical evidence pins; neither replaces
this packet's primary baseline. No withdrawn scheme is an expected result.

H retains its original quantifiers: every successfully lowered Oracle program,
each composed-negative concrete annotation occurrence with its original lexical
scope and binders, every actual copy/use, and every actual call/output route.
Its required conclusion is instance-local subtraction, survival of independent
same-family contributions, connected symbolic tails, actual checks for current
and future lowers, and preserved occurrence/attachment/provider/call/residual
correlation through copying and generalization. Incorrect lowers require a real
error and safe nonpublication. Complete Call, soundness and required principality
remain distinct obligations. This leaf neither narrows nor closes H.

The exact leaf input, unchanged from the probe, is:

```yulang
pub act tick:
    pub ping: () -> ()
my f(cb:(() -> (() -> [tick] ()))) = (cb ()) ()
my provider() = \() -> tick::ping()
my observed() = f provider
```

Let `a` be the concrete `[tick]` inside the returned Function in `cb`'s
annotation; `s_a` is the actual ID allocated by that occurrence's paired
constructor, with its inference-arena origin. Let `S_f` be the actually installed
poly scheme, `Q_f = S_f.stack_quantifiers`, and `u` be its actual instantiation
for `r2` in `observed`. The required leaf conclusion is a source-derived
relation from `s_a` to a retained scheme ID `q_a`, its actual selection in
`Q_f`, and the actual freshening relation `q_a -> M_u(q_a)`.
The conclusion requires the original occurrence; existence of an unrelated
scheme ID with family tick does not suffice.
An actual source-derived final scheme omitting `s_a` from `Q_f`, or an actual
copy assigning inconsistent target IDs to its retained occurrences, would
refute this leaf's proposed bridge. Such omission alone would not refute H:
lawful prior discharge or another exported contract would require its own proof.

Shared operational premises are the inspected source bytes, normally completed
owning method calls, fresh allocation without exhaustion, and the inherited
probe's supplied binary/source correspondence. The binary hash verifies bytes,
not build provenance. No premise supplies a compact occurrence, liveness,
`s_a in Q_f`, complete replay or a provider/check correspondence. Numeric IDs,
allocation order and formatter `#0` are not hypotheses. No source restriction,
new route hypothesis, reconstruction layer or semantic decision is introduced.

## 2. The constructor fixes the original ID, but does not select a quantifier

Oracle paths below are relative to its checkout. At
`lowering/expr/lambda.rs:1244–1283`, the actual annotated parameter goes through
`connect_parameter_computation_detailed`. `annotation/constraints.rs:251–280`
sets the parameter Function boundary; `124–138` emits the positive annotation
lower and negative annotation upper on the same parameter value.

For this occurrence, `lower_value_bounds` at `363–389` recursively constructs
the two Functions. Write `b` for the inner Function's actual effect variable
and `E` for the resolved nullary tick family. The concrete branch at `424–470`
and `657–690` emits exactly this original row's views:

```text
W_a = PUSH(s_a, E)
inner positive ret_eff = Stack(PosVar(b), W_a)
inner negative ret_eff = Stack(NegVar(b), filter(E))
inner positive ret     = NonSubtract(Unit, POP(s_a) with filter(E))
declared fact          = (b, s_a, E)
```

The ID occurs in the PUSH and return-value protection; the negative filter has
no ID entry. Registration at `593–599` retains the declared fact. This is a
constructor derivation, not an inference from the dump.

The outer annotated Function has no explicit return-effect row.
`pure_effect_bounds:492–500` supplies bottom/empty-row views and no subtracts.
The Function case returns only its own `ret_eff.subtracts`, so the outer
`connection.subtracts` is empty despite the descendant `s_a`.
`lambda_annotation_predicate_constraints:1581` therefore supplies no immediate
`cb` call predicate from `s_a`; `lambda_parameter_output_predicate_constraints`
also returns empty for a Function annotation. This prevents a spurious
source-to-root POP shortcut. Public/erased callable-upper construction is
guarded by the nonempty immediate call predicate at `1284` onward.

The real source applications at `tail.rs:535–625` generate four-port negative
Function demands, fresh result variables and effect joins for `cb ()` and
`(cb ()) ()`. Annotated `cb` bypasses the unannotated-argument Empty-ID branch
at `tail.rs:740–785`; the second callee is the application result.
Function propagation at `propagate.rs:210–267` forwards the inner positive
Function on the first demand's result-value port, then forwards its weighted
effect port on the second demand's result-effect port. Stack normalization at
`11–24` enqueues the same `s_a` as a left-weight prefix. These are authentic
generation/propagation owners. They show where an `s_a`-bearing bound can enter
the result route; they do not prove every replay was completed or that the
scheme projection returns that bound. No independent provider witness is
selected here.

## 3. Scheme export preserves surviving ID keys without freshening them

There is a concrete transport fact beyond the inherited audit's identity gap:
**finalization does not rename surviving stack entry IDs.**

`generalize/finalize.rs:3–26` clones compact stack weights into the poly arena
before finalizing the predicate, and copies `root.stack_quantifiers` directly
into the exported scheme. The weight clone at `328–350` uses `entry.id` for
every floor, POP and PUSH. It recursively clones family type arguments, but
never allocates a fresh stack ID for these entries. For this nullary E there
are no family-argument binders to infer or remap.

`compact/finalize.rs:586–603` creates principal positive/negative variable
Stack nodes. Its `principal_stack_weight:837–839` calls `with_filter(All)`;
`poly/src/types.rs:326–330` changes only the filter field and leaves the entry
vector unchanged. Induction over the compact structural traversal therefore
gives this local transport lemma:

> Every surviving compact entry with key `s` exported along this path keeps
> key `s` in the poly scheme. The transported identity is the explicit
> inference-to-poly copy edge, not an accidental equality between arbitrary
> arena-local numbers. Export may change filter meaning and structural shape;
> key preservation alone proves neither check preservation nor H.

Thus, if the original `s_a` actually survives the preceding compact pipeline,
its scheme key `q_a` is the intentionally copied key `s_a`; a separate unknown
numeric renaming at finalization is unnecessary. This conditional conclusion
does not assert survival.

## 4. Exact selector and the first missing premise

For the actual compact root/roles presented to the selector, let `V` be its
selected type-variable quantifier set. `generalize/core/stack_ids.rs:23–49`
and `76–179` select an ID precisely when their traversal encounters it in a
nonempty `entry.stack` on a compact variable whose TypeVar is in `V`, in a
covariant position. Function argument ports flip the traversal sign; result
ports preserve it. Recursive bounds and role inputs/associated bounds are
also traversed. This is the actual finite traversal, not a claim that all
annotation IDs are quantified.

`generalize/mod.rs:867–888` additionally selects an encountered ID when the
current subtracts environment's `fact_by_id(id)` resolves to a fact whose
`Subtractability` is `All`. This test does not require declaration provenance;
an internally registered fact can satisfy it. For the original `s_a`, the
concrete nullary E fact resolves to E, so this exception does not establish
selection. A POP-only/protected occurrence is also insufficient for this
concrete ID.

Selection runs after destructive preparation. In particular:

- `analysis/session/generalize.rs:430–547` performs floor-variable cleanup,
  alias expansion, simplification and stack cleanup before final selection.
- The scheme collector uses `compact/collect/mod.rs:848–877`, not raw lowers.
  `constraints/structural_kernel/access.rs:862–900` applies `project_lower`
  to each record and omits `ProjectionDecision::Excluded`.
- `compact/collect/type_nodes.rs:1–99,117–135` distributes carried weight
  through polarity-sensitive Function ports. Its `545–562` negative effect
  case can emit a concrete row prefix and traverse the tail without the
  original stack weight. A family in a row prefix is not an ID witness.
- `generalize/core/prune.rs:39–80,605–629` can remove dead declared IDs;
  `generalize/mod.rs:177–238` removes stray unselected IDs.
- Final installation at `analysis/session/instantiate.rs:54–83` uses the
  ancestor-aware finalizer. `generalize/mod.rs:839–864` again performs
  simplification/cleanup, selects stack quantifiers and prunes unselected
  weights. `core/prune.rs:165–190` may recompute the selected set after pruning.

The first missing mapping premise is consequently:

> For this actual `f` root and original `s_a`, the scheme-projected lower route
> and compact prepasses produce a surviving occurrence with key `s_a` at a
> covariant compact variable in the selector's actual type-variable quantifier
> set, and it remains represented through the installation cleanup.

No executed projected-bound records, compact root, variable-level/substitution
trace or selector input in the frozen evidence establishes that premise.
The local annotation constructor is established; the stopping obstruction is
**projection/liveness and quantifier selection**, including source-bound
coverage at its projection owner. It is not an unsupported annotation grammar
or an unknown finalizer renaming. Normal completion and the printed clean
result do not fill this gap. Absence of that evidence is not a false-mapping
witness or a refutation of H.

The dump's `'b#0[tick]` establishes a formatted stack occurrence. The namer at
`poly/src/dump/type_format.rs:552–588` assigns numbers by encounter within the
scheme; it does not retain the original occurrence or intermediate lower path.
Neither `#0 = SubtractId(0)` nor `#0 = s_a` follows. An inverse uniqueness proof
would require a census of all reachable allocation/copy/weighted-bound routes
before `f` publication; the probe does not supply that census. This packet
stops instead of adopting it as a new hypothesis.

## 5. Actual use map once selection is established

The inherited SCC audit establishes quantification before the `r2` scheme
expansion, rather than before lowering all source bodies. The local target
branch at `analysis/session/instantiate.rs:449–457` calls
`instantiate_scheme_with_roles_and_provenance`; `instantiate.rs:91–103` creates
one fresh instantiator for this use.

At `instantiate.rs:621–647`, every actual member of `Q_f` receives a map entry
before recursive bounds and predicate cloning. `fresh_subtract:741–748`
allocates once for each source key; `clone_subtract:763–768` reuses that entry.
Thus for an established `q_a in Q_f`, every cloned occurrence of that scheme
key uses the same actual `M_u(q_a)`, and distinct quantified keys get distinct
fresh target IDs. Unmapped IDs are reused in ordinary cloning; there is no
claim that every source ID is independently freshened.

`wrap_predicate_with_stack_pops:770–787` adds a root POP of `u32::MAX` for each
mapped quantified key. The freshened graph is therefore more than renaming.
This lemma gives the mapping rule and its owner, not a numeric executed map,
check discharge, preservation under root POP, or the provider-to-output
contribution bridge. It cannot be applied to `s_a` until §4 is discharged.

## 6. Economy audit, checks and frozen handoff

Two different approaches now meet the same premise: forward source
construction/transport and backward interpretation of the formatted scheme.
The latter lacks provenance; the former stops at the actual projected compact
liveness witness. Under `rules/compiler-engineering.md`, H remains required
A/B work. Recovering original identity from formatter output is D reconstruction
debt; preserving actual checks and contribution meaning through projection is
an A/B semantic obligation. The audit does not reclassify or close H.

The constructor already knows `(a, s_a, b)`; the projection/selector knows its
actual records, compact paths and chosen quantifiers; the use instantiator knows
`M_u`. If runtime evidence is required, a primary-authorized bounded capture at
those owners could retain those existing facts without changing inference.
This is proposed evidence work, not implementation or an adopted certificate.
A third equivalent poly dump or freshening-only argument would leave §4 intact.

Checks performed: narrow source reads/searches, SHA-256 snapshot, read-only Y3
and Oracle revision lookups, dependency recheck, leased-note whitespace/fence/
newline integrity. No Oracle call, Cargo/build/test, checker, mutation search,
compiler edit, child launch or Git mutation occurred. Source coverage is the
named constructor/consumer paths; replay completion, compact liveness,
allocation uniqueness, the runtime map, all-source hygiene, complete Call,
soundness and principality remain unverified. Static shell/Python processes
were short and serial; heavyweight process and measurement count are zero.
CPU/RSS were not measured; the 45-minute static bound was not exhausted.
The final integrity script checked all 23 dependency hashes and local links.
`git diff --no-index --check /dev/null notes/theory/2026-10-11-oracle-annotation-scheme-identity-proof.md`
emitted no whitespace diagnostics; exit 1 denotes the new-file difference.

Independent review: a fresh `compiler_referee` found no blocking or major
finding. One minor was repaired by replacing the inaccurate phrase “declared
fact” with the exact `fact_by_id(id)`/`Subtractability::All` predicate; this
text-only correction changes no source premise or theorem scope. The review
covered the frozen artifact at SHA-256
`6c55630c353ebc6e374b2e3430b5ee5028980e3b58970fbfc07d838a452f3826`.

Runtime routing: requested policy target is normal prover Sol/high. The task
identity `/root/oracle_annotation_scheme_identity` is observed; launch model/
effort metadata is unavailable and therefore unknown. `.codex/agents/prover.toml`
omits model/effort pins; reading that file does not establish live settings.
No Astra assignment or reload is claimed. Writes stopped before review.

Next action: primary dispatches the exact §4 compact projection/liveness
premise to its construction owner, with the unchanged original source and
selector inputs; apply the transport/use lemmas only after that premise is
established. If static derivation cannot recover the actual intermediate
evidence, the primary can separately authorize bounded owner capture.

## 7. Dependency snapshot and commit packet

SHA-256 values freeze the actual read dependencies. No dependency was changed
by this worker.

| Y3 authority/evidence path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/theory/2026-10-11-oracle-global-effect-hygiene-proof.md` | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| `notes/progress/2026-10-11-oracle-returned-callback-fresh-use-bridge.md` | `ecb67737991ae18449d903ac2d314c5c0c37744aa916960bee8fd222d2636512` |
| `notes/progress/2026-10-11-oracle-qualified-returned-callback-probe.md` | `7ccf8ef6d31d640585cbfb3e5813d518be57fd8cb1b3139601ea42d394d61bd2` |
| `notes/progress/2026-10-11-oracle-operation-path-source-audit.md` | `a39b7ff03f7358e31ce811c5e1d933bdfcb06b6de8c477590aecb87a37178819` |

| Oracle path | SHA-256 |
| --- | --- |
| `crates/infer/src/annotation/constraints.rs` | `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db` |
| `crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| `crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `crates/infer/src/constraints/machine/propagate.rs` | `8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086` |
| `crates/infer/src/constraints/structural_kernel/access.rs` | `ad90bc1444be22df6080c7131ef49fedace884178c375af84ecb09416b38740f` |
| `crates/infer/src/compact/collect/mod.rs` | `828fa02521e2426297a9369df2fd9ef1560b7403a668ddfe881063ef16bdfd40` |
| `crates/infer/src/compact/collect/type_nodes.rs` | `96dc38a9a05c447f019bb0421e0b37057d283026ba87bce121bb33959b0d8ab2` |
| `crates/infer/src/compact/finalize.rs` | `53a2452b109ddb461d98f6124d410fa2e771e700e272084f3b83ed87b4f3d272` |
| `crates/infer/src/analysis/session/generalize.rs` | `ed946b9ffb15f40c1fd721d8b2cb0907a6540c21d0bf690f784577307660e64a` |
| `crates/infer/src/analysis/session/instantiate.rs` | `bf21175f47df78f35f2070fea51b3483d59a91ac4a606bace9e24f32878c2d19` |
| `crates/infer/src/generalize/mod.rs` | `03bfda4e4997347b59483de96eca652b67477639fc363e0890d546d2cf36fcef` |
| `crates/infer/src/generalize/core/stack_ids.rs` | `adb9cd35d483af62ea0c3ebc572b9a0535761f3bfb99aedad49b371833b95f8f` |
| `crates/infer/src/generalize/core/prune.rs` | `05e6d343c90f1bbc77def8e50f9acb746451ceb3889bb50dd17342621afba26d` |
| `crates/infer/src/generalize/finalize.rs` | `a8e5a1c8e6ad57d1fac7e25a1ab6a329093e5c76e6d84c0625c124c349f07492` |
| `crates/infer/src/instantiate.rs` | `876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c` |
| `crates/poly/src/types.rs` | `9211e62291b82e71e1b78763b83fe9f1d81e0fe4396d9e12d42e9a4a9b13b47c` |
| `crates/poly/src/dump/type_format.rs` | `49800841ea8059b007076b8018076baa91ae275c76f3f07eb24a57341fe35bd7` |

- Exact changed lease: `notes/theory/2026-10-11-oracle-annotation-scheme-identity-proof.md`.
- Baseline: Y3 `54be89efe7ae5060f72173c88292b1a60437b9bd`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; recheck the frozen table before integration.
- Review status: bounded identity/finalization and selector/use facts passed
  independent review after a primary-closed minor wording repair. Exact
  source-qualified compact survival/selection and H remain OPEN.
- Checks already run: source inspection, hashes/revisions, dependency and note
  integrity; no execution/build/test or Git mutation.
- Proposed checkpoint message: `research: isolate Oracle annotation compact liveness premise`.
- Shared-record deltas left for primary/curator: record intentional ID retention
  at finalization, distinguish it from fresh use allocation, retain the exact
  projected compact/liveness selection premise and exhausted Oracle budget;
  preserve H and downstream observation gates OPEN. No shared record edited.
