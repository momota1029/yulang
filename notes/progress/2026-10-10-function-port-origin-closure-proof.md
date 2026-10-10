# Function-port origin closure: conditional constructive derivation

Date: 2026-10-10
Status: independently reviewed conditional derivation; exact-row separation
within the inspected generation/transport scope, with authentic origin
qualification still open; no universal lifecycle theorem closure
Baseline: `9d4392ef4a4ef309c6c9c9194840deca3cbf6de6`
Branch supplied by primary: `research/simple-sub-intrusion`
Lease: this new note only
Method: constructive allocation invariant and its operational preservation;
no executable replay model, accepted fixture or production modification

## Authority, statement and equality

Authority is the approved contextual attachment/admission design §§3–7,
especially §4's exact inferred-entry certificate and Function operations,
and §5's complete generated component requirement. This work does not change
that gate or the selected two count relations. It applies the `yulang-proofs`
skill under the primary's explicitly bounded fallback assignment. The
repository registers `prover`, but this leaf does not claim that custom role
ran. Requested routing was `gpt-6.1-sol/high`; independently observable runtime
model/effort metadata were unavailable, so effective settings are unknown.

Fix one live authentic Lambda slot-3 origin `o`, originally allocated with
distinct Effect rows `E_o` and `T_o`, and its exact source relation
`E_o <: T_o`. Quantify over finite reachable live states of the frozen native
source generation routes inspected below, including repeated capture/freshening,
extrusion, qualifying intrusion and rollback of those routes. A negative
Function occurrence means its own stored four fields, not a Function selected
by ancestry, an SCC, or a written name. Source generation excludes direct test
construction and injection of arbitrary private arena objects. The source
enclosure premise includes correctly polarized source tasks and selected bound
slots: lower structural operands are positive, upper structural operands are
negative. The generic constraint-store admission at `lib.rs:3731–3746` checks
kind/ownership, not this polarity property. A complete all-source bridge must
therefore establish it from source generation, rather than assume public store
admission establishes it.

For a comparison with a positive Function whose Effect fields are `E` and `T`,
the constructor at `lib.rs:12023–12049` gives

```text
ArgumentEffect / Swap:    U_arg <: E
ResultEffect / Preserve:  T <: U_ret
```

Both children have the exact reverse pair `T <: E` only if
`U_arg = T` and `U_ret = E`. The central result below excludes either equality
when `E/T` are the original authentic ports or ports transported by a coherent
map of their owning rows. It does not establish the completeness of a future
authentic-origin recognizer.

Keep three equalities distinct:

1. **Raw equality:** the same row ordinal in the same live allocation state.
   A rolled-back ordinal is not a surviving allocation identity.
2. **Canonical equality:** `intrusion.effect_rep` returns the same live
   representative. Extrusion copies may differ raw while agreeing canonically.
3. **Semantic mutual subtyping:** both constraints hold. This neither changes
   a row ordinal nor creates a forest union. The argument below concerns the
   first two notions only, and makes no semantic separation claim.

## Constructive invariant

Use a ghost tag `L` for the two rows born at each actual
`admit_lambda_fact` entry/return allocation, and `O` for independently born
source/component/annotation/operation/Apply rows. A row copied by extrusion or
freshened from a captured source row inherits that source row's tag. These tags
are proof annotations on existing allocation events, not proposed compiler
metadata or a new language distinction. In particular a fresh row allocated
for a generic use receives the source tag, rather than being classified from
the allocator's generic `Fresh` metadata.

The joint invariant is:

```text
(I1) Every live row has one tag, L or O.
(I2) Every recorded Effect copy/parent pair has equal tags.
(I3) Every Effect representative class is homogeneous in its tag.
(I4) Every own Effect row field of every source-generated negative Function
     has tag O. Its non-row Effect fields remain non-row endpoints.
(I5) Original authentic Lambda entry/return rows, and coherently transported
     copies/fresh instances of those coordinates, have tag L.
```

`I4` is about fields, not about the rows reachable through bounds on those
fields. Such bounds may connect `O` and `L`; no separation of constraint
components is asserted. Maintain the auxiliary source premise that exact
lower/upper structural bounds have their selected side's polarity. The tag
intentionally distinguishes allocation classes,
not individual Lambdas, uses, annotations or effect families.

### Birth cases and negative producers

Collected Effect components are allocated before fact admission at
`lib.rs:9952–9993`; their live-component positions receive independent dense
ordinals. `fresh_effect_at_level:10092–10121` appends a new live row. Lambda
admission allocates its two rows separately at `:11155–11160`, authenticates
only slot 3 at `:11174–11206`, and constructs a **positive** Function at
`:11224–11229`. Thus an `L` birth does not directly construct a negative
Function. The computation components used by source Apply and Lambda recipes
remain their previously allocated components, rather than those new ports
(`candidate_source.rs:369–386`, `:420–434`).

The source-relevant callers of `negative_function_term`, together with the
only direct arena caller, were searched at the frozen revision. Inline test
modules were distinguished from runtime callers. The constructor in
`term.rs:1147–1165` validates the kinds/polarities and interns exactly the
supplied fields; it does not substitute another row into a port. Its only
direct `.negative_function` caller in the solver is the wrapper at
`lib.rs:10187–10195`; the separate closed-type finalizer is discussed below.
The actual producer premises are:

| Producer | Field source and tag justification |
| --- | --- |
| Signature/annotation and nested operation signature (`candidate_effect.rs:1254–1299`) | Fields are computed from signature syntax by `candidate_signature_effect`. Scoped symbolic tails are first allocated independently at `:843–855`; operation variable maps begin empty at `:650–663`; annotation maps begin empty at `:1063–1065` and local annotation lowering at `:993–1014`. Singleton contravariant tails are these same `O` rows (`:1383–1393`); covariant checking/support ports are independently fresh `O` rows (`:1351–1361`, `:1422–1432`). Bottom/empty leaves are non-row endpoints. Recursive signature descent reverses polarity/variance explicitly; it does not read a Lambda's live ports. |
| Paired formal annotation (`candidate_effect.rs:907–934`) | Omitted Effect fields are independently fresh; singleton named fields reuse only the annotation-owned table above. Positive and negative interfaces may share their **own** `O` row, including repeated names. `:939–971` installs these interfaces around a Value parameter, without assigning an existing Lambda Effect row to the annotation table. The false stronger claim that all negative fields are fresh wrappers is unnecessary. |
| Apply checking demand (`shadow_apply.rs:1327–1358`) | Argument Effect comes from a collected argument computation component, hence `O`; invocation result Effect is independently fresh at `:1342`, hence `O`. It is different from the application's computation row. In the non-graph branch these fields are bottom/empty leaves. |
| Closed-type import (`lib.rs:15407–15445`) | A negative Function is accepted only with bottom/empty Effect fields, then reconstructed using those leaves. This route cannot import a live `L` row. |
| Extrusion and scheme reconstruction | These preserve the original Function polarity and each field position, and map each row from that same field; preservation is proved below. |

Operation signatures can contain negative nested Functions even though the
operation's top-level signature is constructed positive. They are covered by
the recursive signature case, not omitted as positive-only operations.
Closed finalization at `lib.rs:16362–16369` uses bottom/empty Effect fields;
it does not reintroduce a transported live port. Recursive Value binders do not
change this import rule.

This is more than an endpoint-shape argument: field sources, allocation-table
insertions, initial component identity and the sole structural constructor are
the premises establishing `I4` at birth. Search evidence supplies the bounded
constructor inventory; the following induction supplies lifecycle preservation.

### Extrusion and stored bounds

`candidate_extrusion.rs:73–123` keys visits by canonical endpoint, polarity and
target level. It either returns the same row or allocates a fresh copy of that
exact endpoint, then records its parent. Assign the copy its parent's tag;
this proves `I1/I2` for every new pair, including opposite-polarity copies of
one row. The actual production entry callers at `lib.rs:11944–11969` pass
Positive for a lower operand and Negative for an upper operand. Selected row
bound traversal keeps that side at `candidate_extrusion.rs:128–162`;
`candidate_apply_value:700–707` inserts lowers on Positive and uppers on
Negative. Copy/merge transfers preserve bound sides and fresh capture restores
the captured side. These give local preservation of the auxiliary polarity
premise. They are essential: reconstruction chooses its Function polarity from
the visit key `p`, and does not independently require that it matches the
original structural endpoint. The Function children at `:224–250` retain argument/result positions
and their required polarities. Reconstruction at `:323–350` uses the same
polarity and `[argument, argument_effect, result_effect, result]` order. Hence
an `O` negative field remains `O`; no positive Lambda becomes a negative
Function through extrusion.

Bound insertion and replay may connect different tags. They store constraints,
not forest unions. `candidate_apply_effect:724–747` canonicalizes endpoints,
selects the level-directed bound side and replays; it never assigns a forest
parent. Effect-view remapping at `:258–291`, incoming allowance copying at
`:293–305` and copied-bound insertion at `:307–321` likewise move or retain
operands/bounds without filling new negative Function fields from them.
An Allowance/Support tail is not the Function field's raw endpoint.

### Qualifying intrusion and canonicalization

The only production caller of `retain_extrusion_parent` found in this scope is
the extrusion allocation above. Retention initializes new forest entries to
themselves (`candidate_intrusion.rs:171–219`). SCC edges include stored bounds
and Function ports, and may pass between tags; membership alone does not merge
all rows in a component. The merge list at `:477–486` contains only actual
recorded copy/parent pairs. By `I2/I3`, the representatives of both sides have
the same tag. `merge_candidate_rows:524–582` canonicalizes the pair again and
sets only that copy representative to its parent representative. It preserves
`I3`, even when earlier merges in the same batch change representatives.
Path compression (`:304–355`) shortens existing same-tag paths.

Transferring both bound sides and their origins (`:547–572`), canonicalizing
third-owner bound incidence (`candidate_context.rs:1581–1597`) and replaying
the Cartesian combinations (`candidate_intrusion.rs:597–602`) do not create an
additional forest equality. The search for Effect forest assignments found
this merge, restoration during rollback and path compression; no union of two
independent source rows was found. `lib.rs:11334–11339` consults this forest for
Effect canonicalization. Therefore `L` and `O` can never be canonically equal
through this route, even if their constraints are mutually satisfiable.

### Scheme capture, local/module fresh uses and import

Capture canonicalizes an endpoint at `candidate_scheme.rs:177`, and interns
row identities through `intrusion.rep` at `:188–191`. By `I3`, this does not
change tags. Function capture at `:345–400` records the actual polarity and
field order; it neither dualizes an inferred positive Function nor constructs
a checking interface from one. Capturing the reachable bounds may add nodes
of either tag without making their fields identical.

Freshening at `:840–851` canonicalizes each captured source row. Within one
use, `canonical_rows` reuses the result for the same source representative.
Otherwise it retains that source or allocates one fresh row for it. Give each
new row its source's tag. Two differently tagged representatives cannot share
the lookup key by `I3`; independent fresh allocations cannot share an ordinal
in the live state. An unchanged old anchor cannot equal a new allocation.
Thus the map preserves tag separation across generic/non-generic and
old/local boundary choices, with no assumption that all ports are generic.

`Node::Row` reconstruction at `:969–972` reads that map, and Function
reconstruction at `:973–989` preserves the recorded polarity and four slots.
Every reconstructed negative Effect field is still `O`. Restoring captured
bounds at `:995–1032` can induce additional comparisons; the only ways to
construct Functions or change row representatives remain the already proved
cases. This closes preservation under repeated uses, rather than only one
capture of one Lambda. Module fresh-use routing at `:1038–1084` and local
use-time capture/freshening at `:1116–1142` call this same mapping owner.
The closed-type route above accounts separately for imports through finalized
schemes; its empty Effect fields do not share the live map.

### Rollback and lifetime

Rollback restores prior forest parents and truncates retained parent pairs
(`candidate_intrusion.rs:103–114`), context origins/inferred-entry records
(`candidate_context.rs:763–782`, `:823`), route records
(`lib.rs:9310–9318`) and fresh rows (`:9403–9411`). The term owner removes newly
interned nodes and truncates pages (`term.rs:708–723`). Restoring a prior state
restores its ghost tags; discarded allocations do not remain quantified live
objects. A later reused ordinal receives its new allocation's tag. This is
the narrow rollback preservation needed by the row argument, not a proof of
the entire approved transactional/certificate contract.

### Consequence

By induction on the inspected real allocation, reconstruction and forest
operations, `I1–I5` hold under their source enclosure, correctly polarized
source-state and live-handle premises.
For any negative Function `U`, each own row port has tag `O`, while `E/T` have
tag `L`. Homogeneous canonical classes imply

```text
canon(U_arg) != canon(T),     canon(U_ret) != canon(E).
```

If a field is a bottom/empty/non-row endpoint, it is also distinct from an
EffectRow by endpoint variant. Therefore the displayed dual reverse-child
collision is excluded for original exact ports and coherent row-map instances.
Raw equality is excluded as a consequence of canonical inequality. No effect
interpretation, operation execution, finite fixture enumeration or SCC
separation premise was used.

## Authentic origin transport: reduced unresolved premise

At the original owner, authenticity is explicit: `retain_inferred_entry`
stores original Lambda, endpoints, occurrence and cause
(`candidate_context.rs:462–474`); `candidate_context_seed:1319–1354` attaches
the supplied handle to the exact canonical relation. Ordinary admissions pass
`None` (`lib.rs:11803–11811`). Authentic source endpoints therefore satisfy
`I5`; matching a slot number or pair is not needed to prove their birth.

Later **ancestry** is a different object. `candidate_context_bound:1473–1495`
records a Derived parent/child relation, `candidate_transfer_bound_origins`
(`candidate_effect.rs:436–465`) transfers attached relation origins, and
extrusion/intrusion use that transfer at the sites above. Equality transport
canonicalizes actual bound endpoints. Fresh transport at
`candidate_scheme.rs:1018–1024` passes a captured bound's reconstructed
endpoints, original relation ID and one context-use identity to
`candidate_context_fresh_transport:1601–1609`. The latter retains
`Transport { parent, child, use_origin }` and attaches the child to that bound.
It does not retain a newly authenticated inferred-entry record with renamed
entry/return fields. `Origin` and `InferredEntryOrigin` stay distinct records
(`candidate_context.rs:59–72`, `:155–159`); their comments explicitly describe
them as inert construction evidence with no authorization consumer.

Thus the row induction does **not** imply this missing premise:

> Every relation qualified as a transported authentic inferred-entry flow is
> the image of that exact slot-3 seed's two endpoints under the same relevant
> row transport, and qualification excludes ordinary Derived/Replay/port
> descendants that merely have that seed among their ancestors.

The precise seam is the future qualifier/consumer of the original origin plus
Derived/Replay/Transport ancestry, not an unproved assertion that SCC intrusion
merges arbitrary owners. A captured bound's `relation` is provenance; its
captured lower/upper nodes are the actual bound endpoints. They must not be
silently identified with the original seed endpoints from ancestry. The
fresh-use route retains a graph and its row vector, which may support a
correspondence proof; absence of a typed seed-renaming consumer here is not a
claim that all retained data are insufficient. Any such proof must establish
the qualification rule and follow the actual route, rather than choose an
arbitrary `Transport` descendant or an origin somewhere in the component.
The separate source-enclosure premise above also remains conditional at the
whole-source boundary: this leaf proves preservation by the inspected owners,
but has not supplied an exhaustive frontend/module source-admission proof of
correct initial task polarity. Passing a PositiveFunction to negative
extrusion is a private-call falsifier of that premise, not an accepted source
constructor or a production bug. It must not be used to claim the induction
covers arbitrary private API calls.

Two proof approaches were used. A per-allocation-root ancestry proof establishes
original separation but needs per-use seed maps after freshening. The coarser
two-tag operational induction above removes that row-owner reconstruction
burden and covers transport separation. Both leave authentic **relation
qualification** untouched. No third equivalent attempt was launched.
Under `compiler-engineering.md`, that qualifier seam is reconstruction debt
(D) if consumers recover owner flow solely from ancestry, with a real
safety/correctness obligation (A) wherever it licenses `both`. This audit
does not weaken the approved certificate requirement or introduce metadata.

No minimized source constructor violating the tag invariant was found. The
starting detached port witness remains conditional: it can be manually built
using private constructors, but that is not the source route proved above.
The note does not discharge general origin hygiene or prove that every future
authentic qualifier will choose only coherent maps.

## Checks, frozen dependencies and limitations

All compiler reads used `git show <baseline>:<path>` followed by bounded
`rg`, `nl -ba` and `sed`. Read-only `git grep` checked
`negative_function_term(` / `negative_function(`, direct
`.negative_function(` callers, `retain_extrusion_parent(`, Effect forest
assignments, initial/fresh row appends, live-component changes and inferred
origin writers. Test-directory exclusions still expose inline test modules;
these were identified by their module boundaries and excluded from source
producer claims. `git ls-tree` supplied blob identities. Output-limited locator
searches were not taken as proofs of arbitrary frontend/call-graph completeness.

There were no Cargo commands, tests, builds, benchmarks, executable checkers,
parser runs, Oracle runs, mutations, random seeds, child agents or Git mutations.
At most four lightweight read commands were batched; no heavyweight process
ran. CPU affinity, peak CPU/RAM and total wall time were not measured. This
was one leaf assignment and two bounded constructive proof approaches.
No production/model configuration was changed. Independence/review is absent.

The source-reachability input note is absent from the baseline commit, so it
was read as the primary-supplied frozen working-tree input, separately hashed:
SHA-256 `f5ec989cca8a777faaf00c47ecfd18db985154c5a4c74b700315a91ecff5df63`.
Its conclusions are locators/prior assumptions, not a replacement for the source
reads establishing this derivation. Baseline blobs are immutable; current HEAD
and working-tree dependency equality remain the primary's integration check.

| Direct frozen dependency | Git blob |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `1b036291c8c52a5723f070d80ac655f6355e5629` |
| `crates/yu-solver/src/term.rs` | `ec5371430a89abb576b4ee2a78a49c2481553781` |
| `crates/yu-solver/src/candidate_source.rs` | `dbc3ee822a61b4a861597f07654c52cacb8fb92d` |
| `crates/yu-solver/src/shadow_apply.rs` | `3578b31f3d0607f6c71b9fbf6e05e5b1085961b2` |
| `crates/yu-solver/src/candidate_effect.rs` | `57ec353d69e0c59d86434b6ed21c692aaac6da33` |
| `crates/yu-solver/src/candidate_context.rs` | `ac646a46dd687e4d56bcd09887545f91de32391d` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `4dc6dfef0203bd1bcf2bba2380008d58ffe114ac` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `7a750da800199c23d998bc2da23015256c4f265f` |
| `crates/yu-solver/src/candidate_scheme.rs` | `005ca3ccaf2fcfba3284a76168d7e8ba7a165666` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `c99873544ca90aa817c77941514f7868a8023d65` |
| `notes/progress/2026-10-10-entry-circuit-source-falsifier.md` | `224490ac364e41bfa548c7a0488214afcb15e974` |

No complete generated circuit, executable PUSH/Swap, complete Call behavior,
full effect hygiene, soundness, principality, accepted source fixture or
successful publication was established. Current operation labels remain inert
(`candidate_context.rs:114–115`); this row argument gives no permission to omit
either labeled incidence or authenticate a whole component from one origin.

Recommended next action: independently challenge the frozen allocation/forest
preservation argument, then require the origin consumer's exact qualification
contract before using the conditional exclusion as universal lifecycle evidence.

Commit packet: exact leased path
`notes/progress/2026-10-10-function-port-origin-closure-proof.md`; baseline
`9d4392ef4a4ef309c6c9c9194840deca3cbf6de6`; changed frozen dependency hashes:
none; separately supplied source-reachability input hash recorded above;
current integration equality unverified. Review: independent compiler-referee
PASS for the exact frozen artifact hash. The review checked the source-enclosure
premise, tag preservation through baseline extrusion/merge/capture/rollback
owners, and the distinct unresolved transported-flow qualifier. It did not
review exhaustive frontend polarity, future `both` authorization, operation
execution, general mixed-component admission, full route transactionality,
soundness/principality, or production correspondence. Checks: frozen static
reads and baseline blob inspection only. Proposed message:
`research: derive conditional Function-port owner separation`.
Shared deltas left for primary/curator: distinguish operational row separation
from authentic transported-flow qualification; keep universal origin closure
and the approved certificate gate open. No task/index/theory/authority/question
bundle edit is proposed here. All writes stop at this frozen artifact.
