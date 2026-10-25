# R30 primary source/authority result — paper value guard boundary

Sprint: `PAPER-GUARD-CONSTRUCTOR-AUTHORITY-20261026/r30`, r1

Baseline: `f7a8ade138d1abec51a204b36fe5e4b06f856ce9`

Contract SHA-256: `77d1512967f84808ea7bffe1a488e3b2d34b4aaa50ea3475a3753aa99236a3b6`

Primary: `/root`; complementary author: `/root/r30_source_researcher`

Claim class: bounded source characterization and exact missing rule. No new theorem, semantic decision, or production authority.

## Disposition

The paper gives a prose guard criterion and a finite graph typing judgment, but
does not give a constructor-indexed graph-edge/guard judgment for its complete
value grammar. The first unresolved constructor after the cases the paper
classifies is `wrap`. Its typing rule and call-entry behavior do not say whether
the recursive graph observation stops at a wrap, follows its function child, or
how references in adapter computations participate. Thus this audit yields an
exact blocker, not a complete classification and not closure of the parent
guard theorem.

Keep `GVG-FORMS-1`, `B-PAPER-1`, `B-OBSERVE-1`, graph extension, source/native,
A/B, and production gates OPEN. R29 remains accepted only for finite heap
payload allocation. No code or semantic change is authorized by this result.

## Frozen evidence and independent primary check

The operative source is the unreviewed research manuscript
`docs/yulang-operational-type-safety-ja.tex` (O). The source manuscript
`docs/yulang-source-type-safety-ja.tex` (S) has its own source grammar and does
not silently decide O's operational graph edges. The Lean module is a raw syntax
encoding, not a guard definition.

| Input | SHA-256 |
| --- | --- |
| O, `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| S, `docs/yulang-source-type-safety-ja.tex` | `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166` |
| `PaperExecutionSyntax.lean` | `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932` |
| `PaperFreshHeapAllocation.lean` | `7cd87b8e5fd43eea0206401de6ed91e817755f3d1ad2c5aeee1caf0dd1732925` |
| researcher handoff, this sprint | `6c1717c0de5861d6e14c0a931af60bee8d10866546ca2fd76a06b57ecea800a6` |

Primary reread: O `:151–165,184–185,215–240,258–268,362–376,485–494,995–1008`;
S `:133–135,1043–1068,1081–1084,1104`; Lean syntax
`PaperExecutionSyntax.lean:39–63`. The manuscript hashes match the r1 contract.
The exact row evidence and minimal discriminator below were independently
checked against those frozen bytes; accepted HigherOrder/finite-guard results
were not used to fill a paper rule.

## Constructor inventory and source status

Here “barrier” means the observation stops at one retained value constructor
while references in its payload/code remain available for later observation.
“Candidate transparent” is not promoted to a paper theorem without an explicit
edge rule. The inventory has all 20 `Value` constructors; lambda is split into
its two modes, giving 21 rows. Child positions refer to the raw Lean encoding.

| Constructor | Value/code positions relevant to recursion | Source-grounded status | Evidence required to observe the typed value | Paper decision? |
| --- | --- | --- | --- | --- |
| `variable` | Binder index; no syntactic child; may denote a recursive binder before substitution | Alias, not a genuine barrier; O says alias-only cycles do not construct a value (`:184–185`), closed lookup/substitution is described at `:258–260` | Gamma lookup (`:215`), simultaneous substitution and binder-to-reference correspondence | Alias-only exclusion is explicit; exact syntax-to-edge map is not |
| `graphReference` | Heap lookup target `H(r)` | Follow reference; O defines finite graph observation and reference typing (`:260–268`), and shape proof reaches a constructor after finite guard-preserving alias movement (`:1002–1008`) | `Xi(r)=A`, typed immutable lookup and the missing finite guard descent | Following a reference is explicit; guard descent is the open parent |
| `literal` | None | Terminal base value; O `:151,215` | Matching base introduction (`:215`) | No recursive position; terminal |
| `tuple` | Every element | Genuine data-structure barrier, supported by grammar and introduction rule (`:151,184,216,260`) | Ordered component typing and arity (`:210,216`) | Broad data classification supported; no formal edge function |
| `sequence` | Every element | Genuine data-structure barrier (`:151,184,217,260`); sequence is finite | Fixed native List identity, element typing, finite length (`:217`) | Broad data classification supported; no formal edge function |
| `record` | Every present field payload; label/presence are not values | Genuine data-structure barrier (`:151,184,218,260`) | Required labels, declared-label bounds and each present payload (`:218,1007`) | Broad data classification supported; no formal edge function |
| `variant` | Every payload; type arguments are not value children | Tagged data barrier (`:152,184,219,260`) | Constructor/tag, arity, payload typing (`:182,219`) | Broad data classification supported |
| `nominal` | Every payload; type arguments are separate metadata | Nominal data barrier (`:152,184,220,260`) | Same declaration/constructor and instantiated payload template (`:126–130,220`) | Broad data classification supported |
| `lambda(value)` | Computation body and nested references; parameter is bound | Explicit lambda/code barrier (`:153,184,302`) | Body typed under `x:A`, profile/receipt retained (`:160,222`) | Yes for lambda; capture correspondence is separate |
| `lambda(computation)` | Same body positions; parameter has thunk type | Same explicit lambda barrier (`:153,184,302`) | Body typed under `x:UA` and mode retained (`:223`) | Yes; mode does not change the stated criterion |
| `delay` | Computation body and nested references | Explicit delay/code barrier (`:153,184,302`); no termination claim | Body typing (`:221`) and closed code/captured refs (`:264`); forcing may run it (`:307`) | Yes |
| `wrap` | Function `Value`; argument/result adapter `Computation`s with nested references | **First unresolved.** O typing rule (`:224`), call-entry peeling (`:366–376`), and callable shape (`:1005`) do not decide whether it stops, follows the function, or how adapter-code references count | Inner/outer callable types, each adapter under its specified binder (`:224`), plus a graph observation rule and capture evidence | **No** |
| `typeAbstraction` | Body `Value`; introduces a type binder | Type-evidence-only cycles are excluded (`:185`); intro is at `:238`. Candidate follows the body, but exact edge judgment is absent | Fresh type binder, body typing and substitution (`:238`) | Evidence-only exclusion is explicit; no complete child-edge rule |
| `typeApplication` | Function `Value`; type argument is not a value child | Outer elimination is administrative (`:493–494`; normalization `:316,321`); candidate follows/instantiates the function | Polymorphic typing and simultaneous substitution (`:238,1003`) | Administrative status explicit; graph transition for nested applications not defined |
| `injectLeft` | Payload `Value` | Candidate injection/data barrier (`:155,184,233`), but the text also describes union view/evidence (`:137–139`); do not promote from the generic phrase alone | Left payload typing and retained union alternative (`:233`) | **Not explicit constructor-by-constructor** |
| `injectRight` | Payload `Value` | Same ambiguity and evidence (`:137–139,155,184,233`) | Right payload typing and retained union alternative | **Not explicit constructor-by-constructor** |
| `both` | One underlying `Value`; paper typing has two derivations for that same raw value | Not a data barrier on current evidence; candidate follows underlying value. O identifies the two proofs as evidence (`:140,234`) and `choose` removes evidence (`:314`) | Both derivations of the identical raw value at `A` and `B` (`:234`); the raw syntax node itself stores only one `Value` | Evidence status supported; graph edge rule absent |
| `roll` | Underlying `Value` | Explicitly cannot guard by itself (`:185`); unroll is its inverse (`:235,315`); candidate follows the payload | Payload at unfolded type and matching roll/unroll types (`:235`) | **Nonbarrier explicit**; typed traversal rule still needed |
| `topView` | Underlying `Value` | Erasable/top evidence (`:142,236`) and type-evidence-only cycles excluded (`:185`); candidate follows underlying value | Underlying `v:A`; there is no unchecked payload eliminator from `Top` (`:236`) | Nonbarrier evidence; no complete graph rule |
| `view` | Underlying `Value`; metadata contains type/identity data, not a value child | Metadata preserves underlying constructor (`:239,489–494`); outer removal is administrative (`:490–494`); candidate follows underlying node | Underlying typing, path/view metadata and preserved type/constructor | Constructor preservation explicit; graph proof rule absent |
| `continuation` | Computation body with response term binder and owner binders; nested/captured references | Runtime raw constructor (`:163,350–354,1006`), but guard criterion (`:184,260`) does not name it. Similarity to lambda is not authority | Body under response type, owner binder scope/freshness (`:350–354`), captured-reference typing; S `:1104` only supplies saved environment coverage | **No** |

Additional representation limits: Paper `both(v;d1,d2)` stores two derivations,
while `PaperExecutionSyntax.Value.both` stores one `Value`; any full paper proof
must retain both typing witnesses outside or enrich that representation under
proper authority. The paper's `wrap` adapter code and continuation bodies can
contain references, so treating every syntactic nested occurrence as an eager
heap edge is also unsupported.

## Concrete falsifiers and discriminators by constructor

These are small symbolic graph shapes for testing each asserted status against
an eventual constructor-indexed guard rule. They are **not** results of such a
rule, and the open manuscript does not currently adjudicate all of them. For a
claimed barrier, the contrary outcome “this cycle is not guarded by that node”
would falsify that classification. For a candidate transparent edge, the
contrary outcome “the graph rule stops at that wrapper” would falsify the
candidate. Type annotations below are schematic; a witness is admitted only
where the paper's displayed typing premises can be met.

| Constructor/status in this report | Concrete witness | Observation that would falsify the stated status |
| --- | --- | --- |
| `variable`, alias | Two recursive bindings `x=y; y=x` with no value introduction | If either variable lookup itself counted as a barrier, the explicit alias-only-cycle exclusion O `:184–185` would be violated. If these names do not map to reference edges under the paper's closure convention, the syntax-to-graph alias classification needs its missing bridge. |
| `graphReference`, follow edge | `H(r)=graphReference(s); H(s)=graphReference(r)` | If one reference lookup terminates observation or makes this alias-only cycle guarded, the claimed follow-through-reference behavior is false. |
| `literal`, terminal | A literal node `H(r)=literal(c)` | If a pinned `Literal` form has a `Value`/code reference child, or observation follows a child from this node, the terminal classification is false; current `Literal` constructors have no such field (`PaperExecutionSyntax.lean:19–27`). |
| `tuple`, data barrier | `H(r)=tuple([graphReference(r)])` | If the guard rule rejects this one-node cycle specifically because tuple payload is not guarded, tuple is not a barrier. |
| `sequence`, data barrier | `H(r)=sequence([graphReference(r)])` | If the guard rule rejects this cycle specifically at the sequence payload, sequence is not a barrier. |
| `record`, data barrier | `H(r)=record([(l, required, graphReference(r))])` for a declared required label | If a present field payload does not lie below a data guard, record is not a barrier; an absent optional field must not be mistaken for an edge. |
| `variant`, data barrier | `H(r)=variant(K, args, [graphReference(r)])` at a declared constructor/tag and valid arity | If the guard rule refuses this payload cycle despite the matching data introduction, variant is not a barrier. |
| `nominal`, data barrier | `H(r)=nominal(D,K,args,[graphReference(r)])` with `K`'s declared payload template | If the instantiated nominal payload does not guard the cycle, nominal is not a barrier. |
| `lambda(value)`, code barrier | `H(r)=lambda(value, profile, x, call(graphReference(r), delay(ret(x))))`, with `r:C(A,B)` and `x:A` | If inspecting the node executes/unfolds the body before recognizing the lambda guard, or the rule rejects this well-typed recursive-call cycle for lack of the lambda guard, the classification is false. |
| `lambda(computation)`, code barrier | `H(r)=lambda(computation, profile, x, call(graphReference(r), x))`, with `r:C(A,B)` and `x:UA` | Same falsifier as value mode; a mode distinction that removes the lambda guard contradicts O `:184`. |
| `delay`, code barrier | `H(r)=delay(force(graphReference(r)))`, with `r:UA` | If observing the thunk forces its body before recognizing the delay guard, or this well-typed cycle is rejected for lack of a delay guard, the classification is false. This does not assert that a later force terminates. |
| `wrap`, unresolved | `H(r)=wrap(graphReference(r), idArg, idResult)`; separately, put `r` only in deferred argument-adapter code around a lambda | The first shape distinguishes stop-at-wrap from transparent function traversal. The second distinguishes a function edge from captured/deferred code. Either paper outcome would resolve the gap; neither is assumed here. |
| `typeAbstraction`, evidence-only candidate | A recursive type-evidence spine whose only repeated occurrence is under `Λα` | If the paper guard accepts a cycle composed only of type abstraction evidence, the candidate nonbarrier reading from O `:185,238` is false. Exact typed witness depends on the missing graph/type relation. |
| `typeApplication`, administrative/candidate transparent | `(Λα.v)[A]` where the repeated occurrence is exposed only after the administrative application step | If the stated outer normalization leaves a distinct guarded constructor or does not expose the abstraction/body as O `:316,321,493–494` indicate, the candidate traversal is false. This tests normalization, not a rule for arbitrary graph cycles. |
| `injectLeft`, candidate data introduction | `H(r)=injectLeft(graphReference(r))` at a left-union payload type | If the graph rule classifies the injection as evidence-only and rejects this cycle, the candidate data-barrier reading is false. O `:137–140` must decide whether its explicit union introduction is the relevant “actual data constructor.” |
| `injectRight`, candidate data introduction | `H(r)=injectRight(graphReference(r))` at a right-union payload type | Same discriminator for the right injection; a contrary evidence-only outcome would falsify the candidate. |
| `both`, evidence / follow candidate | `H(r)=both(graphReference(r))` with the same raw value given both required derivations | If this evidence-only wrapper guards the cycle, it contradicts O `:185`; if observation fails to follow the underlying raw value while preserving both derivations, the candidate edge is false. |
| `roll`, explicit nonbarrier | `H(r)=roll(graphReference(r))` at a matching recursive type | If this roll-only cycle is accepted as guarded, it contradicts O `:185`. The witness has no intervening data/lambda/delay. |
| `topView`, evidence / follow candidate | `H(r)=topView(graphReference(r))` at `Top` | If `Top` evidence alone guards the cycle, it contradicts O `:142,185,236`; if a typed observation invents an unchecked payload eliminator, it violates O `:236`. |
| `view`, administrative / follow candidate | `H(r)=view(metadata, graphReference(r))` with unchanged underlying type | If removal changes the underlying constructor or treats metadata itself as a guard, it contradicts O `:239,489–494`. |
| `continuation`, unresolved | `H(r)=continuation([],z,resume(graphReference(r),z))`, with `r:Kont(Q,A)` and `z:Q` | If the guard judgment accepts/rejects this solely by analogy with lambda, without an explicit continuation clause, it is not source-grounded. O `:163,350–354,1006` gives runtime typing/shape but omits guard status. |

The tuple through nominal rows give a separate minimal payload cycle for each
claimed data barrier; lambda modes and delay each get a code-reference cycle.
This makes the source claims falsifiable without pretending that the omitted
paper judgment has already evaluated these examples. The wrap, polymorphic,
injection and continuation cases remain discriminators, not adopted semantics.

## First blocker and discriminating examples

Missing definition owned by the operational manuscript's rec/graph authority:
an explicit `wrap(function, argumentAdapter, resultAdapter)` graph guard/edge
rule stating whether observation stops at the wrapper, follows `function`, and
how references in adapter computations are retained. O `:184–185,240,260–268`
states the guard premise and graph typing; O `:1002–1008` invokes it in shape
proofs. None defines this constructor case. Luna owns authority intake. The
source manuscript's SCC/closure owner can provide source capture evidence but
cannot decide O's runtime guard by implication. Any semantic change requires a
reviewed in-scope manuscript correction or explicit user decision.

Minimal symbolic discriminator: one node with `Xi(r)=C(A,A)` and
`H(r)=wrap(r,id,id)`. O `:268` types the reference and O `:224` gives the wrap
typing premises, assuming identity adapters have their ordinary code typings.
If `wrap` guards, this self-cycle passes; if its function position is
transparent, it fails. O `:372–374` shows entry re-enters through the wrapped
function before result adaptation. This is not a counterexample to an
authoritative theorem: the manuscript permits divergence generally and does
not state which guard outcome is intended.

Separate adapter-only discriminator: place a recursive reference only in
deferred argument adapter code while the function is a lambda. A traversal that
follows all nested syntax children confuses code capture with an immediately
observed function edge; a traversal that follows none confuses it with the
function-self-cycle. The required edge distinction is missing from the paper.

## Prior-results boundary

- `FiniteGuardDecision` proves a total decision procedure only for the accepted
  `GuardedValueGraph.Node.next` relation. It does not map paper constructors to
  that relation.
- `HigherOrderRecAllocation.frontier` follows selected ref/recvar and
  both/top/view/wrap children in a different research grammar. Its
  `projectNode`/`projection_edge` correspondence proves that model's own
  definition, not the paper rule.
- `HigherOrderGraphObservation` retains adapter types/evidence and distinguishes
  wrapper observation from callable terminal status. It does not cover the
  paper's full polymorphism, raw continuation, or syntax-to-graph relation.
- R29's reviewed theorem is finite heap payload allocation only. Its self-alias
  witness exposes the missing guard premise; it does not establish guardedness.
- S `:133–135,1043–1068,1081–1084,1104` covers source SCC/capture/closure facts
  only in its own grammar. It does not supply O's constructor edge rule.

## Work receipt and gate status

The complementary handoff SHA-256 is
`6c1717c0de5861d6e14c0a931af60bee8d10866546ca2fd76a06b57ecea800a6`.
Researcher cessation was reported at `2026-10-25T18:05:45Z`; active duration
and effective model/effort remain UNKNOWN. Its packet used source reads and
hashes only, with no Lean/Lake, cache, Rust, build/test/runtime, network, Git,
semantic edits, descendants or background work. Primary source reads and hashes
also used no proof/checker/runtime calls. This result awaits fresh independent
M1 citation/coverage review; no self-certification is claimed.

Falsifiers for any later stronger classification: an absent citation for a
constructor-specific edge; treating HigherOrder frontier as paper authority;
dropping either `both` derivation, adapter evidence, wrapper order, or
polymorphic/continuation typing; counting delayed code references as immediate
edges without a rule; or claiming a well-typed payload alone proves graph
guardedness.

**Gate:** exact source blocker identified; full paper guard theorem remains
OPEN. No Lean theorem or native correspondence closed. Implementation remains
`NO_SAFE_CODE_SLICE` pending authoritative edge rule and source/native mapping.
