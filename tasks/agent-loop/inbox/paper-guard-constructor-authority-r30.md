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
| `variable`, alias | Two recursive bindings `x=y; y=x` with no value introduction. A typed cyclic witness is unestablished until the source-to-heap alias relation is specified. | If either variable lookup itself counted as a barrier, the explicit alias-only-cycle exclusion O `:184–185` would be violated. If these names do not map to reference edges under the paper's closure convention, the syntax-to-graph alias classification needs its missing bridge. |
| `graphReference`, follow edge | `H(r)=graphReference(s); H(s)=graphReference(r)`; the manuscript's alias-only-cycle exclusion is the discriminator. The excerpt does not give a separate typed observation judgment for this heap, so typed witness status is unestablished. | If one reference lookup terminates observation or makes this alias-only cycle guarded, the claimed follow-through-reference behavior is false. |
| `literal`, terminal | A literal node `H(r)=literal(c)` | If a pinned `Literal` form has a `Value`/code reference child, or observation follows a child from this node, the terminal classification is false; current `Literal` constructors have no such field (`PaperExecutionSyntax.lean:19–27`). |
| `tuple`, data barrier | Candidate finite heap `H={r↦roll(tuple([graphReference(r)]))}`, `Xi(r)=T`, `T=μ α.(α)`. At node `r`, the reference premise gives `r:T`; tuple introduction gives `tuple([r]):(T)=T[T/α]`; roll gives `H(r):T`. The graph path is `r → tuple payload r`. | If the graph rule rejects this cycle specifically because the inner tuple payload is not guarded, tuple is not a barrier. This typing is conditional on `T` being in the paper's well-formed type domain; the cited clauses give roll typing but no separate `μ` formation rule. Roll itself is not counted as a guard (`O:185,235`). |
| `sequence`, data barrier | Candidate finite heap `H={r↦roll(sequence([graphReference(r)]))}`, `Xi(r)=T`, `T=μ α.List⟨α⟩`, using the declared native List identity. At node `r`, `r:T`; finite-sequence introduction gives `sequence([r]):List⟨T⟩=T[T/α]`; roll gives `H(r):T`. Path: `r → sequence payload r`. | Rejection specifically at the sequence payload falsifies its barrier status. Typing is conditional on this recursive type being admitted by the paper's type-formation domain; no `μ` formation rule is cited here. |
| `record`, data barrier | Candidate finite heap `H={r↦roll(record([(l,required,graphReference(r))]))}`, `Xi(r)=T`, `T=μ α.{l^{required}:α}`, with declared required label `l`. At node `r`, `r:T`; record introduction gives `record(l=r):{l^{required}:T}=T[T/α]`; roll gives `H(r):T`. Path: `r → present field l → r`. | Rejection at that present payload falsifies the barrier; an absent optional field is not an edge. Typing is conditional on recursive type formation. |
| `variant`, data barrier | Candidate finite heap `H={r↦roll(variant(K,[T],[graphReference(r)]))}`, `Xi(r)=T`, `T=μ α.⟨K(α)⟩`; `K` is a declared tag with one payload. At node `r`, `r:T`; variant introduction gives `variant(K,[r]):⟨K(T)⟩=T[T/α]`; roll gives `H(r):T`. Path: `r → K payload r`. | Rejection at the payload falsifies the barrier. The derivation is conditional on the recursive type and declaration meeting the paper's formation premises; the graph/typing excerpt does not state those premises. |
| `nominal`, data barrier | Candidate finite heap `H={r↦roll(nominal(K,[T],[graphReference(r)]))}`, `Xi(r)=T`, `T=μ α.D⟨α⟩`. Assume a well-formed declaration `D` has constructor `K` with payload template `D⟨α⟩` and one payload of type `α`. At node `r`, `r:T`; declaration substitution gives `K(r):D⟨T⟩=T[T/α]`; roll gives `H(r):T`. Path: `r → K payload r`. | If this admitted nominal data payload does not guard the cycle, the barrier claim is false. A typed cyclic witness remains conditional on both the recursive type and declaration formation premises. |
| `lambda(value)`, code barrier | `H(r)=lambda(value, profile, x, call(graphReference(r), delay(ret(x))))`, with `r:C(A,B)` and `x:A` | If inspecting the node executes/unfolds the body before recognizing the lambda guard, or the rule rejects this well-typed recursive-call cycle for lack of the lambda guard, the classification is false. |
| `lambda(computation)`, code barrier | `H(r)=lambda(computation, profile, x, call(graphReference(r), x))`, with `r:C(A,B)` and `x:UA` | Same falsifier as value mode; a mode distinction that removes the lambda guard contradicts O `:184`. |
| `delay`, code barrier | `H(r)=delay(force(graphReference(r)))`, with `r:UA` | If observing the thunk forces its body before recognizing the delay guard, or this well-typed cycle is rejected for lack of a delay guard, the classification is false. This does not assert that a later force terminates. |
| `wrap`, unresolved | Discriminator shapes: `H(r)=wrap(graphReference(r), idArg, idResult)`; separately, put `r` only in deferred argument-adapter code around a lambda. A typed cyclic witness for either shape is unestablished because exact adapter typing and graph-edge premises are the unresolved authority gap. | The first shape distinguishes stop-at-wrap from transparent function traversal. The second distinguishes a function edge from captured/deferred code. Either paper outcome would resolve the gap; neither is assumed here. |
| `typeAbstraction`, evidence-only candidate | Finite heap `H={r↦typeApplication(graphReference(s),Unit), s↦typeAbstraction(graphReference(r))}` with `Xi(r)=Bool`, `Xi(s)=∀β.Bool`. At `r`, `s:∀β.Bool` and type application at `Unit` gives `Bool`. At `s`, in the same `Γ={r:Bool,s:∀β.Bool}`, `r:Bool`; abstraction gives `Λβ.r:∀β.Bool` because `β∉FV(Γ,D)`. The path is `r → application child s → abstraction child r`. | This is a typed finite two-node cycle using the displayed typing rules, with no data/lambda/delay. If the paper guard accepts it, the nonbarrier reading is false. O `:185,238` supports rejection; the exact constructor edge rule remains absent. |
| `typeApplication`, administrative/candidate transparent | The same finite heap and `Xi` above gives a concrete application edge `r → s`, followed by the abstraction edge `s → r`; the node derivations are those in the preceding row. | If outer administrative normalization leaves an actual data/code guard or does not expose the application as O `:316,321,493–494` say, the candidate traversal is false. This exercises the application but does not define the missing general guard rule. |
| `injectLeft`, candidate data introduction | Candidate finite heap under `T=μ α.(α∨Bool)`: `Xi(r)=T`, `H(r)=roll(injectLeft(r))`. If `T` is well formed, `r:T`; left injection gives `T∨Bool=T[T/α]`; roll gives `H(r):T`. Path: `r → left payload r`. | If the graph rule treats this explicit union introduction as evidence-only and rejects the cycle at its payload, the candidate data-barrier reading is false. O `:137–140` leaves its guard classification to be made explicit. Typing is conditional on recursive-union formation. |
| `injectRight`, candidate data introduction | Candidate finite heap under `T=μ α.(Bool∨α)`: `Xi(r)=T`, `H(r)=roll(injectRight(r))`. If `T` is well formed, `r:T`; right injection gives `Bool∨T=T[T/α]`; roll gives `H(r):T`. Path: `r → right payload r`. | A contrary evidence-only outcome falsifies the candidate, and O must decide it explicitly. Typing is conditional on recursive-union formation. |
| `both`, evidence / follow candidate | Candidate heap under `T=μ α.(α∧α)`: `Xi(r)=T`, `H(r)=roll(both(r;d_1,d_2))`. If `T` is well formed, `r:T`; each `d_i` derives that same raw value at `T`; both gives `T∧T=T[T/α]`; roll gives `H(r):T`. Path: `r → both raw value r`. | If admitted by type formation and the guard rule counts the evidence wrapper itself as a guard, it contradicts O `:185`; if traversal drops either derivation, typed observation is incomplete. Without an established formation premise for `T`, typed cyclic witness remains unestablished. |
| `roll`, explicit nonbarrier | The paper explicitly excludes cycles consisting only of alias/roll/type evidence (`O:184–185`). The tempting one-node shape `H(r)=roll(graphReference(r))` would need `Xi(r)=μ α.α` to satisfy roll introduction, whose well-formedness is not established by the cited paper clauses. | No well-typed cyclic witness is claimed: the missing type formation premise cannot be invented to force one. The concrete source falsifier is the explicit negative statement itself: if O's guard judgment accepts a roll-only cycle, it contradicts O `:185`. All other roll-wrapped data witnesses here count only their inner data constructor as guard. |
| `topView`, evidence / follow candidate | Finite candidate heap `H={r↦topView(graphReference(r))}`, `Xi(r)=Top`. The displayed top introduction types `r:Top` and hence `topView(r):Top`; path: `r → underlying value r`. | If `Top` evidence alone guards the cycle, it contradicts O `:142,185,236`; if a typed observation invents an unchecked payload eliminator, it violates O `:236`. |
| `view`, administrative / follow candidate | `H(r)=view(metadata, graphReference(r))` with unchanged underlying type. Whether this metadata-bearing finite graph is a paper heap entry is unspecified; typed cyclic witness remains unestablished. | If removal changes the underlying constructor or treats metadata itself as a guard, it contradicts O `:239,489–494`. |
| `continuation`, unresolved | `H(r)=continuation([],z,resume(graphReference(r),z))`, with `r:Kont(Q,A)` and `z:Q`; the body has type `A` under the runtime typing premise. A typed cyclic witness is unestablished because the excerpt does not state the continuation node typing/graph-edge rule. | If the guard judgment accepts/rejects this solely by analogy with lambda, without an explicit continuation clause, it is not source-grounded. O `:163,350–354,1006` gives runtime typing/shape but omits guard status. |

For each candidate recursive-data heap above, `Xi` assigns its sole location
the displayed `T`; every reference occurrence therefore has that fixed type,
the data introduction has the one-step unfolded type, and explicit `roll`
returns `T`. The finite heap has exactly the shown location and edge, so its
cycle path is explicit. These are source-valid *conditional derivations* from
the displayed node-typing rules, not unconditional claims that each proposed
recursive type or declaration is well formed: O `:235` supplies roll typing,
but the cited fragment does not state a general recursive-type formation rule.
Where that premise cannot be established, the typed cyclic witness remains
unestablished and the row is only a discriminator template.

The polymorphic two-node heap is unconditional under the displayed rules:
`Γ={r:Bool,s:∀β.Bool}` types both entries, type application uses `Unit`, and
the abstraction side condition holds for fresh `β`. Its cycle path is
`r → s → r`. Lambda modes and delay have the node typings shown in their rows;
their code-reference paths close at `r`. The roll-only row is explicitly not
claimed as a well-typed witness. These examples make claims falsifiable without
pretending the omitted guard judgment has already evaluated them. Wrap,
injection, and continuation cases remain discriminators/candidates rather than
adopted semantics.

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
