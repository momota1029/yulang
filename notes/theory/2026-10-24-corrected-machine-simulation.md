# A finite observation simulation for the corrected candidate machine

Frozen handoff: CM-SIM-20261024, revision 1. Author: `/root/astra_corrected_machine`; no coauthors or descendants. Status: **unreviewed mathematical candidate**, not semantic adoption, source/native correspondence, principality, or production authority. Requested model/effort: Astra/medium; observed model/effort: UNKNOWN. Baseline supplied by primary: `424566114` (no Git commands performed).

## 1. Parent and fixed dependencies

The parent is `thm:repaired-source`, source manuscript lines 2486–2505: for every finite declarative typing derivation in the fixed candidate `Src*all`, obtain the conclusions of `thm:release-source` and wildcard hygiene, including all finite executions and typed repeated responses/resumptions. This does **not** quantify over all ordinary programs accepted by an unspecified inference algorithm. The enclosing sprint retains the larger goal for the original approved source domain; this note does not replace that goal with this narrower candidate theorem.

Direct inputs, frozen SHA-256:

- `tasks/agent-loop/sprints/semantics-proof-20261024.md`: `41fe6dae949980c6e4e2289046b3bd281b63c9d7d0a04e594907e23a764b335a`.
- `docs/yulang-operational-type-safety-ja.tex` (O): `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
- `docs/yulang-source-type-safety-ja.tex` (S): `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`.

Dependency locators: O:1300–1453 (diagrams and transfers), O:1631–1707 (cut grammar), O:2291–2486 (old release and representation); S:391–532 (immutable evidence/current control), S:1560–1655 (source transfer and family theorem), S:1657–1996 (R-Inputs through R-Cross and multi-target release), S:2379–2509 (permission kinds and W-Eligible). Manuscript authorship is inherited from these frozen files; this worker claims authorship only of this note. Older proofs are used only for the explicitly unchanged value constructors and frame grammar, not as a certification of the revised abstraction.

Three stages: joint representation and selective-update construction; current-state/resumption simulation and finite cut closure; parent application and obstruction. No source language, inference rule, or concrete transition is changed.

## 2. What must be represented

A concrete finite-prefix state has immutable allocated evidence `E`, current control `C` (active owners/handlers, executing View occurrences and frame modes), current relation `L ⊆ Scope × Target`, and typed packets with route witnesses. Scope origin, receipt, target capture table `B_t`, saved evidence and old Observe rows remain immutable. A route witness includes its own transported target set `H(w)`; two routes with the same event remain distinct witnesses. Treating witness identity as event identity is invalid.

For each currently queried packet/candidate pair `j`, use these concrete predicates on a protection witness `w`:

- `D_j(w)`: all original receipt/Path/Observe/incidence and current activity conjuncts required for protection, excluding Prot and release;
- `P0(w)`: original protection kind;
- `A(w)`: activity of its original receiver;
- `F_j(w)`: original receiver differs from the current candidate owner;
- `Z(w)`: there exists `t ∈ H(w)` with `L(s(w),t)` and `Match(t,s(w))`.

Thus `Live(w)=P0(w) ∧ ¬(A(w) ∧ Z(w))`, and

`P_j = ∃w. D_j(w) ∧ Live(w)`,

`PF_j = ∃w. D_j(w) ∧ Live(w) ∧ F_j(w)`.

This factors the concrete R-Project formula without changing it. Z is a derived **current binary-incidence query**, not a unary replacement for L, nor a permanent fact stored at capture. `D_j` must include exactly the source query's other activity/path conjuncts; expired protection is not resurrected by merely making Live true when A becomes false.

Also retain finite scalar observations `Base_j, GC_j, GW_j`, operation/declaration/port tags, completion modes, and finite static template labels. Actual family/type-instance equality required by a query is an equality observation; coincident finite colors never establish that equality.

## 3. Explicit finite joint cell

Fix a finite interface I from a finite typed code/template derivation. It has finitely many register *slots*, sorted by evidence owner, control owner, handler, scope, target, receipt, event and view occurrence; owner identity comparisons across evidence/control roles are allowed through their common owner-name sort. The action role is separate from the identity sort. Finitely many packet ports and candidate slots are jointly represented. Runtime identities and stack depth are unbounded; the number of slots is not.

A cell contains:

1. Defined bits and the equality partition of all identity registers, with sort restrictions; role tags and finite scalar observations.
2. Named binary observations `L(s_i,t_k)` and `Match(t_k,s_i)`, origin/receiver equalities, and named activity. These are only for represented endpoints.
3. For every named witness, its complete Boolean vector over the predicates in §2, membership in the interface packet ports, scope/receiver equalities with named registers, and `t_k ∈ H(w)`. Include any finite additional discriminator columns required by the current primitive. For hidden witnesses, one occupancy bit `e_beta` per complete vector beta. Hidden means distinct from *all* named witness registers.
4. Analogous joint unary diagrams for owner activity/incidence when needed by existing transfers. These owner diagrams do not replace the witness diagram.

Alpha_I evaluates these finite predicates in the concrete state. The concrete evaluation may traverse a finite history DAG; the abstract table generator never evaluates an arbitrary history. There are finitely many partitions, Boolean vectors and occupancy bits, so the set S_I of **syntactic** cells is finite. It may include unrealizable cells. Require only explicit finite constraints (equality coherence, named-row agreement, sort correctness, and PF implies P as derived below); do not test concrete reachability or realizability.

Query is a total Boolean function on a cell: compute P and PF by disjoining qualifying named vectors and hidden occupancy bits, then use

`Eligible_j = Base_j ∧ (¬P_j ∨ GC_j ∨ (GW_j ∧ ¬PF_j))`.

**Lemma 1 (observation exactness).** For every finite concrete state x, this function on Alpha_I(x) equals current W-Eligible, provided I contains the current query slots.

**Proof.** Partition the concrete witness set into named singletons and hidden complete-vector regions. The body of each existential is constant on each region. Its existential is therefore exactly the disjunction of the corresponding occupancy bits and named truth values. All four scalar observations are evaluated in that same state and packet/candidate tuple. Substitution into W-Eligible proves equality. Binary L/H/Match correlations are evaluated together inside Z; the proof never infers their intersection from separate nonemptiness bits. ∎

Exactness belongs to **Alpha_I(x)**. An abstract set U containing Alpha_I(x) can contain cells with either query answer. Filtering U by a desired answer is not an exact decision about x. Both reachable answers must remain in graph branches.

## 4. Finite splitting, selective mutation and reexposure

The following executable-by-enumeration operations define abstract tables without a soundness oracle.

**Refine.** Add k Boolean columns. A named vector receives every compatible refinement. For a hidden occupied beta, choose any nonempty subset of its at most `2^k` compatible refined vectors as occupied. An empty beta has no occupied refinements. Constraints already represented remain fixed. Enumerate all such choices jointly with the register partition. The result is finite. Multiple refinements may be occupied even if some concrete realization has only one witness; this is intentional overapproximation.

**Map.** When a primitive has a justified pointwise Boolean formula f, map named vectors by f and set `e'_gamma = OR_{beta:f(beta)=gamma} e_beta`. With copying of a route into several outputs, first use a joint vector with output-port membership columns; a witness can contribute to several output ports. Do not subtract a shared witness merely because one View ends. A specified deleted output port is forgotten, not removed from all other ports.

**Expose.** To name a previously hidden witness from occupied beta, create its named vector and choose independently whether the residual beta is empty or occupied. Other regions are unchanged. If the new register aliases an existing named witness, use its existing row instead. Forget is the converse safe operation: add the forgotten singleton to its hidden region if no register still names it. No count of one is inferred from occupancy.

**Refresh.** Drop selected mutable/derived columns and refine them anew using all finite assignments satisfying explicit constraints. Preserve immutable identity and origin facts that the action really preserves. If a predicate depends on any forgotten binary endpoint, hidden route, changed world or new candidate, it is refreshed unless a concrete defining equation proves its update. In particular Z, D, F and grant-query results cannot be copied merely because a packet was saved. New target introduction and newly exposed candidate endpoints require fresh joint columns.

**Lemma 2 (representation preservation of these four operations).** For every concrete operation of the stated kind and input x, its actual output cell is among the enumerated outputs from Alpha_I(x).

**Proof.** For refinement, choose precisely the refined regions containing an actual witness. They form a nonempty subset for each occupied old region. For map, a region is occupied exactly when some occupied input region maps into it. For expose, the actual residual has one of the two enumerated emptiness values, including the case of two indistinguishable witnesses. Forget contributes the actual singleton. For refresh, the actual new predicate values are one enumerated refinement and satisfy each retained defining equation. Named identities are chosen according to their actual partition. None of these arguments requires an upper bound on concrete multiplicity. ∎

**Selective-release example.** Suppose two hidden witnesses w1,w2 have identical old displayed vector, P0=A=D=1 and Z=0. Their scopes are distinct and a crossing selects only s(w1). Introduce a discriminator `U(w)` for the actual selected scope/target/route condition before updating. Refinement permits both U=1 and U=0 regions to be occupied. The actual state chooses both. At fixed activity and with the relevant target carried by each tested witness, `Z'=Z∨U`; the output contains one released and one protected region, hence P'=1. Mapping the old region uniformly to Z'=1 would incorrectly make P'=0. Even a single scope can have differently targeted route witnesses, so the discriminator must include each witness's H, not scope alone.

For general R-Cross, use `U(w) = ∃s,t. s=s(w) ∧ (s,t) is newly added ∧ t∈H'(w) ∧ Match(t,s)` and the unchanged L facts, or simply Refresh Z when this finite interface cannot express the equation. H' must include the delimiter's new transported target where appropriate. The concrete U is a finite query; the abstract relation introduces U by Refine, not by solving hidden reachability. For known named `(s,t)`, use the exact equation `L'(s,t)=L(s,t)∨[t=t_frame ∧ s∈Scopes(q) ∧ From_s(q) ∧ Match(t,s) ∧ Act(r(s))]`. Unrepresented conjuncts are fresh finite observation bits. Joint scope consistency may be lost, producing extra states; actual successor inclusion remains proved.

**Binary-incidence obstruction to an exact quotient.** Let hidden scopes a,b and targets x,y have no represented endpoint distinguishing them. Two finite structures may agree on every existing unary occupancy/marginal: L1={(a,x),(b,y)} and L2={(a,y),(b,x)}. A later witness with scope a and H={x}, with active receiver and Match true, has Z=1 in the first and Z=0 in the second. Therefore old unary diagrams do not determine future query answers. Naming/exposing x must refine the joint observations, not recover a unique answer from the old quotient. This is an information-loss countermodel, not a source-qualified counterexample: reachability of both structures by the approved source constructors is not proved here.

## 5. Local corrected-machine simulation

Construct a transfer relation R_a by enumerating finite input/output cells, using the four operations above and only the following concrete defining equations. Every unlisted coordinate depending on changed data is Refresh, not an implicit frame condition. This last rule is essential: a soundness proof must justify every copied derived coordinate.

- **L-Enter:** expose/read the original owner if necessary. Active branch assigns the same identity to control and mode borrow. Inactive branch adds a fresh owner unequal to the entire old support, sets activity and mode own, while old receiver activity is unchanged. Freshness beyond named support is imposed concretely; abstractly require inequality with all named identities and zero old-evidence membership. Hidden coincidence questions are refreshed. Immutable evidence, s,t and named L pairs are copied. Receive/forwarded-handler/new View rows use the new current control; route observations not specified by an exact primitive equation are refreshed.
- **Completion:** borrow does not remove its owner; own removes precisely the fresh control owner of that frame. Expose the owner, update its activity, then refresh witness activity/incidence/Z-dependent columns jointly. No original receiver is renamed to this owner. Restore the saved outer ambient View contribution rather than taking set difference.
- **R-Cross:** update the named L pairs by §4 and transport the current packet with t; apply Refine/Map or Refresh to every affected hidden witness. Keep source attribution and immutable grant evidence; refresh grant *query values* if current path/candidate changes. Ret transports t but leaves L unchanged; Fail leaves L unchanged. Observe alone leaves L unchanged.
- **Resume/read/No re-search:** keep saved evidence and allocated s,t fixed; use the present C,L and actual resumer ambient View. Expose needed endpoints, then Refresh current queries. L-Enter reconstructs each captured control frame. Raw resume does not redo source receipt or create a Boundary. Stored values remain immutable. New executing occurrences are fresh. Repeat this construction on every resume; no snapshot of L is restored.
- **Fresh source introduction:** a new actual receipt/scope/target has fresh identity, source-specified immutable origin/capture, and no old L pair containing that new scope or target. Future paths may reveal old target identities, but those are Expose, not Fresh. Match and H/route queries with old hidden endpoints are refreshed. New ordinary call and resumption remain different action tags.
- **Transport/observation/lookup:** copy only actual primitive identity/prefix/projection facts. Recompute the current packet's observation predicates after executing-View changes. Previously retained Observe evidence is not a separately emitted packet and cannot be unioned as a stale unreleased current alternative. Unknown closure routes and source-owner lookups use Refresh. Existing finite source alternatives are all retained.

**Lemma 3 (local simulation).** For every concrete finite state x of the corrected candidate machine, every one of the above concrete metadata steps `x --a--> y`, and matching interfaces, `(Alpha_I(x),Alpha_J(y)) ∈ R_a`. This also holds for current-state reexposure after arbitrary intervening typed computations, not just after one local frame action.

**Proof.** Concrete L-Enter has exactly the two stated exclusive branches. Its chosen identity and mode satisfy the corresponding enumerated branch, with evidence fixed. Completion and R-Cross satisfy their stated pointwise/set equations. Lemma 2 covers hidden multiplicity, newly visible endpoints and lost binary incidence. Resume/read chooses actual current C,L values among Refresh outputs; old allocated evidence and current named L satisfy the retained equalities, regardless of the number or origin of intervening steps. Fresh source allocation satisfies all support inequalities and zero old L incidence. Remaining transports either have a defining pointwise formula, covered by Map, or discard the unavailable relationship, covered by Refresh. Scalar query branch selection follows Lemma 1 on the actual output cell. Thus each concrete successor is included. ∎

This is a finite **overapproximation**, sometimes coarse. It neither claims all enumerated successors are realizable nor proves preservation for a smaller preexisting table that omits them. It does not require L to be finitely bounded globally.

## 6. Finite cut closure and its quantifiers

Take the typed seven-frame grammar of O:1631–1707 with release from O:2517–2520 and corrected scope semantics from S:391–532. Fix a finite union interface for each frame signature. Forget/refine are finite interface adapters. Let B be the finite disjoint union of the cell universes for value, event, latent, reentry and required joint ports. Lattice `D=P(B)` is finite; use a finite product if ports must stay distinct. Joint comparisons are cells in B, not products of independently chosen marginal facts.

Each primitive relation induces `R[X]={y | ∃x∈X. x R y}`, a monotone function. Query filters retain all cells satisfying the branch condition. This is monotone even though W-Eligible contains negation: the condition is a fixed Boolean function of a cell, not a negation of growing sets of facts. Frame interpretation composes these maps, source body-port tables and fixed unions. A finite function lattice `Mon(D,D)` contains every frame summary. For N grammar nonterminals and finite code ports, the simultaneous code/cut lattice is a finite product of powersets and such monotone-function lattices.

Start at bottom and repeatedly apply all grammar equations/inclusions, retaining old facts. Each step increases this finite lattice, so iteration stabilizes after at most its finite height. Function composition is monotone in each argument, hence the simultaneous operator is monotone. The resulting table is a post-fixed solution containing every finite grammar derivation, proved by induction on that derivation: terminals are included; a grammar composition applies the induction hypotheses and monotonicity. This constructs closure rather than assuming a sound cut summary.

For an actual captured continuation, induction on the number of request propagation steps supplies its grammar derivation: bind/scope/View/mapop/wait/release append the corresponding frame; forwarding through an unselected handler appends handle; selection stops before the selected handler. Every typed response and every current admissible ambient world is a separate input. Lemma 3 applies to the actual current input, and compositional monotonicity includes the finite suffix trace. Repeated resumptions reuse this universal input statement; their current L and activity may differ. No identity equating immediate and reentry effects is used. A foreign continuation's body still requires its own typed introduction/reentry contract: the local frame argument does not discharge that independent quantifier.

The finite-signature premise is essential. The manuscript uses finite template nodes and abstract colors for nonregular type instantiations; unrepresented instance equalities must remain observation bits. This proof does not construct a finite exact universe of all instantiated types, nor prove source/native generation of its template interfaces.

## 7. Application to the original source obligation

For the **explicit table construction in this note**, Lemmas 1–3 and §6 discharge the missing abstract local-simulation/cut-closure argument for current-state protection and W-Eligible. Given a finite `Src*all` source derivation that supplies its existing value typing/source elaboration and satisfies every mandatory inclusion **using these tables**, induction on finite execution prefixes gives immediate/latent/reentry inclusion: each actual seed belongs to its input port; Lemma 3 supplies each actual successor; graph closure supplies its successor port; §6 handles captured suffixes for all typed current inputs. An outward event cannot appear in an empty outward port. Current query execution obeys W-Eligible by Lemma 1, retaining the candidate wildcard-hygiene argument. Value preservation/progress use the unchanged explicit value-typing construction, not the abstraction as an assumed premise.

This supplies a concrete interpretation of the manuscripts' phrase “all consistent candidates.” It does **not** establish that any previously asserted small annotation passes the resulting stronger inclusion check. Nor does it prove that all possible readings of their underspecified hidden transfer sentence generate this table. The selective-release example identifies exactly the missing split that a proposed implementation/table must retain.

The remaining obligations for parent closure are therefore precise:

1. **Fixed-table reconciliation (primary + independent reviewer):** audit that each graph-generation rule in S and O uses this finite relation or a proven sound refinement, in particular R-Cross hidden splitting, No/current query refresh, new target exposure and joint ambient/captured inputs. Falsifier: one actual concrete successor excluded by a generated edge. Earlier “Boolean image” prose without the discriminator does not suffice.
2. **Source bridge and accepted domain (primary source lane):** construct all surface elaboration/value/source-origin rules for the original approved source domain and show their concrete transitions are these candidate transitions. Owners in the manuscript: source decoration, F-Seed/F-Owner/N-Transfer, R-Inputs/R-Capture/R-Match/R-Cross and generated-binder surface elaboration. The note supplies no compiler-symbol evidence and no native correspondence. A source constructor producing a different receiver, target, grant kind or continuation frame is an exact falsifier of that bridge.
3. **Natural inference and A/B:** prove generation, accumulation, propagation, levels, extrusion, qualifying intrusion, generalization and independent residual/provider/witness premises under their original quantifiers. This note has not changed or discharged them. A finite conservative table may reject a natural small effect derivation; safety inclusion does not make that acceptable language behavior, prove principality, or justify weakening ordinary inference.
4. **Semantic adoption:** `Pi_flow`, `A_all`, corrected lifecycle and permission remain candidate choices where the manuscripts say so. Declarative safety does not establish agreement with all approved observable behavior. No authority change occurs here.

No implementation TODO is issued: implementation is excluded and no production constructor was inspected. The minimal future evidence request is a table-generation/source-constructor audit with the precise successor-exclusion falsifier in item 1, before any code proposal.

## 8. Freeze and resource receipt

The useful previous results reused are the finite typed frame grammar, value-type invariance under metadata actions, immutable-evidence/current-control definitions, and R-Project/W-Eligible concrete formulas. Rejected transfers are old saved-evidence renaming, bound-release snapshot copying, deterministic unary hidden release without splitting, stale query reuse after No/resume, and collapsing independently transported witnesses by event identity.

Checks: direct input SHA-256 compared with frozen contract; relevant formulas and source locators read; proof is pen-and-paper enumeration/induction, not an executable test. No builds, tests, network, code edits, Git operations or descendants. Budget: 180 seconds and at most three substantive stages; three stages used. Exact active runtime is not instrumented, hence UNKNOWN; no unobserved budget is returned. Only new/written path: `notes/theory/2026-10-24-corrected-machine-simulation.md`; no scratch paths.

Stop condition: constructive conservative simulation and cut closure supplied, with exact precision/source/adoption boundaries. Revision 1 is frozen on handoff. Writes cease after hash receipt; no background work or unresolved descendant leases. Next action belongs to the primary: obtain independent review of this exact hash and reconcile the tables/source bridge. This author does not certify or promote the candidate.
