# Conditional public-import graph derivation for captured `pick`

Date: 2026-10-08
Status: Unreviewed research-only conditional derivation; frozen on submission
Baseline: `fe5cd0e946e8e45a628cbaed4d560288dc76c29c`
Branch: `research/simple-sub-intrusion`
Exclusive lease: `notes/theory/2026-10-08-pick-public-import-graph-derivation.md`
Gate/method: D0 fixed-import supplier; finite typed graph construction and scope-preservation proof
Implementation authority, representation adoption, import sufficiency and gate closure: none

## 1. Objective and governing scope

Construct a finite typed public-contract graph for the established immutable
capture `z` in the bounded Value-entry projection `pick ignored = z`. The
construction records the public contract's actual value/provider incidences,
original binders, complete dependencies and dynamic argument positions. It
then proves preservation of the imported actual provider's existing
same-provider admission/observation obligations under one authorized local
instantiation. This is a wiring/transport result given exact public contracts,
not an extraction theorem from arbitrary source definitions.

Read only the committed baseline for semantic dependencies:

| Source | Exact governing sections and use |
| --- | --- |
| [Accepted q1/a1](../../questions/2026-10-08-successor-generalize-root-policy/approved-answer.md) and [receipt](../../questions/2026-10-08-successor-generalize-root-policy/receipt.md) | Decision items 1–5: transformed/displayable scheme plus necessary additional use information; no retained full source relation under a new name; sufficiency and adoption remain open. |
| [FVIEW](../design/2026-10-05-inferred-function-call-views.md) | §§1.1–5: distinguish annotation, public scheme and internal evidence; source-generated incidences, original shared `nu,K,D`, comparison independence and actual-role preservation. |
| [Source Generalize](../design/2026-10-08-source-generalize-definition.md) | §§2–4: fixed established external contracts and full dependencies, eligible component-owned descriptions, original binder scopes, aliases versus independent frames, active residual, separate public/production obligations. |
| [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md) | §§2.1–3.4/3.7: typed finite relational clauses, joint operands, independent admission, whole renaming with rigid imports fixed, Option 2's independent extras and unchanged-domain certificates. §2.2 remains a conditional hypothesis, not an established active-root supplier. |
| [D0 proposal](2026-10-08-id-pick-d0-concrete-decoder-proposal.md) | §§3–6: `J_z` fields, fixed import, Value entry and current-world return, import/admission/descriptor suppliers, unresolved S/T and production choices. Its pinned header says Unreviewed; this note adds no review certification or adoption. |
| [Contextual membership](../design/2026-10-08-contextual-function-membership-definition.md) | §§2–4: every genuine actual decomposition, same actual provider, independently checked challenges, all pending/complete/future observations, hereditary immutable binding interpretation and current-event eligibility. |

Repository workflow dependencies are `rules/research-lab.md`,
`rules/design-authority.md`, `rules/git-concurrency.md` and
`rules/question-board.md`. The integrated q1/a1 bundle is consumed at its
pinned contents. The pending ReadInvoke presentation question and dirty shared
records are excluded. No `M_E`, source-presentation owner, selected production
grammar, S/T choice, or universal finite-summary theorem is assumed.

## 2. Claim classes and hypotheses

**Established input meaning:** the cited membership definition requires the
same actual callable at every genuine `Act(z,U,r)`, at independently admitted
whole challenges and their live indices. Source Generalize preserves actual
binding/provider and fixed external dependencies; it does not make public
projection sufficient. These statements are inputs from governing sources.

**Bounded characterization:** the finite incidence construction below works
for a *supplied* finite, dependency-closed collection of independently
interpreted public contract clauses. It accommodates finite cycles without
unrolling them. Its size is measured in supplied nodes and incidences, not
source size, history length or solver complexity.

**Conditional theorem:** if H1–H6 hold, the graph and its one local
instantiation preserve the import's complete admission and observation
predicates, hence preserve any existing same-provider obligation or its
failure. No hypothesis is asserted proved for an arbitrary captured source
value. In particular, H1/H3/H4 are the remaining public supplier premises.

| Hypothesis | Exact premise; failure boundary |
| --- | --- |
| H1: public supplier | `J_z` is a genuine public contract for the fixed captured binding, with finite typed public clauses and references; each clause has its independent meaning. It contains complete descriptor, admission, observation/guarantee, scope/visibility/lifetime/authority and actual-provider obligations, including licensed Option 2 alternatives where applicable. A source root, full source relation, successful-Q predicate or unexplained containment oracle is not a supplier. |
| H2: exact incidence | The certificate from formation associates every clause operand with its original ordered incidence, binder scope, value/provider origin, static slot and dependency. It preserves every genuine actual decomposition quantified by the original contract. A certificate for one convenient decomposition is insufficient when another genuine decomposition exists. |
| H3: finite complete closure | Following all *public contract* references and all required fixed free-coordinate dependencies from `J_z` reaches finitely many registered nodes. The explicit dependency inventory is exhaustive. No hidden semantic free field, unbounded generated reference chain or private source lookup is needed. This is a supplied finite-envelope premise, not a language rejection rule. |
| H4: public interpretation | Finite clause assembly denotes the same independent clauses on the same shared tuple at their original scopes. References resolve to the same established public contracts with their pre-existing meanings. Any cyclic meaning is supplied by those contracts, not defined by this graph. If actual ordinary descriptor activation requires an unprovided embedding theorem, semantic preservation is conditional on that theorem. |
| H5: lawful allocation | Only the named eligible formal-local ordinary description binders of this `pick` publication are freshened; they are outside the fixed dependency closure. One injective capture-avoiding map acts jointly on every incident local occurrence and residual. Aliases share one incoming description frame; independent uses get distinct frames. Original source slots and all fixed/imported coordinates retain identity. |
| H6: dynamic validity | Evaluations supply the actual event/current configuration/history/continuation operands at their original logical scopes, jointly with `xi=(nu,K,D)`. The import's hereditary certificate applies at the considered independently compatible future event. Static provenance supplies no live grant. Unknown State transitions and incompatible worlds are not covered. |

H1 is stronger than knowing the printed endpoint `B_z`; H2/H3 cannot be
reconstructed from endpoint equality. H4 does not assert the source-contracts
§2.2 `M_E` interpretation, and the theorem supplies no instance of that open
hypothesis. Existing independently interpreted public clauses are the inputs.
If the only available object is an internal source relation, this construction
has no H1 instance and stops there.

## 3. Finite typed graph and dependency closure

A node key is a publication-qualified identity and a sort. It is never a
printed type, raw endpoint shape or inferred provider equality. Indexed edges
preserve ordering and repeated operands: two argument positions referencing
the same endpoint remain two incidences, while their common endpoint remains
one shared node.

| Node sort | Contents retained from supplied public contracts |
| --- | --- |
| `Contract(c)` | Established public contract identity/version; clause-root references; ordinary independent descriptor and full admission/observation interfaces. |
| `Value(v_z)` / `ActualIncidence(i_z)` | Rigid actual captured value/binding origin and its certified provider/receiver incidence. The original `Act` quantifier over genuine decompositions remains at its imported scope; a finite node is not an enumeration or selection of its domain. Concrete provider anchors, when supplied, retain their actual identities. |
| `Endpoint(d)` | Typed public description endpoint and its declaration identity; no role/entry/provider inference from shape. |
| `Binder(b)` | Original logical binder, sort, owner and parent/dependency incidences; classification as fixed free coordinate, imported bound binder, shared environment binder, or eligible formal-local description binder. |
| `Clause(q)` | Independently typed public primitive/conjunction/alternative/binding/reference clause, semantic supplier/version and ordered typed arguments. Admission and observation clauses remain distinct. |
| `StaticIncidence(k)` | Capture occurrence, static slot/profile, source-established owner/path/receipt incidence and visibility scope. The identity records formation; it does not grant dynamic eligibility. |
| `DynamicPort(t)` | Typed argument position for event, current world, complete challenge/history, response/resumption, observation and original scoped evidence. No current value is frozen into this port. |

Edges are:

```text
root(c,q)                  public contract clause inventory
arg(q,j,n)                 ordered operand j with its declared sort
bind(q,b), parent(b,b')     original logical binding and scope ancestry
requires(n,n')             explicit typed dependency, including free coordinates
ref(q,c')                  public contract reference, not source relation reference
capture(k,v_z,i_z,c_z)      original capture incidence and fixed public contract
at(q,t), shares(q,q',n)     dynamic argument incidence and same shared coordinate
```

`shares` records incidence already given by repeated `arg` references; it
adds no independently chosen witness. Binder and reference edges record the
existing semantics. No graph-wide least/greatest fixed point is selected.

Start with `c_z`, its capture incidence, endpoint `B_z`, actual binding/provider
anchors, shared environment/lifetime/world anchors and their complete public
clause operands. Repeatedly follow `root`, `arg`, `bind`, `parent`, `requires`
and `ref`, adding a node only once by its certified key. Under H3 this ends in
`G_z`. All reachable clauses and references are retained; this is intentionally
not an import-minimization claim.

The *fixed coordinate set* `F_z` begins with the actual binding/provider and
established monomorphic free fields, shared initializer/environment facts,
actual one-shot evidence and their required free-coordinate dependencies.
Close it transitively through the declared fixed dependency relation. A bound
Family or other imported logical parameter is retained under its original
binder; it is not converted into a new fixed concrete assignment. Its free
outer dependencies are fixed where the established contract requires them.
An imported event binder likewise remains a binder rather than a stored
publication-time event value. This distinguishes dependency closure from
freezing every semantic variable reachable in a contract.

In a finite supplied graph with `N` nodes and `I` incidence/reference entries,
indexed closure uses `O(N+I)` visits and storage. This excludes discovering
missing dependencies, deriving truthful clauses, checking arbitrary logical
equivalence, solving constraints, actual descriptor embedding and provider
membership. Without H3, a visited set cannot establish finiteness of a lazily
generating dependency universe; the search stops without claiming completion.

### Concrete schematic `pick` attachment

Let `a` be an eligible ordinary formal description binder and `B_z` the
supplied fixed import endpoint. The proposed public scheme is schematically
`forall a. a -> B_z`, subject to its remaining D0 suppliers. The attachment is:

```text
pick local declaration a -------> formal WholeCarrier(a)/Value(a) ports
pick capture occurrence k_z ----> Value(v_z), ActualIncidence(i_z), Contract(c_z)
pick result endpoint -----------> Endpoint(B_z)
c_z clause arguments -----------> original shared fixed/imported binders
c_z public references ----------> c_1, ..., c_m with their complete dependencies
pick result/future-use ports ----> same v_z and same c_z at current event/world
```

If a purported eligible `a` is required as a fixed free coordinate by an
established contract, H5 forbids freshening it. The graph cannot decree its
eligibility or retain the schematic `forall` against Source Generalize's
fixed closure. Residuals that link a lawful local `a` to fixed operands remain
jointly active; they are never dropped because `pick` returns a capture.

The projection's argument must still undergo its designated Value-entry
Force even though ignored. A Force return supplies its actual `C1`; the body
and outward return use `(v_z,C1)`. A pending Force carries its original raw
continuation and proceeds at the resumed current world, without replaying
receipt. These entry/Bind obligations remain D0 inputs; the import graph
neither executes nor proves them.

## 4. Binder/capture incidence and one joint per-use renaming

For one independent incoming frame `u`, let `L` be exactly the authorized
formal-local description binder declarations outside `F_z`. In the simplest
supplied envelope `L={a}`. Define one injective map `rho_u` with fresh range:

```text
rho_u(a) = a_u             for a in L
rho_u(n) = n              for all rigid/fixed/imported node identities
```

Apply it jointly to the scheme, local clause operands, binder declarations,
all local references, residuals and incidence links. It is not a separate
map per endpoint, admission clause or capture. Source position/slot identity
`beta`, capture identity `k_z`, actual `v_z`, provider origins, `c_z`, fixed
free coordinates and imported bound binders remain unchanged. Fresh printed
names are cosmetic and never justify changing any of these identities.

The binder's original position/dependency order is preserved in the allocated
frame. A logical binder internal to an imported contract may produce its
lawful witness when that contract is evaluated; keeping the binder unchanged
is not fixing one witness across all future demands. Conversely, existing
shared binders remain once across instances. No independent per-port witness
is allocated. Description-frame allocation and actual event activation are
different operations: freshening `a` never manufactures a new runtime object,
receiver, operation instance or grant.

Every alias of one incoming frame uses that frame's single `rho_u`. Distinct
independent use frames may have `rho_u` and `rho_v` with disjoint local ranges,
while referencing the same `G_z`, actual captured object and fixed anchors.
This is only the lawful partition already specified by Source Generalize.

### Dynamic arguments

At evaluation, write `delta` for the complete jointly scoped assignment of
actual live event/world/history/whole carrier and invocation/evidence fields.
It supplies the original `nu,K,D` correlations; it is not a tuple of separately
satisfiable marginals. Event binders and dependent continuations retain their
original scope/strategy order. Later event fields are supplied at their actual
activation, response or resumption scope, under the existing source law.

The graph's static incidence is evaluated with `delta.C_current`, not
`C_publication`. A fixed allocation/lifetime anchor can constrain the actual
current world without equating the two worlds. A captured authority origin
and current authority eligibility are different operands. The preservation
lemma ranges only over `delta` satisfying H6, including all independently
admitted arbitrarily long finite histories. No finite history grammar is
substituted for that quantifier.

## 5. Conditional preservation lemma

Let `D_J(delta)` be the independently admitted complete challenges of the
import's existing public contract. Let `P_J(h,delta)` be its full observation
contract, including pending/complete observations, continuations/future
developments, hard bounds and dependent evidence at original scopes. These
are independently given meanings of H1, not a retained source image or `M_E`.

For every genuine `Act(v_z,U,r)`, its same-provider obligation is:

```text
for every compatible delta and h in D_J(delta):
  U accepts that same whole h at its original live indices;
  every actual pending/complete observation and admitted future development
    of that invocation of U satisfies P_J(h,delta) jointly.
```

Define `D_G,P_G` by the same supplied public clauses wired through `G_z` and
H4's public interpretation. This definition names the proposed interface
surface; it does not assert that any existing compiler root exposes it.

**Lemma.** Under H1–H6, for every lawful local frame map `rho_u` and every
corresponding original-scope assignment/strategy:

```text
D_rho(G)(rho(delta)) = D_J(delta)
P_rho(G)(h,rho(delta)) = P_J(h,delta)
Act/capture/provider coordinates are identical on both sides.
```

Consequently the import's same-provider obligations hold after attachment and
instantiation exactly when they held before, for each genuine decomposition.
If an obligation fails for the imported actual provider, graph transport
preserves that failure; the graph does not turn it into membership.

**Proof.** By H2 each clause's ordered typed operands are the same original
coordinates. Closure retains every operand, binder and public dependency by
H3, including repeated incidences and fixed free fields. Transport a complete
valuation by assigning each local `rho_u(a)` its old `a` value and leaving all
other fields unchanged. Injectivity and capture avoidance give an inverse on
the allocated local frame. The parent/dependency tree and shared witness
incidences therefore agree, so quantified binders retain their strategy order
and local-to-fixed residuals have the same truth values.

At a primitive/public leaf H1/H4 give the same independent relation on the
same ordered tuple; no source constructor or query success is invoked.
Conjunction and whole-tuple alternatives preserve truth by the same valuation,
without choosing separate port witnesses. Original scoped binding preserves
truth by the valuation/strategy bijection. A public reference resolves to the
same contract/version with unchanged fixed/imported operands by H4. Cyclic
references use their already supplied meanings; this step is not an induction
assuming the cycle proves itself and supplies no new fixed-point theorem.
If the supplied meaning is a positive finite-derivation grammar, the same
rule-by-rule correspondence transports every finite derivation in both
directions. If its established hereditary meaning uses a different fixed
point, H4 must already give its reference law; this lemma does not replace it
with positive finite unfolding.

Thus the complete admission and observation formulas have identical truth
values under corresponding joint assignments. In the imported subgraph
`rho_u` fixes every operand, so its dynamic arguments are literally the same
actual `delta` fields. H6 selects the same compatible domains/current worlds.
Every genuine `Act(v_z,U,r)` and actual invocation remains the same: the map
cannot change `v_z`, U, r or the live receipt. Applying the two formula
equalities to the displayed universal obligation yields its preservation,
including every pending prefix and compatible future demand. QED, conditional
on the explicit public clause/reference/embedding and compatibility premises.

This proves an import transport lemma. It proves neither that all D0
primitive images satisfy their ordinary descriptor guards, that a whole
`pick` descriptor is complete, nor that its production alternatives preserve
the admission domain. In particular, H1's import truth is not inferred from
an evaluator that merely implements the graph's assumed transitions.

## 6. Adversarial cases and precise stopping points

| Case | Construction consequence and exact unresolved premise |
| --- | --- |
| Public dependency cycle `c_z -> c_1 -> c_z` | Index each supplied node once; all edges survive, so construction terminates under H3. Semantic circularity is not discharged. Without an independently established interpretation/reference law for the SCC, H4 fails. Alternatives are using the established SCC contract with its own certified meaning, or proving an applicable SCC interpretation separately. Choosing least versus greatest interpretation here would be a new semantic choice and is stopped. |
| Multiple equal endpoints | Keep endpoint declaration/incidence identities and repeated argument indices. Equal denotations can be recognized by an independent existing equality law but do not identify providers, slots, binders or witnesses. A quotient needs its own joint preservation certificate; no quotient is performed. |
| Two captures share `B` but have distinct actual providers | Retain `k_z -> (v_z,i_z,c_z)` and `k_w -> (v_w,i_w,c_w)` separately; common `Endpoint(B)` sharing is permitted. Admission and future obligations use each original provider incidence. Sharing a contract reference is lawful only if its ordered value/provider arguments remain distinct where originally distinct. Endpoint equality supplies no provider alias law. This is an incidence audit, not a new endpoint-only collision experiment. |
| Two captures actually alias | Share the certified actual value/provider node and relevant shared dependencies, while keeping two occurrence indices. Independently copying their evidence/coordinates would destroy the original alias relation. Source formation's alias certificate is required; graph shape cannot infer it. |
| Unauthorized identity renaming | Any map changing fixed `v_z`, a provider origin, `c_z`, shared lifetime/authority anchor, imported binder, static slot or required fixed description lies outside H5. Matching printed types does not make it lawful. See the small graph-law falsifier below. |
| Transitive fixed dependency omitted | Closure is sound only against an exhaustive H3 dependency inventory. A successful traversal of listed edges cannot show that an unlisted free coordinate is irrelevant. Obtain the certificate at the public supplier's formation point; do not recover dependency from successful uses. |
| Dynamic world accidentally stored | Freezing eligibility at publication violates H6. Compatible future worlds still evaluate the original live guards. Static reference retention does not preserve protection as an active grant. Need the existing current-world compatibility law; an arbitrary mutable update supplies none. |
| Imported Option 2 observation | It remains subject to the complete independent public guard and future-domain obligations. No source witness is added. A graph that only retains source-generated alternatives lacks H1; a new abstract provider needs its own admission certificate, as source-contracts §3.7 requires. |

### Explicit graph-law falsifier: changing one fixed dependency

This finite algebraic witness attacks unauthorized fixed-coordinate freshening
rather than repeating an endpoint-only import collision. It is a falsifier
for a claimed unrestricted renaming law, not an established Yulang execution.

Supply one public import root, one rigid authority/dependency anchor `k0`,
one independent admission clause and one observation clause. The clause
relations are given independently:

```text
D_J(h;k0)       iff h.token = k0
P_J(h,O;k0)     iff O.token = k0
actual fixed U accepts h0 and produces O0,
  with h0.token = O0.token = k0.
```

The finite token domain is `{k0,k1}`, with distinct rigid constants. There is
one considered challenge `h0` and one actual observation `O0`. No search,
random seed, production license or source program is claimed. Under these
supplied relations, the actual same-provider obligation holds at that fixed
fiber. A mutant graph map keeps the actual provider and admission clause but
freshens the observation clause's required fixed anchor to `k1`. Then `h0`
remains admitted while `O0` violates `P_mutant` because `k0 != k1`. The
conditional preservation conclusion fails. This uses one shared fixed
dependency and two incidences; removing either the admission/actual invocation
or the observation incidence removes this particular membership failure.

Even a joint map of both clauses that changes `k0` to `k1` while the actual
provider is fixed is outside H5: the new `h1.token=k1` domain is not certified
for that U. Jointness alone does not authorize renaming an import. A genuinely
uniform isomorphism of an entire ambient token universe and every actual
provider might be a different semantic theorem; that theorem is not local
Generalize and is not assumed here.

The token interpretation is the witness's explicit candidate assumption.
No claim is made that a Yulang primitive realizes it. An actual source
falsifier would require the independent source/primitive interpretation plus
a compatible live-world witness. This algebraic example separates a graph
transport law from its needed fixed-incidence premise without assuming source
transition rules or certifying a toy evaluator as source correctness.

## 7. Why this is public graph wiring, and what it leaves open

`G_z` contains supplied public contract clauses and their typed operand/binder
references. It contains no initializer/body AST, latent body proof program,
source constructor inventory, source relation, source-root ID or deferred
source lookup. Contract evaluation consumes the current dynamic arguments;
it does not walk the source definition. The graph therefore meets the
accepted target's *syntactic boundary* conditionally on H1/H3. A public
contract clause implemented by an opaque reference to the full source
relation would fail H1; naming that reference `c_z` would not repair it.

An exact independently given public contract can have infinite challenge
and observation domains while its clause graph is finite. Finiteness of the
graph does not bound those domains, prove effective query recognition or show
that every source capture admits such a finite interface. Exactness and finite
public realizability are input premises here, not consequences of the graph
representation. The construction intentionally retains all supplied public
dependencies and does not prove any of them necessary or the import minimal.

The new theorem reduces the import transport work to typed construction,
complete dependency inventory, exact public interpretation and current-world
compatibility. It leaves untouched the premise that a concrete exact finite
`J_z` exists at the actual public supplier. An additional equivalent graph
probe would leave that premise untouched. The next useful method is a
construction-point audit or supplier definition that produces canonical
public incidence/dependency evidence before source information is discarded.
If that requires choosing a new embedding, recursion meaning or public
contract representation, return the alternatives to the primary for the
existing design/approval gate.

Unverified scope: arbitrary capture/import values; universal finite-summary
sufficiency; active ordinary-descriptor embedding; actual D0 guard suppliers;
S/T result policy; complete production W/Z inventory and changed-provider
domains; public-query resolver completeness; source admission adequacy;
principality/all-view factorization; generalized mutable State, adapters,
callbacks and recursive source components; compiler/runtime conformance.
Cycles here are public dependency cycles, not a new source-recursion theorem.
No gate is closed or reclassified.

## 8. Checks, independence and resources

Method: symbolic finite graph construction, valuation/strategy transport and
one explicit conditional algebraic mutation witness. Oracle independence:
there is no executable oracle or transition checker. The proof relies on the
independently supplied public primitive/reference meanings and their exact
incidence/embedding laws. It cannot prove those laws by interpreting clauses
that assume them. The witness uses independently stated token equality and
provider behavior; it is not source adequacy evidence.

Coverage: the tables explicitly examine finite reference cycles, repeated and
equal endpoints, distinct-provider captures, actual aliases, fixed-coordinate
renaming, missing dependencies, live-world guards and Option 2 extras. They
are proof cases, not an enumeration of source programs. No seeds, random
ranges, search shards or history bounds were used; no enumeration was started
or reported complete. The displayed mutation was evaluated symbolically only.
Failure conditions are the failed hypotheses H1–H6 and the exact cases above.

No numeric CPU/RAM/wall-time limit was assigned in the packet. Execution was
restricted to lightweight committed-file reads and serial note/hash/integrity
work; no build, test, formatter or heavyweight process ran. At most one shell
command was awaited at a time. Individual read/hash commands completed below
one second. Total research wall time, CPU time and peak RSS were not
instrumented. No timeout, killed process or partial search occurred.

Narrow checks already run before freezing: committed dependency reads and
SHA-256/current-byte equality checks; exact approved-draft embedding in the
approved answer; HEAD/branch/path status; note newline/trailing-whitespace,
code-fence and local-link integrity; path-specific diff whitespace check.
The note is untracked before primary integration, so the actual whitespace
inspection is the direct file check rather than relying on `git diff` alone.
Final dependency and integrity results are reported in the submission packet.

## 9. Pinned dependency hashes

SHA-256 of committed bytes at the baseline:

| Path | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6` |
| `rules/design-authority.md` | `925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `rules/question-board.md` | `8c617ceb978dfa26ce12f4f71ecc8ece22ffd8f1cf1982125b33142f645ae1c0` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| `notes/theory/2026-10-08-id-pick-d0-concrete-decoder-proposal.md` | `70aed32e52e777e82b53023c7451ffc1a7a1b07ab043dc78ba16e04ef0276f7b` |
| `questions/2026-10-08-successor-generalize-root-policy/question.md` | `69f43d833a0237523c88a26125f3cf4878e599e38903f84b458d437da662072b` |
| `questions/2026-10-08-successor-generalize-root-policy/answer-draft.md` | `6234a26dd6491b67d92b3f86421160becf52779ef3188b12fbe49fa84c28bbed` |
| `questions/2026-10-08-successor-generalize-root-policy/approved-answer.md` | `e358a5d796f0a26b2d7dbe5891b3d1f21d0ac9089ab655796fa0b696a13194e5` |
| `questions/2026-10-08-successor-generalize-root-policy/receipt.md` | `c3bb6fbab0e3ba431fca56b4b7cdca54278d66a3711eb47bf8b9f9a812322a42` |

## 10. Frozen commit packet

- Exact leased paths: `notes/theory/2026-10-08-pick-public-import-graph-derivation.md` only.
- Baseline SHA: `fe5cd0e946e8e45a628cbaed4d560288dc76c29c`.
- Changed dependency hashes: none observed against the pinned dependencies;
  recheck by the primary at integration if HEAD/dependencies move.
- Claim/review status: unreviewed research-only conditional graph transport
  lemma and algebraic fixed-coordinate mutation witness; no independent
  certification, adopted representation, source law, D0 closure or principality.
- Checks already run: bounded committed reads, 13 dependency byte/hash checks,
  approved-draft embedding, note integrity/local links, read-only status/HEAD
  and path-specific whitespace inspection; no tests/builds or Git mutation.
- Proposed one-line research-checkpoint commit message:
  `research: derive conditional public-import graph preservation for pick`.
- Shared-record deltas intentionally left for primary/curator: link this
  conditional import-transport result if accepted; keep exact finite public
  supplier/embedding/dependency completeness, D0 production and principality
  obligations open. Record no representation selection or new graph recursion
  meaning. No edits to task/index/authority/theory maps/question bundles are
  proposed as part of this lease.

Recommended next action: audit one concrete established `z` public-contract
supplier at its construction point for H1–H4, retaining canonical typed
incidence and fixed-dependency evidence; seek a focused independent review of
this frozen conditional lemma before promoting its status.

Writing stops before frozen review submission.
