# NPAIR use-certificate retention across local commit

Status: candidate conditional design invariant; independent review NOT RUN.
Assignment: `NPAIR-USE-CERTIFICATE-RETENTION-20261017`, revision 1.
Author/worker: `/root/npair_use_certificate_retention`, sole author; no descendants.
Requested role/model/effort: prover / `gpt-6.1-sol` / high.
Observed model/effort: UNKNOWN / UNKNOWN; no effective-settings metadata supplied.
Sprint: `npair-commit-retention-repair-20261017`, revision 1, SHA-256
`bdb5f6fb16d7dba84fca79c0197775e2ea23bb3bd49856b324fcd2152b13a6ee`.
Administrative baseline: `ab32591e91d0759620a2b9d3d0d54513fb4a0f73`;
compiler baseline: `74bfaa6a8ce0a60051e40e531c54576516d6c151` (supplied labels; no Git).

## 1. Parent application and limit

The original parent is **CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017**:
authentic negative formal formation and the ordinary route
`f () -> install(g) -> fresh local use -> g ()`, with all original providers,
assignments, contexts, worlds, source occurrences, typed positions, guards,
continuations, interactions, Call demands and futures. Accepted source domain
and complete dependent predicates are unchanged. F1/FK1 remain independent.

This note identifies a local information-retention requirement and proves a
finite query-factorization lemma for a proposed committed use record. It does
not construct whole native `rho_u`, an authentic NPAIR producer, a complete
replay interpretation, an extrusion/intrusion theorem, or a receive subtraction
consumer. Current native code does **not** implement the proposed retained
record. All those gates and the parent stay OPEN.

Apply the result to the parent's J2 route as follows: the conditional anchored
J2 lemma already supplies, under F/A/R/U, the actual second result-effect route
with original `D,w,delta` and new use `u`. Before destruction of FreshUse, retain
that exact packet's identities, its actual route operands and unresolved tail
references under the committed use owner. Later consumer queries on that packet
then need no recovery of FreshUse's discarded maps. This removes a storage
obstruction **conditional on constructing and retaining that packet**; it does
not establish its missing source/native premises or existence of a consumer.
Neither B1 nor J1 supplies the actual J2 demand or selection evidence.

## 2. Source facts at the pinned bytes

All locators here refer to `crates/yu-solver/src/`. Inspection only; no execution.

- `candidate_scheme::Graph` (:38–54) retains source frontier/owned regions,
  negative-Function indexing, nodes, rows, bounds, bound snapshots, attachment
  references/spans, context views, root/live_root and boundary. `Capture::intern`
  canonicalizes endpoints; `expand_node` (:493–596) keeps all four Function
  children with proper sorts/polarities. `expand_row` (:645 onward) stops at
  nonlocal rows whose live bounds remain in session. Capture is not a closed
  semantic presentation and does not itself retain NPAIR descriptors or At.
- `prepare_candidate_fresh_use` (:1104–1378) allocates `context_use`; maps rows
  according to current representative, level and non-generic rules; reconstructs
  terms; records effect-operand images, bundle/context/scope maps and imported
  snapshot IDs. Each processed Contribution node receives a new native instance
  with its old effect and source origin (:1177–1196). That fact does not map the
  complete semantic provider/assignment/witness tuple.
- Scoped demand reconstruction (:1294–1318) changes `use_instance` only for an
  input owned by the scope map. External demands keep their original use
  instance. ScopeRemap has distinct region, scope and input maps
  (`candidate_source`:105–109); identity outside the owned domain must not erase
  its owned/external distinction. `ScopeInventory::fresh` (:212–270) retains
  source origins and actual copied region parents, attaching copied roots to
  the caller. This is not a lexical eligibility proof.
- `begin_candidate_fresh_bound` (:1380–1428) reads exact mapped value/effect
  endpoints and owner polarity; constructs a child relation using context_use,
  mapped context and optional scoped flow; attaches mapped bundles; and supplies
  the imported antecedent, source BoundKey and mapped relation in
  `BoundAdmissionCause::FreshUse`. Native target relations, admissions,
  emissions, snapshots and scope records can survive separately in their
  session owners. They are useful inputs, not a complete At judgment.
- `step_candidate_local_use` (:1664–1710) restores represented bounds before
  publishing the mapped root-to-local-value link, reserves route storage while
  fallible work remains and marks the frame complete. This establishes an
  ordered represented-bound frontier, not complete dependent source replay.
- `lib.rs::finish_route_transaction_with_candidate_accounting` (:9281–9331)
  calls `commit_local_use` only in the successful branch after complete status.
  The error branch rolls back the private attempt. The commit itself has no
  fallible promotion hook in these bytes.

### Exact commit inventory

`GraphState::commit_local_use` (`candidate_scheme`:267–292) pops the LocalUse
frame and moves only these fields to `LocalFreshRoute` (:140–147):

| Retained in committed route | Discarded with FreshUse/frame |
|---|---|
| slot, local identity, source occurrence, whole Graph, `fresh.rows` | scope_remap, scoped_relations, context_use, terms, effect_operands, bundle_remap, context_remap, evidence_remap; frame value/level/cursor |

The row vector is an explicit old-graph-row-index to target-row crosswalk.
The graph retains source-side nodes/bounds/snapshots. That combination does not
retain every target contribution/term, per-use evidence or context image.
`released = fresh.bytes() - rows.capacity()*sizeof(RowKey)` accounts precisely
for releasing construction allocations. Some scalar data are also dropped.
The optional `cfg(test)` census copies selected maps only for requested
occurrences; it is not production retention and excludes other fields.

The distinction is essential: target native records may remain; the table says
which route-owned **crosswalks** cease to exist. It does not assert that every
lost image is impossible to find by some global search. No proved lookup from
the surviving route to the required complete NPAIR tuple exists in these inputs.
Reconstruction by family/origin/row shape is unsound as an identity criterion.

## 3. Proposed query projection, without selecting a code representation

This is the bounded logical payload that Luna's candidate must account for.
It is not a new authoritative runtime API or production storage decision.
Let `S` be a successful pre-commit construction state while its Graph/FreshUse
and restoration receipts are still available. Let `u` identify this actual use,
including session generation and local occurrence. Source origin and current
use identity remain different coordinates.

Define the following finite query language **Q** for already registered use
packets. Its results are typed operands plus evidence status; a successful
lookup never means permission to subtract.

1. Find the original descriptor and permission operands at the exact annotation
   occurrence and Function path; return shared port image and its source link.
2. Find the particular original contribution/provider lineage and its actual
   destination endpoint for this use; distinguish a shared anchor from a copied
   node and retain the correspondence evidence or its missing premise.
3. Find the ingress derivation and transport route to this use/demand, including
   original predecessor dependencies and four-child comparison positions.
4. Find actual mapped receiver coordinates and original lexical coordinates,
   owned/external scope/input status, and the original demand's own use identity.
5. Enumerate dependencies, coverage gaps and pending requirements; check whether
   a packet is still valid or pending and which future observations it requires.

Q does not include deciding complete Call, selection/matching, closed-world
absence of a future At, or reconstructing arbitrary uncaptured source evidence.
Those operations require the missing source/consumer premises.

A sufficient retained projection `P_u(S)` consists of the following **related**
records (references may replace copied payload only with the lifetime below):

- A Use header: session/generation, distinct u, actual local occurrence and
  installed root/graph identity, capture boundary/frontier, caller coordinates,
  actual publication link and target value. An actual later call/demand is
  associated explicitly when supplied; no guessed J2 is installed at capture.
- A port instance: original D identity and full descriptor operands
  `(O,b,alpha,path,sigma,K,V,C_sym dependencies)`, Permission references,
  original/current shared-row coordinates and typed correspondence status.
- A contribution incidence: original w identity and full provider/observation,
  assignment, position and lineage dependency references; exact source node or
  anchor; actual target contribution endpoint; D/u association. Native effect,
  origin and allocated instance remain separate fields from semantic w.
- A derivation reference: original delta, actual mapped ingress/transport
  derivation if authenticated, its premise references, comparison fields,
  bound kind/side/source BoundKey and exact target BoundKey/relation where used,
  imported snapshot ID and unchanged coverage gaps. Retain actual restoration
  receipts as structural evidence; they do not fill missing source antecedents.
- A scope/context projection restricted to operands used above: source and
  target region/scope/input, owned/external tag, caller parent link, context
  and scoped-flow images, actual demand root/original_call/use_instance.
  Bundle references are retained only if needed as provenance, never as At.
- A dependency frontier: typed edges to every original predecessor required by
  these records, plus pending tail/future/association requirements, their
  stable source anchor/event keys, use/scope identity, coverage and validity
  state. A missing dependency is explicitly Pending, not an empty list.

This is a minimum **category** projection for Q, not a theorem of byte-minimal
storage or independence of every field. A field can be omitted only when a
proved total lookup through retained stable records gives that same operand
and status. Retaining all FreshUse maps is sufficient for structural lookup
but still does not create missing semantic evidence. Conversely a bare u,
Graph and row vector do not supply the stated crosswalk by definition.

Construct P while S is available: enumerate registered packets and their Q
operands; evaluate structural images through the actual FreshUse maps once;
record the exact images/receipts; follow dependency references to a finite
retained closure or to explicitly pending leaves. Never fill a semantic hole
by evaluating a structural map. A source-typed image which is absent is a
named Pending dependency and its owner, not an authenticated record.

References target immutable records, or versioned mutable records with an
observable validity state. Session ownership pins every transitively referenced
record while a use, consumer, graph, pending request or undo state refers to it.
IDs are not silently reused; invalidation marks dependent records Pending before
any dependent residual is published. Failed attempts expose no certified
partial tuple. One may discard the failed private attempt; exact capacity
restoration is not a semantic requirement.

## 4. Bounded retention lemma and proof

**R1 (conditional query retention).** For each successful S and finite
registered packet set, suppose:

(a) P is constructed as above, recording every Q field or explicit pending
leaf, with no loss of original identity/dependent scope;
(b) referenced dependency closure and validity statuses survive commit;
(c) promotion is atomically visible with the committed use, and no consumer
can treat Pending as authenticated or publish a solved dependent residual;
(d) subsequent state changes update/invalidate the relevant versioned records
before affected consumers run.

Then after destruction of FreshUse every Q query on those packets returns the
same operands and status as its pre-commit evaluation, modulo the explicit
updates in (d), without reconstructing any discarded map. In particular
`q(S)=q_retained(P_u(S))` at commit. This statement preserves missing-evidence
status as well as successful images; it proves no missing image exists.

**Proof.** For header/port/contribution/scope leaves, use the exact stored value
or dereference the pinned identity: promotion copied the actual pre-commit
image and tagged its source coordinate, so equality holds. Pending leaves
return their original requirement and owner, not a witness. For derivation
nodes, recursively look up the same ordered premise references and stored
comparison/transport labels. Induct on the finite dependency expression;
shared subexpressions are evaluated once by identity. A cycle of ordinary
row constraints is retained as graph structure, not recursively unfolded into
a finite derivation. If a requested proof depends cyclically on itself without
an established proof object, it remains Pending. This gives equality for
composite Q results. Lifetime (b) makes every dereference valid, (c) prevents
a reader observing a half-promoted tuple, and (d) preserves the same reasoning
for each later query at its current versions. No proof step uses FreshUse
again. Thus q factors through P. End proof.

This is stronger than retaining a snapshot of successful answers: it retains
the reason for Pending, complete dependency references and invalidation hooks.
It remains conditional on completeness of the chosen packet projection and
on producer/consumer protocol enforcement. Neither follows from present code.

**Future lower boundary.** A fixed finite P cannot precompute an unbounded
future contribution/derivation. A live anchor subscription may supply a later
actual delta and a new packet, retaining original w and a fresh route u;
shared-anchor cases can use the prior anchored lemma under its same premises.
For a copied future dependency, either its required correspondence is already
in the retained domain or its owning source operation supplies and authenticates
a new image. Otherwise the request stays Pending and returns to that owner.
R1 proves finite lookup for each supplied packet, not total future generation,
fair wake-up, completion or normal progress. A subscription without an event
producer/progress argument cannot discharge that gap. No absence of an At
observation proves permanent ineligibility on an open port.

**Necessity discriminator.** Two distinct w values or uses can have identical
family and canonical row. A query choosing which one has At must return
different lineage operands. A representation which forgets that distinction
cannot answer both faithfully; it needs a retained discriminant or proved
lookup. This is an information-loss argument about the query interface, not a
new source-qualified counterexample or proof that both particular native
histories are reachable. It excludes family/row-only recovery without inventing
an implementation failure trace.

## 5. Integration obligations and exact obstruction

The candidate sentence “FreshUse retains the explicit remaps” covers only the
construction/restoration interval. Correct its later-consumer claim by assigning
P to a committed route/session Use owner **before** final fallible work ends.
`commit_local_use` is currently an infallible move boundary, so allocation,
closure validation, reservation/accounting and atomic-publication preparation
must precede that boundary in any later approved implementation. Commit moves
or attaches the prepared record; errors cannot leave an authenticated fragment.
Do not change ordinary constraint generation/propagation or defer actual
inference merely to make this evidence argument easier.

For finite registered packets, storage can share immutable descriptor and
premise/derivation DAG records. If V unique retained records, E dependency
edges, I lookup entries, W pending subscriptions and U undo/version references
are retained, charge all their capacities and payloads: O(V+E+I+W+U) plus operand
payload sizes and required map fragments. This is an accounting formula, not a
bound on how many distinct derivations the solver generates. Avoid enumerating
all paths through a shared DAG. Deduplication requires identical complete
operands/dependencies; it must not identify distinct providers, uses, witnesses
or residuals. No global termination or resource-fit theorem is claimed.

The first semantic obstruction is unchanged: native negative formation refuses
the concrete annotation before authentic D/Permission/At is constructed;
structural replay lacks complete source-typed antecedents. In
`candidate_context::admit` (:684–702), OwnerEmission/ExtrusionLink record
`ProcessingAntecedentsUnavailable`, `OrdinarySeedAuthenticationUnavailable`,
`MissingAntecedent`; FreshUse inherits gaps and adds
`ReplayUseAntecedentsNotRetained`. A retained certificate can preserve those
facts, not promote them to authenticated source derivations. The strongest
justified claim is R1 plus the direct source inventory above.

## 6. Mutual TODOs and next step

- **NPAIR-RETENTION-PROMOTION-20261017** — Luna's already leased candidate repair:
  specify P owner, finite query domain, pre-commit preparation, atomic transfer,
  lifetime, invalidation and complete capacity accounting. Input: this R1 and
  exact source pins. Falsifier: any post-commit consumer needs FreshUse-only
  data or a dangling/unversioned dependency; Pending can publish a solved
  residual; two uses/providers collapse. No code lease is requested here.
- **NPAIR-REPLAY-AUTHENTICATION-20261017** — original candidate_context and
  capture/replay source owners: provide typed original antecedents and lawful
  provider/use actions for copied packets. Falsifier: bound snapshot, bundle
  copy, matching origin or row equality alone becomes At. Requires a later
  exact source/proof packet; this assignment stops at that boundary.
- **NPAIR-PENDING-EVENTS-20261017** — Function/constraint and publication owners:
  identify direct/annotated arrivals, future lower notifications, registration
  before races, wake-up/completion criteria and progress. Falsifier: an earlier
  direct route finalizes before the same-contribution incidence can arrive,
  or an open port is classified permanently ineligible from missing evidence.
- **NPAIR-NATIVE-INTRO / NPAIR-RESIDUAL-OWNER / NPAIR-SYMBOLIC-COVERAGE** — retain
  existing owners and OPEN status: candidate_formal_pair/formal_effect_port,
  candidate_signature_effect/formal_annotation and preflight_formal must realize
  actual adopted formation; original effect-elimination owner must identify
  real demand/selection/scope at receive; formal signature owner must supply
  original mixed/multiple-symbolic C_sym. Extrusion and qualifying Value-SCC
  intrusion still need their actual correspondence proof. No Catch consumer,
  f0 substitution, synthetic source restriction or bypass is supplied.

Next in-envelope step belongs to Luna: repair the leased Draft candidate using
R1, then arrange fresh independent review. This producer cannot certify this
note or the repaired combined artifact. No further leaf work is running.

## 7. Reuse, frozen dependencies, resources and cessation

Reused: reviewed L1–L4 only for authentic graph/local incidence premises,
ordinary J1/R1 consequences and native per-node contribution allocation;
reviewed conditional anchored J2 only under F/A/R/U. Rejected: whole-rho_u from
row maps, At from native snapshots/bundles, family-based identity recovery,
permission as inflow/cap/empty, Catch experiment as receive subtraction,
foreign-continuation closure from a local action. Original inference levels,
extrusion, qualifying intrusion, accumulation and generalization remain intact.

All following SHA-256 values were recomputed from actual dependency bytes:

| Dependency | SHA-256 |
|---|---|
| adopted NPAIR proposal | `0a73aaf7016e86dd5babbdd5482b05a793764418bc003607207ef0375ee46006` |
| adoption receipt | `d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa` |
| corrected native readiness contract | `36d9792d7a5bb4d06beeb4a1c62df28d38ff171fc324783061c2219a970ce064` |
| prior architecture candidate | `278e1de992421fc237468a266eb3051388ea3c7e5019ca4f95daf9fe72ff96e6` |
| whole-presentation/anchored J2 note | `cc9aee77661de00ac011a9da411b385e9e440277bb194bc13a83d71f973b0719` |
| adopted-negative-pair L1–L4 note | `6a3c6b5754448b38430ee368feb52d87ebd38c1b7050c3b33652132ead5f0fb2` |
| top-level inference principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| candidate_scheme.rs | `2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e` |
| candidate_context.rs | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` |
| candidate_effect.rs | `44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9` |
| candidate_source.rs | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| candidate_extrusion.rs | `2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b` |
| candidate_receiver.rs | `620b09011ec4dc4bfa71998e2b6fc1498b9299b3056662fdaa80b17376ba23c3` |
| shadow_apply.rs | `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf` |
| lib.rs | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` |

Dependency authors: proposal `/root/negative_formal_pair_proposal`; L1–L4
`/root/adopted_npair_construction`; anchored note as recorded in its frozen
artifact; contract/adoption/plan/candidate Luna/primary provenance; native source
authors UNKNOWN. No borrowed result is attributed to this author.

Four substantive stages: authority/pin read; actual source lifecycle audit;
projection construction/conditional proof; parent application and frozen handoff.
Checks: textual inspection and SHA-256 only. No tests, builds, probes, compiler
execution, Git, descendants or external contact. Cap 240 seconds; reserve/charge
the full 240 seconds conservatively, exact launch-to-stop elapsed UNKNOWN to
this leaf. No continuation budget requested. All scratch was in memory/command
output. Only new paths are this note and the assigned inbox file. Writer STOPPED
upon freezing revision 1 and sending its receipt; no descendant leases exist.
The inbox carries this note's byte hash; its own final byte hash is sent to Luna
without a self-referential hash field. Pending independent review/integration.
