# Replay constructor lineage: source branches and specimen correspondence

Status: working candidate source/native derivation; runtime application pending.
Author: `/root/replay_constructor_proof_20261018`; no descendants/coauthors.
Requested Sol/high; observed model UNKNOWN, effort UNKNOWN.
Sprint `npair-replay-constructor-lineage-20261018`, contract revision 2,
SHA-256 `b04f61d76511ebca81ed5217bf8ba0ec76fdaa3035a212123031e4079005ad80`.
Labels below distinguish **Source fact**, **Observation**, **Conditional
inference**, and **Unknown**. No independently reviewed theorem is asserted.

## Parent and exact application

The parent is `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`: construct the
authentic negative formal pair, ordinary formal edges and contribution/permission
association through `f () -> install(g) -> fresh local use -> g ()`, in the
unchanged source domain. Every original provider, assignment, context, world,
occurrence, typed position, guard, continuation, interaction, Call demand and
future remains quantified at its original dependent scope. Fixed `c`, independent
J1/J2, initializer effects, provider/witness/residual lineages and F1/FK1 remain
unchanged. Parent OPEN; original-condition closure **0 -> 0**.

The source branches below identify exactly when a native row image is shared
or fresh, and which constructor facts can classify this one cross-route join.
They supply neither a complete dependent NPAIR map nor authentic ingress for an
unobserved provider. Ordinary generation, accumulation, propagation, levels,
extrusion, qualifying Value-SCC intrusion and generalization remain required.

Governing semantic authority: inference principles dated 2026-10-11, §§1/1.1;
adoption receipt dated 2026-10-17 and the exact NPAIR proposal §§2-4. Adoption
provides definitions; N-Transport and N-Subtract-Elim remain obligations.
The native implementation contract §Frozen inputs records CLEAN review of L1
and local L2 under their premises, L3's absent whole-presentation J2 map, and
L4's limited contribution-node allocation result. None is broadened here.

## C1: capture classification

**Source fact.** At the intake source bytes, `Capture::intern`
(`candidate_scheme.rs:694`) canonicalizes endpoints; `Capture::row` (:706)
resolves `intrusion.rep(key)`, returns an existing captured row on a key hit,
or reads that representative's current level/metadata and inserts exactly
`Row { key, local: level > boundary && !non_generic }`. Thus a newly inserted
captured row has stored local true iff both strict-level and genericity tests
hold at that capture. Stored local false follows from level <= boundary OR
non_generic. Invalid/missing owner state returns an error, not a successful row.

**Source fact.** `Capture::expand_row` (:996) returns immediately for !local;
the older coordinate's mutable bounds remain session-owned. Capture is not
asserting that those bounds are empty or that later constraints cannot arrive.

**Conditional inference.** A recorded capture row with local false is anchored
at this stage, regardless of a later genericity/level improvement. A capture
key already present in the capture map reuses its first stored classification;
a later key hit does not establish a new metadata snapshot. Actual capture
occurrence, hit/miss and stored-row provenance must accompany a claimed fact.

## C2: reconstruction over representative fibers

**Source fact.** `prepare_candidate_fresh_use` (:1491) begins a distinct use and
an empty per-use `canonical_rows` map. In graph-row order i, define source s_i
as the current `intrusion.rep(graph.rows[i].key)`. Read its current level L_i
and non_generic N_i. Let M_i be the canonical map just before processing i.
Successful construction obeys exactly:

```text
s_i in dom(M_i): image_i = M_i[s_i]; no allocation; M_(i+1) = M_i.
s_i not in dom(M_i):
    g_i = row_i.local && L_i > graph.boundary && !N_i
    image_i = fresh_row_at(use_level) if g_i, else s_i
    M_(i+1) = M_i with s_i -> image_i
rows[i] = image_i
```

**Conditional inference.** Induction over this actual loop proves that all
entries encountering the same representative use the image created by its
first encounter. On a miss, g_i false retains s_i; g_i true allocates a row
of the same Value/Effect kind at use_level. On a hit, even g_i true does not
allocate. A later row's stored local flag is not consulted to choose its image.
This proof does not assume representatives are immutable while allocations
occur; a hit is defined by the actual s_i and actual M_i at that iteration.

**Conditional inference.** If representatives stay fixed during the loop, let
j(s) be the first index in that representative fiber. Every image in that
fiber is determined by g_j(s). Distinct captured keys can have the same current
representative after intrusion, so per-row freshness cannot be inferred without
the map hit and first insertion. If two such captured rows have different
stored flags, the source still follows the first entry's decision. Whether
that combination is actually reachable and semantically permitted is not
proved by this abstract case analysis; it is not a demonstrated compiler bug.

**Conditional inference.** Two independent successful uses can share the same
anchored representative while retaining different use identities, transports
and reconstructed Function terms. Fresh allocations in distinct uses are
distinct allocations at construction time; later ordinary equality may equate
their representatives. Numeric row equality does not identify those uses,
source occurrences, provider witnesses or residuals.

## C3: per-route reconstruction square

**Source fact.** For each exact captured Graph G and actual use u, Graph row
indices belong to G; `fresh_u.rows[i]` is indexed by those same indices.
`Node::Row { row:i, polarity:p }` reconstructs a live term for image_i with p
(:1655). `Node::Function { children:[a,ae,re,r], polarity:p }` reconstructs
the four already reconstructed children in that exact order (:1669).

```text
captured endpoint x --capture/canonicalization--> exact (G,row i,node n)
          |                                              |
 current representative at reconstruction              rows_u[i]
          |                                              |
          +-- actual M_u hit or miss branch ----------> image_u[i]
                                                         |
                                     live term with original polarity
```

**Conditional inference.** The square commutes by the actual map writes and
Row term constructor for this G/u. A Function's four endpoint squares compose
with its ordered constructor. This is structural correspondence, not a map of
every dependent NPAIR judgment. Module route0/use1 and route1/use2 require
separate squares. Equal node indices, source support, family names, or a final
row 44 do not establish equality of their graph domains or source occurrences.

## C4: producer -> admission -> Replay -> consumer requirements

**Source fact.** `candidate_bound_origin_with_evidence`
(`candidate_effect.rs:457`) constructs OwnerEmission/FreshUse-specific admission
relations. `candidate_insert_bound_with_evidence`'s physical append path
(`candidate_extrusion.rs:499-667`), called by `candidate_begin_bound_restoration`
(:763), canonicalizes owner/item, admits, appends to
the matching lane, reads the exact physical slot back, checks its BoundKey,
and retains an admission-linked emission. OwnerEmission's processing relation
is evidence of that producer, not a FreshUse occurrence identifier.

**Source fact.** `begin_candidate_fresh_bound` (`candidate_scheme.rs:1767`)
uses reconstructed endpoints, preserves bound orientation, and creates one
FreshUse transport with its actual use, source bound, scoped relation and
imported antecedent before physical admission. Anchored row sharing does not
erase that separate transport/use evidence.

**Source fact.** `candidate_context_begin_replay` (`candidate_context.rs:3719`)
enumerates retained lower/upper fibers; forms the ordered task pair; unions
source support; rejects a lower demand; composes transformer flows and takes
the upper demand. It retains both a recipe and `Dependency::Replay` connecting
the child, lower/upper relations and exact lower/upper BoundKeys.

**Source fact.** `authenticate_replay_ancestry` (:2749) checks exact bound
membership, ordered pairs, one Replay dependency, one FreshUse witness and
demand/root/flow correspondence. Its four distinct FunctionPort children have
fields [A,AE,RE,R], operations [Swap,Swap,Preserve,Preserve], identity A/R
transformers, input-stamping AE and body-protecting RE. Their concrete pairs
still need comparison with both actual Function port arrays. An existing
FunctionPort of the right kind is insufficient evidence of that comparison.

**Source fact.** Actual Function dispatch (`lib.rs:12648`) for positive lower
L=(La,Lae,Lre,Lr) and negative upper U=(Ua,Uae,Ure,Ur) constructs these ordered
port pairs, preserving component kinds and polar interpretation:

| Field | Lower endpoint | Upper endpoint | Operation |
| --- | --- | --- | --- |
| A | Ua positive | La negative | Swap |
| AE | Uae positive | Lae negative | Swap |
| RE | Lre positive | Ure negative | Preserve |
| R | Lr positive | Ur negative | Preserve |

This table is the concrete falsifier for a swapped route/port or an incorrect
same-route assumption. Actual endpoint canonicalization must be included when
comparing row-valued ports; distinct structural Term IDs alone do not prove a
port mismatch or a valid source edge.

**Source fact.** `candidate_context_step_replay_child` (:3827) passes an exact
retained child relation and ReplayChildAck into `start_typed_drain`
(`lib.rs:12272`). The start preserves a supplied relation via `item.relation.or(seed)`.
The operation records its drain index and ack; subsequent steps validate
those and occurrence/cause. Terminal handling (`lib.rs:12728-12793`) prepares
the exact return, retains completion in ReplayChildWait::Ready and pops the
drain. The Ready branch checks consumed/queued counters and drain-stack length
before Delivered. Merely finding a child or drain start proves no completion.

**Unknown, pending reviewed runtime.** For the specimen the required full chain
is actual lower relation/source occurrence -> admission/emission physical owner
-> shared or fresh image under both route maps -> upper relation and selected
demand -> exact Replay child -> four concrete FunctionPort pairs -> actual
drain/return result. Historical names Relation58/admission56/emission56,
upper35/Replay61 and row44 identify the prior specimen only; no new numeric
identity is assumed before observing the new run.

## Runtime application, correction prerequisite and remaining parent

**Unknown.** No new runtime receipt has yet been supplied. No ownership
classification, successful drain, observation-test pass or compiler correction
is justified by this working artifact. This section must incorporate Luna's
reviewed observation and exact source/runtime hashes before final freeze.

**Conditional inference.** If both constructor squares select one current
anchored representative and the actual producer/port/drain chain agrees, the
shared native join is supported for that specimen. If a required miss/fresh
image or map/port incidence is demonstrably lost, a correction first requires
the actual owning constructor and violated guard/map to be identified under
independent review. If an edge is unobserved, name its first missing fact and
owner rather than selecting either alternative. No authenticator relaxation
or source-domain restriction follows from any of these cases.

The unchanged original transport question still requires authentic source
ingress, the complete dependent map through all allowed operations, future
lower coverage and the real residual consumer. Original ?e_Op, F1/FK1,
complete Call/effects, soundness, principality and termination remain open.
This specimen cannot discharge those independent quantifiers.

## Evidence, reuse and finalization state

Intake verified r1 contract and all ten frozen inputs; r2 hash verified before
any writing. Reuse: prior CLEAN cross-route audit's observed IDs and omitted
fields, plus its source locators. Refine its reconstruction statement by the
canonical-map hit branch and first-entry order. Reject same-route containment,
equal graph indices, family equality and source-support union as substitutes
for authentic occurrence/map correspondence. Historical negative-annotation
refusals concern their old bytes, not a conclusion about this new run.

New paths: this note and the single assigned proof inbox only. No scratch,
tests, builds, Git, descendants or code writes by this author. Resource cap
420s, Astra0; timestamps and spent/remaining resources will be recorded at
freeze. Artifact and handoff are not frozen yet; runtime application pending.
