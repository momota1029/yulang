# One native PE new: constructed frame action and root supplier cut

Date: 2026-10-10
Baseline: `68ea68fa3b0a73fff05f28c631e9f49be076ebf6`
Branch: `research/simple-sub-intrusion`
Status: frozen at submission; unreviewed, non-authoritative research derivation
Exclusive lease: this file only
Gate: selected PE Decode/new sublemma; no IFACE_EQUIV or CI_USE closure
Production implementation / semantic selection: none

## 1. Objective, authority and result

Trace one real `new(id,i)` and its alias through the selected public decoder,
extending the prior fixed-fiber result beyond its supplied frame and root
outputs. Method: constructor induction on the explicit source allocation keys
and the seven public root equations, followed by an allocation-supplier audit.
No checker, allocator implementation, source API or new language rule is used.

The selected clauses construct the frame incidence and equation **schema**
from the export and original allocation grammar. Its transport below follows
without a supplied decoded root. They also require a fresh ordinary public
root and literal same-root alias reuse. They do not define a root identity
key, allocation-state transition, nominal action on registered root handles,
or changed-identity readout law. Consequently they do not prove a commuting
square for actual `Decode` outputs. The exact unsupplied portion is §5.

Governing sources at the pinned baseline:

- `notes/design/2026-10-08-native-projection-public-export-definition.md`
  §§2–4: authentic native formation, fresh public roots, full ownership and
  selected scope for id and finite-public-import pick.
- `notes/theory/2026-10-08-projection-public-export-construction.md`
  §§3–3.1 and 4.1–4.3, especially §4.2: public inventory, extraction, whole
  frame decode, root equations and alias reuse; §6.1: actual-root retrieval.
- `notes/design/2026-10-08-source-generalize-definition.md` §2 and
  `notes/theory/2026-10-08-source-generalize-definition-and-proof.md`
  §§5.1–5.2 and 7.0: eligible placement, syntax-directed allocation keys,
  exact sharing and source final-root incidence. SRC-J does not claim alpha
  transport or a public root allocator.
- `notes/progress/2026-10-09-native-projection-interface-equivariance.md`
  §§2–3.4 and the companion falsification note: reviewed fixed-call/supplied-
  root scope and rigid identity-observer boundary, as recorded in
  `tasks/current.md` §Native projection renaming sublemma toward IFACE_EQUIV.
- `notes/progress/2026-10-07-successor-recursive-synthesis.md` §5.1 and
  `notes/theory/successor-proof-obligations.md`, IFACE-EQUIV/CI-USE: actual
  operation covariance and complete rigid identity accounting remain inputs.

Accepted decisions retained: the public root is ordinary and distinct in
responsibility from the source final root; Omega and fixed captures remain
fixed; one whole description action precedes challenges; aliases share it;
Shared, ViewLogic, EventField and EventProof have their original scopes;
complete Option 2 production and all nondefinitional proof choices remain.

**Claim classes.** Established inputs are the selected PE and source allocation
clauses and the previously reviewed fixed-fiber lemma. The new result is an
unreviewed derivation of finite syntax/incidence commutation. The actual-root
square is a conditional theorem with explicit supplier premises, not an
established consequence. The supplier audit is bounded to those clauses; it
does not assert that no adequate allocator can exist.

## 2. One real new and its complete incoming data

Fix the authentic included immutable unannotated id export E, its actual
source allocation grammar, one real client `new(id,i)` before any challenge,
and the finite client `new(id,i); alias(i,j)`. Fix the original type scope
sigma, source origins/slot identities, original event keys and base tree.
Let r be the selected final source root; E has no accessor for r. Omega
contains the fixed operational binding/provider, intrinsic IF0/q registrations,
outer contracts and their free closure, original nu/K/D and scope incidences.

The image A_i is a well-typed endpoint term at sigma, chosen before challenge
evaluation, not a later successful assignment. Its dependencies and constraints
are retained. The remaining data are the public inlet/IF/Delta and certificate
slot/telescope schema, the original shared binder incidences and frame/event
routing from Generalize §5.2, and all original proof choices. Nothing infers
their existence or validity merely from a printed `forall a. a -> a`.

For this note h is a bijection of **represented local coordinate names and
references** preserving sort, predecessor order, ownership, ordered operands,
tags and every incidence. It fixes i, j, original source/slot/provenance
identities, all client rigid coordinates, Omega and actual runtime identities.
The transported endpoint term A'_i is h(A_i). A reference to a fixed semantic
identity continues to denote that same identity. We do not let h replace a
registered source slot, runtime event, provider or existing ordinary root.

The induced frame action H_i maps each allocated local reference to its
corresponding reference in the renamed presentation. In the keys below q and
P identify the **same original** declaration/region, not new semantic source
identities. Writing a corresponding reference does not rename those origins.

| Selected owning class | Construction from §5.2 | H_i action / sharing |
| --- | --- | --- |
| Eligible Desc | One occurrence with key `(i,q)` at translated original sigma | Corresponding local reference; one image A_i, incident everywhere. |
| ViewLogic | `(i,q,original description-region path P)` | Corresponding binder and full predecessor telescope; allocated once before challenges. |
| Shared / OneShot / Established / Intrinsic | Original field or original single base-tree binder | Fixed; no frame copy or repeated initializer. |
| Event/EventField | Actual key `(origin,parent event path,occurrence)` | Same runtime key and witness; an initializer stays in the base tree. |
| EventProof | `(i,actual event key,q,original proof-region path P)` | Corresponding per-frame proof reference under the same event; runtime EventFields remain shared. |
| Client checking intermediates | Owning finite rule and original telescope | Corresponding local proof references; same proof tag and complete intermediates. |
| Alias j | Antecedent i's entire frame and certificate | Same routing; no new key, image or witness region. |

This uses the source allocation construction, not its adequacy theorem as an
assumed covariance law. SRC-J §7.0 confirms that an alias reuses its antecedent
certificate and that the source root incidence stays r. It supplies no equation
identifying r with the decoder's public root u_i.

## 3. Derived frame and equation-schema commutation

Define M_i(E,A_i) to mean the finite **schema construction** just displayed:
instantiate the selected export fields, route the original allocation keys,
and assemble the seven entries of PE §4.2. It is notation for those explicit
record operations, not a second semantic decoder or an executable source API.
It contains no ordinary-root handle allocation or registry lookup.

**Frame lemma.** Under §2's hypotheses, construct M_i on each side, rather
than supply its result. Each owning key has exactly one corresponding key,
and every reference/edge has the corresponding incidence. Thus

```text
M_i(h(E), h(A_i)) = H_i(M_i(E,A_i))
alias-route_j(M_i(h(E),h(A_i))) = H_i(alias-route_j(M_i(E,A_i))).
```

Proof: eligible Desc creates one reference per original declaration; preserving
the predecessor tree places its image at the corresponding sigma. ViewLogic
and EventProof key formation uses the same i, original origins and region paths;
their translated dependency lists are the H_i-images of the original lists.
Shared/base-tree references and actual event keys are fixed, so shared edges
remain literally shared. Local check introduction follows its finite rule
tree and translates every intermediate at its own telescope. Alias takes the
existing routing map, so its case performs no introduction. Constructor
induction gives the displayed equalities; h inverse gives reflection. No
operational call or semantic clause truth is used in this proof.

Let Eq_i(E,A_i) be the root-independent entry record in M_i. For id it is

```text
head       = Function(Pure,Value,ValueResult/InvocationReturn)
inlet      = I_q[A_i;Delta_i]
result     = A_i
dependency = EntryValue
admission  = four independent VP challenge/history constructor schemas
production = exhaustive VP phase/development schema with Echo
proofs     = ordinary CE schema at the original slots/telescopes.
```

By ordered record construction and whole substitution,

```text
Eq_i(h(E),h(A_i)) = H_i(Eq_i(E,A_i)).
```

The result entry and every occurrence inside inlet/IF/Delta/proofs receive
the **same** image; there is no independent output instantiation. Admission
and production transport as complete syntax with all guards/alternatives,
not as source execution relations. A pending event retains absent completed
witness fields; this operation never manufactures them. Proof constructor
choices and intermediates are retained, not normalized. Omega is fixed.

For included pick replace result by the fixed `J_z.value_type`, dependency
by `PublicValue(J_z)`, and Echo by Fixed(J_z), keeping the whole capture closure
fixed. The same schema derivation applies. No arbitrary capture summary is
inferred. No theorem about truth of changed-operand VP, hereditary, registry
or local-law applications follows from these syntax equalities.

This improves on the prior note exactly at the constructed frame: its outputs
are obtained from selected keys before any root supplier result is given.
It still cannot create the ordinary root handle from those keys.

## 4. What §4.2 establishes about the public root

At the level selected in PE §4.2 and native projection §3, a decoder must:

1. Allocate one fresh ordinary public root u_i at the real new and attach the
   complete Eq_i record to it, with active ordinary interpretations.
2. Make ordinary readouts and the actual-root consumer read that record at
   u_i, without resolving source r.
3. Return literally that same u_i and full description frame for alias j.
   A distinct real new has its own eligible/ViewLogic images while retaining
   original Shared/event sharing.

These are genuine selected constraints. They exclude reusing r as a hidden
answer and allocating again at alias. They do not choose the representation
or semantic identity of u_i. Generalize's `(i,q)` and proof keys are keys for
source descriptions/witness incidences; no selected equation assigns the
ordinary root handle the key `(i,q)` or any other key. Root freshness is stated,
but the relevant root namespace, state, reserved/live identities, publication
barrier and failure behavior are not specified in these sections. We retain
the selected freshness requirement without defining those missing details.

Consequently, even a completely determined Eq_i does not determine the
registered root identity. Equal equation records permit distinct roots; PE
§6.1 expressly checks that a submitted certificate names the actual retrieved
record. Equality of printed type, syntax or denotation cannot replace that
identity check.

## 5. Exact remaining supplier and conditional square

To state the obstruction without choosing an API, write `R_i(E,A_i;B)` for
the authentic allocation/installation **relation**, if supplied, whose output
contains public root u, full frame f and the resulting root registry/context
B+. B names all real supplier inputs, including the identities it observes.
Neither R_i nor B is a newly selected source rule here.

The necessary supplier packet is:

- Its complete input/state and identity-observer inventory, root identity
  sort, meaning of freshness, and alias routing/installation semantics.
- A permitted extension H+ of the frame action to the allocated root and
  resulting store, fixing every prior rigid root and Omega. Any allocator
  identity-sensitive constant must be fixed or independently transported.
- Preservation and reflection at that **actual** supplier, including complete
  typed output evidence and whatever failure cases its selected contract has:

```text
R_i(E,A_i;B) -> (u,f,B+)
  iff
R_i(h(E),h(A_i);H(B)) -> (H+(u),H_i(f),H+(B+)).
```

- Actual installed-root readout transport, with its independently supplied
  active interpretation laws, rather than only stored equation syntax:

```text
Read_{H+(B+)}(H+(u)) = H_i(Read_{B+}(u)).
Alias_{H+(B+)}(j) = H+(u)  whenever Alias_{B+}(j) = u.
```

Here arrows denote related outputs, not a claim that the supplier is a total
deterministic function. Exact functional equality needs that separate contract.
H+ is not assumed merely because u is called fresh: its legitimacy depends on
the complete observed-identity inventory and actual root/registry meaning.

**Conditional one-new theorem.** Given this packet and §2's frame hypotheses,
the selected equation installation and alias rules commute at one real new:
transporting the complete actual output equals/relates to a transported decode
output, and both alias paths retrieve its same public root. Proof: §3 supplies
the corresponding frame/equation record before allocation; the supplier law
supplies the actual root/store step; readout supplies the retrieved record;
the selected alias rule plus supplier routing gives literal reuse. Inverse
laws give reflection. This does not supply any missing packet premise.

**Smallest underdetermination witness.** Keep one actual new, no challenges,
one fixed Omega and the same Eq_i. Suppose the independent root namespace
permits two otherwise admissible fresh handles u0 and u1. That namespace
premise is explicit. Attaching Eq_i at u0 and attaching it at u1 each satisfy
the stated one-new root/entry requirement; their aliases each reuse the
respective handle. The selected displayed clauses contain no selector deciding
between them and no nominal correspondence between actual registries.
Thus the entries plus freshness alone cannot conclude which actual handle
an independently rerun decode returns. A one-root namespace cannot express
this ambiguity; one new and two available handles suffice. No global
minimality or complete source-program counterexample is claimed.

This is a logical supplier-underdetermination witness, not two proposed
Yulang allocators or a lawful counterexample to PE/CI. In particular we do
not pick a least-free-ID algorithm or treat every fresh root as alpha-local.
An existence claim up to renamed fresh names can be made for an abstract
presentation; moving an actual registry-visible handle requires the supplied
H+ law. Another checker that implements such a law by definition would leave
the supplier premise untouched.

## 6. Coverage, checks, resources and next action

Oracle independence: no executable reference/candidate oracle exists here.
The frame derivation shares the selected allocation and equation constructors;
it proves a consequence of those definitions, not their independent source
validity. The conditional root theorem explicitly assumes its authentic
supplier law. The two-handle witness shows missing determination, not semantic
failure. No seeds, numeric ranges, mutations, samples or search shards apply.

Coverage: one selected native id real new plus one alias, with a schema
extension to the stated fixed-public-import pick cases. Original future/event
telescope schemas remain represented; no enumeration of runtime histories
occurred. Omitted: actual root supplier/lookup representation, nontrivial
semantic identity action, opaque changed-operand operations, arbitrary W
observing moved root identities, foreign kernels, general recursion/State,
production F5 correspondence and resource/failure implementation.

Failure conditions: changing original/rigid source identities or Omega;
misclassifying an intrinsic q, capture or registry handle as a local label;
changing telescope order; allocating ViewLogic per challenge or alias;
copying Shared or actual runtime EventFields; dropping certificate choices or
Option 2 arms; substituting source r for public u; or invoking an unprovided
root/readout covariance law. Each exits the proved or conditional hypotheses.

Checks performed: full research-lab/design-authority/git-concurrency rules;
compiler-engineering proof-obligation-economy audit; exact source-section and
prior-result reads; pinned HEAD/branch inspection; dependency SHA-256 and
pinned/live equality; narrow leased-note scope/whitespace inspection. No Git
mutations, compiler edits, tests, builds, benchmarks, executable search,
scratch files or child agents. CPU/RSS and total research wall time were not
instrumented; zero heavyweight processes and zero probe processes ran.

The prior two lanes already left actual changed-operand operations open; this
attempt moved to their owning construction point and resolved frame routing,
then stopped at the root supplier. Under proof-obligation economy, frame
incidence reconstruction is reduced by the retained allocation keys. The
actual root allocator/readout safety and required natural fresh-use behavior
are A/B concerns when integrated; unrestricted nominal characterization stays
conditional. No classification retires IFACE_EQUIV or changes CI_USE status.

Recommended next action: lease the actual ordinary-root allocation/installation
supplier and enumerate its complete root identity observations, then prove
the §5 packet at that owner; do not run a third supplied-transition model.

## 7. Frozen dependencies and commit packet

Direct dependencies were compared with the pinned baseline before submission:

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-08-native-projection-public-export-definition.md` | `aed6ef63b01f555a5f2804f87a599167c1a30fa999afc0b9d9f11b8ae974a919` |
| `notes/theory/2026-10-08-projection-public-export-construction.md` | `4cf84e7a38153b893f1d339780598e2b79084c747ecb883acf0e4fdaa49cf631` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/progress/2026-10-09-native-projection-interface-equivariance.md` | `b55fed5b726995c307c12b94bee99c592ed056dc6ac3db192b8a127cfce5e818` |
| `notes/progress/2026-10-09-native-projection-interface-equivariance-falsification.md` | `20a79f8c226611ab7de76b333da1714a66909c27b933ac12457392bb3ce517ae` |
| `notes/progress/2026-10-07-successor-recursive-synthesis.md` | `e34a568946f5c1946c01828aae34e890747477ee8c272775408438acd95aa43f` |
| `notes/theory/successor-proof-obligations.md` | `41e25bc633f69df302361f41c60c0c324e9713a7194373f23f9f7a182724e4a1` |

- Exact leased path: `notes/progress/2026-10-10-pe-decode-new-action-construction.md`.
- Baseline SHA: `68ea68fa3b0a73fff05f28c631e9f49be076ebf6`.
- Changed dependency hashes: none at freeze; unrelated branch changes do not
  supply or invalidate the root supplier law.
- Claim/review status: frozen, unreviewed research derivation of one-frame
  syntax/incidence naturality; conditional actual-root square; precise supplier
  obstruction; no independent review, source counterexample or gate closure.
- Checks already run: governing reads, HEAD/branch/lease scope, dependency
  hash/pinned equality and final leased-file whitespace/content inspection;
  no tests/builds or executable semantic experiment.
- Proposed checkpoint commit: `research: derive PE new frame action and isolate root supplier law`.
- Shared-record deltas intentionally left for primary/curator: link this result
  from `tasks/current.md`'s native projection renaming section if accepted;
  identify the actual allocation/installation/readout packet as the remaining
  one-new leaf. Retain IFACE_EQUIV OPEN-PROOF, CI_USE CONDITIONAL-CLOSED and all
  production/lifecycle gates. No shared file or question bundle was edited.
- Writing stops before frozen review. The producer does not certify this note.
