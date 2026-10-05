# Source generator to SCC boundary formation: identity and ownership audit

Date: 2026-10-06
Status: frozen, unreviewed research derivation and bounded contract audit
Baseline: `2e742ee914d6db32a2ada93483735f2f6e7bde42`
Exclusive lease: this file only
Implementation authority: none

## Objective and method

Audit the bridge from the supplied finite structural source generator to the
SCC generalized-boundary producer/consumer contract. The method is a
constructor and identity-origin audit, with two small symbolic source
witnesses and an equality-class derivation. No source semantics, generalization
policy, late-dependency policy, representation, or production route is selected.

The result is narrower than a source-boundary adequacy theorem. The generator
retains enough symbolic incidence to expose necessary fixed-sharing checks;
it does not introduce the enclosing non-generic relation or a generalized
boundary. The missing rule is not finite copying: it is a source judgment
that assigns each exported member and relevant identity its boundary status
under the actual enclosing context, before any transport operation.

For an effectful derivation, §5 supplies only independently justified
structural obligations. Its shadow cannot discard `Φ/K,D`, coupled effects
or required evidence; those relations remain jointly conjoined. No conclusion
here upgrades the pure ledger to that complete source boundary.

This note takes the prior finite local-generation and monomorphic reference
construction as dependencies. It does not repeat their counting or finite
scheme-copy attacks. The source witnesses below discriminate identity-origin
shortcuts, not the existence of finite schemes.

## Exact dependencies and authority

All semantic reads use objects at the baseline. Uncommitted task/index
material was navigation only and contributed no premise. Relevant sections:

- [Source-generated structural theorem package](../design/2026-10-04-source-generated-callback-structural-theorems.md)
  §1 (conditional scope), §5 (all nine generator rows and finite-generation
  lemma), §6 (structural anchors), and §7 (existence-witness boundary). This is
  Reviewed mathematical material, not an Authoritative compiler generator.
- [SCC generalized-boundary contract](2026-10-05-scc-generalized-boundary-contract.md),
  **Abstract producer/consumer contract**, clauses 1–6, and **Exact missing
  premise and stop line**. This is a source-grounded research obligation,
  not successor implementation authority.
- [SCC foundation](../design/2026-09-20-constraint-collection-scc-foundation-draft.md),
  **Lightweight-port boundary**, **Phase and fact ownership**, **Construction
  sequence F0–F2**, and **Deferred semantic gates**: complete collected
  definition/use identities, source-use ownership, static partition and scope.
- [Static SCC session](../design/2026-09-21-oracle-aligned-static-scc-inference-session-draft.md)
  §§2–5: owner, complete draft visibility, internal-use direction,
  post-finalization incoming routing and whole-attempt failure, within its scope.
- [Redesign charter](../design/2026-09-29-scc-intrusion-redesign-charter.md)
  §§1–4: F5 is replacement material; preserve meaningful source constraints
  and distinguish outer sharing, member roots and use substitutions. User
  decisions in §§22–23 fix guarded comparisons and variable-only levels;
  neither specifies a generalization classification rule.
- [Experimental transport gate](../design/2026-10-04-intrusion-experimental-transport.md),
  **Bounded implementation gate** and invariants 1–5: the partition, root and
  bounds are supplied inputs, explicitly outside that gate's source proof.
- [Rebuild addendum](../design/2026-10-04-scc-intrusion-cross-edit-rebuild-addendum.md),
  **Interface comparison boundary**: complete interface equality is required
  for inference reuse; interface fields and granularity are not selected.

The required research, authority and concurrency rules, and the orchestration
budget, were read in full. The SCC foundation, session, transport and rebuild
sources were read in full. No new approval bundle was consumed.
The already committed
[local source construction](2026-10-05-source-scc-source-coverage-construction.md)
and [current implementation correspondence](2026-10-05-source-scc-current-bridge.md)
identify finite generation, monomorphic references and missing scheme
introduction. Their results delimit this audit; no new production code trace
or independent review of those artifacts is claimed.

## Input hypotheses and objects that must stay distinct

Let `S` be a supplied finite derivation graph belonging to §5, with finite
guarded annotation schemas and resolved binder references. Let `T_i` be its
preallocated endpoint at source expression/binder identity `i`; clauses use
these endpoints exactly as the table specifies. Suppose equality normalization
succeeds, with quotient map `q` into finite endpoint classes `Q`. Retain the
original source-to-endpoint map, occurrence labels and directed clauses.

An additional supplied definition-membership map names one component `C` and
its represented definitions. It selects an ordered tuple of member roots
`R_C = (q(T_d))`; this is not a quantifier list. The tuple can repeat a class
when distinct member identities alias. Neither the structural table nor its
free-class incidence graph selects that membership map from raw syntax.
F0–F2 supplies it only for its separately admitted definition/use envelope.

For the necessary sharing lemma below, supply the actual enclosing context
`Γ` and a map from each existing enclosing semantic identity to its endpoint.
Let `A_Γ` be the set of their quotient classes. This set is a necessary fixed
subset, not a proposed complete non-generic closure algorithm. Additional
scope, permission, level or live-context obligations may make other identities
non-generic. Deriving that complete relation is the missing premise.

Three uses of the word root/anchor refer to different objects:

| Object | Definition in the inspected sources | Consequence |
|---|---|---|
| SCC member root | Endpoint selected by a represented definition and its collected identity | An export to preserve; selection alone does not make its variables generic. |
| Fixed context identity | Existing enclosing/non-generic identity that consumers must continue sharing | Can be descriptor-free, and can alias an exported member root. |
| Structural descriptor anchor | Nonfree descriptor incident to a free component in theorem §6 | May be open and member-owned; it is not evidence of enclosing ownership. |

Theorem §6 connects free classes by undirected free/free bounds for an
auxiliary regular-witness construction. The definition SCC graph instead
uses directed `parent/user -> target/dependency` arcs. Neither graph can
replace the other's membership or ownership map. Theorem §7's temporary
aliasing to an open descriptor is an existence-witness choice; it cannot
classify generic variables or erase the original identity partition.

## Derivation: enclosing aliases exclude generic freshening

**Conditional necessary-sharing lemma.** Under the input hypotheses above,
any boundary reconstruction satisfying contract clause 3 must preserve every
class in `A_Γ`. A generalized substitution cannot replace that class with an
independent use-local identity, even if it also appears in `R_C`.

**Derivation.** Take an existing enclosing identity `a` and any source
endpoint `T_i` equal to it in the generated ledger. Successful normalization
gives `q(T_i) = q(a)`. Contract clause 3 preserves the enclosing identity and
its constraints. Every occurrence in this class denotes that same assignment
coordinate. Replacing one occurrence with an independent use-local coordinate
would split the generated equality; replacing all occurrences, including `a`,
would replace the enclosing identity. Either contradicts clause 3. Therefore
the entire class must retain its fixed interpretation. The argument applies
pointwise to each existing enclosing identity, including a class containing
several member roots. QED.

This is a necessary condition conditional on actual `Γ` and equality
correspondence. It does not prove that every other class is generalizable,
choose a reachability closure, or establish consumer-extension equivalence.
Source identity labels remain distinct provenance even when endpoints share a
class. A partition used by transport must respect this equivalence; keeping
one alias local and another fixed before quotienting is not enough.

### Smallest alias discriminator

In structural proof notation, take one existing enclosing binder
`a : α`, and one represented immutable definition `x = a`. The §5 name and
binding rows emit

```text
T_name = α
T_x = T_name
R_C = (q(T_x))
A_Γ contains q(α)
therefore q(T_x) = q(α) is fixed.
```

One represented definition, one resolved name and one existing enclosing
identity suffice. There is no constructor, application, annotation, recursion
or second consumer. Removing the enclosing identity removes the fixed-sharing
obligation; removing the binding/name equality removes the selected-root alias.
The witness refutes the shortcut "every selected member root is local" at
boundary formation. It does not refute §5 or an SCC transport theorem supplied
with a correct partition, and is not claimed as an executed raw-source fixture.
F0–F2 does not admit this enclosing-local binding form as a new source feature.

### Open-descriptor illustration; anchor status still conditional

For the supplied identity-lambda derivation `f = lambda z. z`, the table emits

```text
T_body = T_z
T_f = Function(T_z,T_body).
```

After quotienting, the Function descriptor is open because it reaches the
free parameter class. This is only an open-descriptor illustration: the
equations do not emit a retained free/descriptor inequality, so they do not
establish the `Anch(C)` predicate of §6. The expression's constructor origin
also supplies no enclosing ownership. Conversely, the preceding `α` is fixed
while descriptor-free. These examples show that descriptor-bearing structure
and enclosing ownership are different facts, but they do not instantiate an
anchor-versus-owner discriminator. A source rule that emits the needed
incidence could make this descriptor an anchor without thereby assigning
enclosing ownership. No claim is made that the parameter must be generalized
under every context; that still needs the missing introduction rule.

## Contract audit: proved clauses, conditional clauses, missing rules

| Contract clause | What follows in the supplied shadow | Exact unproved bridge |
|---|---|---|
| 1: source-derived boundary | Each supplied expression/binder receives its endpoint; represented definition identities can retain an ordered member-root map. The alias lemma prevents classifying an enclosing alias as generic. | Source selection of represented definitions/SCC roots and a total generic/non-generic classification under actual `Γ`; treatment of level/permission dependencies and aliases after normalization. No partition is synthesized by §5. |
| 2: joint outgoing relation | §5 states all original directed structural checking clauses and bound identities survive normalization. Keeping their common assignment retains source endpoint sharing. | Generalized boundary introduction, adequacy of actual source annotation obligations, coupled effects, guarded relations, scope dependencies and evidence. No exported relation is introduced by the table. |
| 3: fixed-context sharing | The conditional alias lemma above is necessary. Lexical lookup reuses its supplied binder endpoint. | Complete non-generic closure and retention of the actual enclosing constraints through boundary publication and later consumers. Lexical root reuse alone does not classify it. |
| 4: visibility/internal recursion | Monomorphic recursive references reuse preallocated binder endpoints. A supplied ledger contains all supplied member clauses simultaneously. F3/F4 independently requires complete draft visibility within its own scope. | A simultaneous mathematical conjunction has no publication/read event. It does not prove that a wider producer exports all roots before an incoming consumer, or constructs a joint generalized result. |
| 5: consumer extension | A supplied resolved name has an occurrence endpoint and equality to its binder. F0–F2 independently preserves each admitted module-use payload and its exact parent/target. | Generalized use introduction, full occurrence ownership for this wider grammar, independent incoming substitutions and all later caller constraints. The table has no such incoming rule. |
| 6: failure/observations | Existing session authority requires whole-attempt failure with no partial result. The audit preserves source labels as proof inputs. | Failure behavior of a new producer; complete observation/evidence disposition and canonical interface comparison. Source equation generation has no reconstruction transaction. |

The source-table name equality is not silently substituted for F3/F4's
`target-root <: occurrence-value` internal route. They are different stated
relations in different scopes. Establishing a correspondence requires the
source-boundary judgment; it cannot be inferred from shared endpoints alone.
No stronger endpoint equality is proposed for a callback boundary.

## Source-use ownership and complete visibility

For every supplied name node, §5 provides a binder lookup and a source endpoint.
It does not say whether the binder is a parameter, local immutable binding,
module definition, imported provider, or another boundary's fixed identity.
It also does not assign `DefinitionUseId`, parent definition, cause or an
internal/incoming route. Expression-to-binder incidence cannot replace those
source occurrence identities after endpoint quotienting.

The Authoritative foundation assigns one payload per admitted resolved
binding-body occurrence, retains `(parent, target, occurrence, cause)`, and
preserves duplicate occurrences on one graph arc. Local names create no
module dependency edge, and direct-root names have no parent and are excluded
from F0–F2. Those are established scope facts. For all nine §5 rows, ownership
must additionally cover names inside lambda bodies, records, arguments,
selections, annotation checking and nested bindings, whenever those derivations
are admitted. The table supplies no rule assigning these occurrences to
represented definitions; a supplied resolution/owner map can support an audit
but cannot prove its own source correctness.

For a source-to-boundary bridge, each admitted use must therefore have a
source-derived occurrence and target plus the applicable source owner or
explicit no-parent status. The original occurrence record must survive
equality aliases and arc deduplication. An owner/cause record is not a new
constraint endpoint. Completeness must cover every admitted source use,
including uses that select no new structural descriptor.

Complete visibility is likewise two premises: a complete source member/root
and obligation inventory, then a publication ordering rule on that inventory.
The static session supplies a scoped ordering rule, but does not enlarge its
source envelope merely because the §5 inventory is finite. Whether another
feature introduces late dependencies is left for the separately assigned
policy gate; neither exclusion nor admission is chosen here.

## Operations absent from this generator

The nine-row table has no rule for component generalization, quantified binder
introduction, boundary closure, generic/non-generic classification, incoming
scheme use, caller constraint extension, level extrusion, publication,
rollback or canonical interface equality. It contains structural annotation
checking only as a supplied original clause, not annotation admission or
elaboration from written source types.

As a pure structural shadow it also contains no invocation/receipt/entry
program, first-class computation elimination, coupled effect row,
Pure/Handler view formation, handler capture/release, operation request
packaging, effect-family invariant evidence, store/State alias, method/role
resolution, imported opaque provider, cast/adapter realization, optional
Record comparison or public diagnostic/result-query observation. These
absences identify obligations outside the table; they are not proposed
language exclusions. The separate callback generator in theorem §§2–4 is
not silently combined with §5 to supply missing SCC introduction rules.

## Independence, coverage, failure conditions and resources

There is no executable oracle, checker, random seed, range, enumeration,
mutation campaign, build or compiler test. The semantic method is derivation
from supplied source constructors and separately stated boundary requirements.
The two witnesses share the same table and equality notion, so they are not
independent validation of those source rules. Their discrimination concerns
root-based and descriptor-based identity classification respectively. The
contract and table are separate artifacts, but share lexical identity and
joint-assignment assumptions; document separation is not oracle independence.
Frozen Oracle `a58eefc3` is historical context in the authority documents only;
its code and runtime behavior were not consulted in this lane.

The audit covers all six boundary clauses against all nine table rows, with
focused derivations only for equality aliases and lexical ownership. No raw
source acceptance, complete context/permission closure, effect/evidence
adequacy, scheme formation, generalized consumer theorem, solver termination,
resource complexity, or production conformance was proved. The producer's
reread is not independent review.

The derivations fail as applications if the supplied derivation is outside
the table, lexical resolution is absent or wrong, equality normalization has
failed, member selection is incomplete, or `Γ` omits an existing enclosing
identity. Even with those hypotheses, a broader generalization theorem fails
to follow until its boundary-introduction rule exists. A known-head structural
anchor or a regular witness cannot supply that premise.

Commands: sequential lightweight reads of pinned documents with `git show`,
scoped `rg` locators, revision expansion, dependency SHA-256/worktree byte
comparison, one exclusive file creation, and final text/hash inspection.
Git was used read-only for pinned-object retrieval; no index/ref mutation.
Some initial combined navigation output was truncated; the exact generator,
contract and governing authority excerpts were subsequently read separately.
CPU/RSS and end-to-end wall time were not instrumented; command calls reported
about 0.1 seconds each. No heavy process, parallel compute, child, scratch
output, shared-record write or question-board write was used. The assignment
supplied a no-test/build/probe envelope, with no numeric CPU/RAM/wall ceiling.

Recommended next action: construct or identify a source boundary-introduction
judgment for the admitted pure fragment, indexed by actual `Γ`, represented
members and source occurrences. Require it to handle the enclosing-alias
witness and keep occurrence ownership through equality quotienting. If no
existing authoritative rule determines generic/non-generic eligibility,
return that exact gap to the primary before a consumer preservation proof;
another finite transport probe cannot introduce the rule.

## Dependency snapshot

SHA-256 at the baseline; all listed worktree bytes matched at capture. No
dependency was modified by this worker. Revalidation at integration HEAD is
primary-owned.

| Path | SHA-256 |
|---|---|
| `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` | `568bb4649ba278519f3ad01af2091dd1baaca42850cd19e3b5734b3c47c2eefe` |
| `notes/progress/2026-10-05-scc-generalized-boundary-contract.md` | `9e117cac7bf5566d231b8cd7499222913ba639510d33d9a99d62b50118b40271` |
| `notes/design/2026-09-20-constraint-collection-scc-foundation-draft.md` | `37a2799288db0081cf3f32c7f6860c376ff0b2ce3249397cd9c23c7a89fedeaa` |
| `notes/design/2026-09-21-oracle-aligned-static-scc-inference-session-draft.md` | `d5bc6defbd13ac4f632ab1a4973dfcc77deb87f2f2236f715e31340a73bd4eaf` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-10-04-intrusion-experimental-transport.md` | `b9eeaa4c014e98f0e2790208030a6cccf48e6efcfb05c2d46effd27caff25c96` |
| `notes/design/2026-10-04-scc-intrusion-cross-edit-rebuild-addendum.md` | `e8abb68f0d1dc656e3e303a82d8b7ffb4254bb1a8be99b51ad9593c5a7b85e29` |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `rules/orchestration-budget.md` | `32174c0eb14314df334499586b43db3074de4662fdc908da60eb1a24e1dc3716` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-source-scc-boundary-formation-bridge.md`.
- Baseline SHA: `2e742ee914d6db32a2ada93483735f2f6e7bde42`.
- Changed dependency hashes: none; the captured dependency snapshot is above.
- Claim/review status: frozen, unreviewed research checkpoint; conditional
  necessary-sharing lemma and bounded source/contract audit; no gate closure.
- Checks already run: pinned source reads, dependency SHA-256 and worktree
  equality, lease absence before creation, final UTF-8/fence/whitespace/local
  link inspection and artifact hash. No semantic executable checks.
- Proposed commit message: `research: audit source identity formation at SCC boundaries`.
- Shared-record deltas intentionally left to primary/curator: link this note
  from the active SCC adequacy entry; distinguish member roots, fixed context
  identities and structural anchors; retain boundary introduction, full
  occurrence ownership and generalized consumer preservation as open.
  `tasks/current.md`, `tasks/research-lab.md`, design index and theory maps were
  not written. No authority or reviewed-status promotion is supported.
