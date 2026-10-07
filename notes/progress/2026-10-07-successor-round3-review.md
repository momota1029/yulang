# Successor round 3: closure, repair and integration record

Date: 2026-10-07 UTC
Branch: `research/simple-sub-intrusion`
Primary: Astra; source self-init synthesis and final proof adjudication
Start remote: `6fb5d7f697d5d592e0a39532ddb4967b54e18090`
External remote delta revalidated: `6cd43ea855acdd1e7f47a46408715a03d192ffd4`
Latest external remote revalidated: `4a9d969db09be881bdc0ce6888cc3d651dfc2405`
First published checkpoint: `31b97ed3b56db5a642ae9eddeebda366af74233e`
Status: proof panels, repaired deltas and final remote integration reviewed; final counts in §10 and integration checks in §13
Production cutover: prohibited; no production inference routing change

## 1. Exact starting state and result accounting

The primary fetched the requested remote before work and fast-forwarded the
clean local branch from the preceding `dcea2caf` checkpoint to `6fb5d7f`.
The 25 intervening commits, current task, canonical DAG, dependency/theory
maps, approved receipts/designs, reviewed progress, current shadow slices and
relevant historical Oracle producer notes were reread. The preserved
pre-correction/full-DAG ledgers were read as history and not edited.

| Status | Start | Reviewed round-3 checkpoint | Change |
| --- | ---: | ---: | ---: |
| CLOSED | 6 | 7 | +1 exact approved subcase |
| CONDITIONAL-CLOSED | 17 | 19 | +2 existing proof nodes |
| OPEN-PROOF | 46 | 44 | -2 |
| OPEN-SEMANTIC | 19 | 19 | 0 |
| IMPLEMENTATION-ONLY | 1 | 1 | 0 |
| BLOCKED-BY-USER-DECISION | 0 | 0 | 0 |
| Total nodes | 89 | 90 | +1 |
| Dependency edges | 194 | 195 | +1 |

The real reduction is **65 to 63 existing OPEN nodes**. The new CLOSED
`REC_INIT_SELF` is an extracted subcase, not another old OPEN-node reduction.
The conditional promotions prove composition from independently stated
prerequisites; neither asserts that the open semantic premises now hold.
The current checkpoint counts above passed the independent canonical-record
review. Any further independently reviewed downstream delta and final
publication are recorded below rather than attributed retroactively to it.

## 2. Accepted source and theorem closures

### Exact self-initialization

The primary synthesized the
[governing source rule](../design/2026-10-07-recursive-self-init-executable-boundary.md)
and [proof/initializer cut](2026-10-07-self-init-and-conformance-round3.md)
from unchanged approved q1/d1. EXEC-SELF-Q1 determines execution acceptance
without a runtime membership premise. SELF-ENVELOPE, SELF-NOSTART,
SELF-INFER and SELF-ADEQUACY close exclusion, pre-execution rejection, F4
`Never` preservation and the disjoint rejection contribution to source
adequacy. No runtime Return/Request event or provider is invented.

The original question, saved draft and approved answer were each compared
with commit `a814bc76aa107f2ffb7aae9cb2e2887c5b078792`, and the saved draft
was verified inside the approved answer. All comparisons passed. Only the
receipt's application history is updated. Other initializer classes retain
their own source inclusion/start rules and the exact unavailable-target
`InitRead(sigma,G,b,n,g,iota,A,w;xi)` disposition. Exact q1 does not decide
aliases, local groups, other `Never` results or initialization scheduling.

### Whole-relation principality composition

The [actual-export synthesis](2026-10-07-actual-export-synthesis-round3.md)
proves PRINCIPAL from its existing SOURCE_ADEQUACY, ALL_VIEW and PROJECTION
contracts, without adding a new postulate. The computed finite public scheme
is fixed before the independently valid view; the whole ordinary-use graph
is fixed before assignments. ALL_VIEW retains one original-scope strategy
for the source/query conjunction and accepted Direct at actual `B_common`.
The existing full PROJECTION contract includes ordinary-use/evidence
factorization, which carries that whole joined strategy into the actual
designated export. Marginal projection alone has a displayed countermodel.

Thus the residual generic composition proof is retired, while actual export
acceptance, widened-domain/observation law construction, independent source
adequacy and effective projection remain OPEN. Nonidentity `VIncl` does not
become accepted Direct by transitivity or successful Q. Paired Option 2 extras
and original witness correlation remain in the retained premises.

## 3. Call proof: accepted major finding and fresh repair

The [Call/original rule attack](2026-10-07-call-original-rule-round3.md)
initially composed ordinary local CalRet, DelayIntro, phase and typed-Bind
laws. The initial compiler referee found a **major missing input bridge**:
the implications could all be vacuous when no argument typing at the
callee-returned world, first receipt inputs, or original Bind interface
instances had been constructed. Independent admission is not operand typing.
The primary accepted this finding.

A fresh producer repaired only §2.1 and the related small checker seam.
The repaired theorem retains explicit local constructor laws and five
independent constructed-input laws:

- CI-Operands: obtain jointly typed operands and capture/provider/current-world
  adequacy at the original independently admitted assignment.
- CI-Bind: obtain the actual ordered interface instances at every original
  outer/entry/body/native/consumer Bind, including current resumed state.
- CI-ArgFrame: retain each actual callee-return evidence and jointly extend it
  with argument typing at that returned world and compatibility with the
  actual provider's whole-carrier contract.
- CI-Receipt: use the resulting whole-carrier membership and original
  authority operands to construct the complete first receipt inputs.
- CI-StepFrame: preserve each local phase output together with retained inputs
  to construct the next phase input and Bind interface at the current world.

All extensions form one coherent family at the original scopes and binder
dependencies. None assumes whole-Call, complete receiver, source attachment
or licensing membership. The proof constructs inputs forward and finite
typed suffixes backward. Callee-prefix suspension, receipt/entry suspension,
consumer suffixes, actual raw-resumption state, finite prefixes and latent
returned-provider futures keep their original incidence and complete suffix.

The fresh compiler delta review passed the repaired theorem. The fresh spec
delta review found the proof repaired but required the canonical records to
retain **all** these ordinary laws and CI bridges explicitly before the
conditional promotion. That record omission was accepted as
promotion-blocking and assigned to a fresh theory curator. DESC_CLAUSES stays
OPEN-SEMANTIC and SEM_JOINT stays OPEN-PROOF; concrete law instantiation is
not implied by CONDITIONAL-CLOSED CALL_TYPE. The record delta must pass the
narrow independent integration review before final closure is claimed. That
review subsequently passed as recorded in §8; the conditional promotion is
accepted with all these input obligations retained.

## 4. Direct attacks that remain OPEN

| Gate | New exact result and residual |
| --- | --- |
| ORIGINAL_ASSOC P2 | An owned full typed-image preimage is stronger than global denotation surjectivity plus owner existence. The same-original-tuple separation locates the missing original slot/contribution/view incidence introduction; contribution = whole Call and slot = source position are not used. |
| ORIGINAL_ASSOC P3 | Finite-family assembly and pointwise coverage do not imply one whole-family original witness. The finite-history diagonal preserves every licensed arm yet misses a longer history. A finite semantic coverage quotient of the fixed owned fiber suffices for uniform assembly; finite source/slot syntax does not prove that quotient finite. |
| ATTACH / licensing | Original association membership has no independent Attach constructor by itself. Original licensing payload is not a licensing derivation. Both directions must range over all original licensed witnesses, including those outside any chosen assembly image. |
| INIT_WORLD / INIT_VALID | The missing source-root installation maps actual exporter evidence into importer incidence/current world with shared aliases; semantic imports require a filling-independent open action on the whole witness/world graph. Source generation of a literal is not importer-world validity. |
| REC_DESC / MEMBER_DISCHARGE | The dependency-cut lemma exposes a world premise that already entails the own-member membership to be introduced. The direct simultaneous constructor must produce both actual root-world validity and member typing from independent imports/provisional roots. Its next ordinary clause is acceptance of the latent recursive Return certificate, not captured-Name lookup identity. |
| ALL_VIEW | Actual root acceptance still needs the fixed original descriptor/domain/guarded-observation inclusion rule, actual resolver conformance and complete constructor transport. The first decorated widening/Return instance remains explicit in the export note. |

The [world/recursive note](2026-10-07-world-recursive-rule-round3.md) retains
the strict FH quantifier order. Failure of `forall h. exists e. LocalCheck`
requires a history refuting every compatible evidence, not one failed choice.
No cut here proves that two complete Authority-consistent Yulang meanings
differ on the same independently admitted source; no user question is raised.

## 5. Independent review snapshots

Review roles use the repository's compiler-referee/spec-auditor instructions;
producer conclusions were not accepted as independent review. The primary
waited for each parallel panel before adjudication.

| Frozen artifact | SHA-256 | Review |
| --- | --- | --- |
| Exact self-init governing rule | `e38bba12e827c1604665c47ef155b63ffa973f0a3927bf85561f8bd88fc655ed` | `round3_compiler_referee` + `round3_spec_auditor`: PASS, no findings |
| Self-init proof/attack | `71ffbd4c586fb1ba2c73e352e3f657127a8674ef0c06ed7bd1d435f0a7cae9ad` | Same independent panel: PASS |
| Actual-export synthesis | `5a2c74f73a408d02d4658cf78d5c06b0500246923794073704f48cb9b8e4da33` | Same independent panel: PASS, exact existing PRINCIPAL conditional promotion supported |
| World/recursive rule attack | `93fbb60a8ee394107314af9fe5dadf824568b7b3fa7fdeadf7da0ae99d67f437` | Same independent panel: PASS, no node promotion |
| Repaired Call proof | `b04b21f8eea999e3e949753d24c6a47089eb6b9bd9689630ccfbeffc33694744` | Fresh `round3_call_delta_referee`: PASS; fresh `round3_call_delta_spec`: proof PASS, canonical-record condition retained |
| Repaired Call finite checker | `c5b37eeb87dde0359c85cfbd4a72dec79f5687ddb7d3da78eca514b39f72e2d3` | Both fresh delta reviewers executed the small checker successfully |
| Aggregate source-to-actual attack | `ae1f757b98f84c4b64e79105a015c3014367608ddc8242b2940c32ad28f03a48` | Fresh `round3_aggregate_referee` + `round3_aggregate_spec`: PASS, no required repair or node promotion |

The first panel's dependency snapshot included 911 tracked paths; the direct
inputs were rechecked against the starting committed tree. The Call repair
preserved §§3–6 byte-for-byte at hash
`ee4bc2b4d0beb23671e340d90a8c93249587b53c08bb073e1ab7e5c035049de4`.
Its 27 non-task dependency hashes remained unchanged; the additive remote
fixed-cut reconstruction only sharpened the independent CI-Operands premise.
Subsequent review/status metadata is recorded separately from these frozen
proof snapshots.

## 6. Default-off implementation and verification

The [initialization retention slice](2026-10-07-shadow-initialization-retention-round3.md)
retains whole resolved self-Name structural candidates from the original HIR,
through collection identity and frozen SCC/use joins, to the current solved
scheme. Foreign collections and parse artifacts are rejected. Both exact
q1-envelope recognition and pre-execution enforcement remain pending even
when a scheme is Bottom. No production path invokes the cold API.

The independent spec auditor passed the implementation and approved the exact
new-test repair before writing: compare unchanged facts in the same arena,
rather than compare branded facts from independent solves. The compiler
referee then passed the final source/tests without findings. The focused
feature-on suite passed 4 tests, 0 failures after the `6cd43ea8` integration.
The test packet covers original IDs, root/RHS/use/SCC joins, pending wider
source cases, solve retention, same-arena fact stability and unchanged
counter/error observations. The feature-off
`cargo check -p yu-core -p yu-hir -p yu-solver --offline` also passed, using
two Cargo jobs and a 180-second timeout; it completed in 1.46 seconds.

The repaired finite checker checks 64 two-arm assemblies, 128 finite-history
diagonal cases, all 512 three-by-three coverage matrices (169 satisfy the
finite-cover condition), three rule-seam discriminators and the small Call
input-vacuity/joint-extension controls. All pass. These are finite algebraic
and structural evidence, not source semantics or production conformance.

## 7. Remote integration and remaining barrier

The remote advanced during the attack with a reviewed State structural slice,
a reviewed Call fixed-cut reconstruction and its task synchronization. Their
three commits through `6cd43ea8` were merged without discarding worker changes.
The published checkpoint `31b97ed3` preserves that remote as a merge parent
and includes the reviewed principality synthesis. Local/published tree
equality was checked at `a8fe53759dc7c9af65cbc29b189f03f539fe9076`.
No force update was used. The remaining integration must again check remote
HEAD and exact tree identity before final publication.

Full soundness, actual all-view acceptance, source adequacy, complete original
profile/licensing/admission, actual recursive world/member/generalization,
finite joint solving/projection and production/source correspondence remain
cutover barriers. The first conditional compositions do not authorize a
successor inference switch. Final counts, canonical delta review, focused
checks and remaining publication are recorded below when completed.

## 8. Canonical-record closure and checkpoint verification

A fresh theory curator synchronized only the canonical generator, generated
Markdown/JSON and two navigation maps. Fresh `round3_dag_delta_spec` then
reviewed the five frozen files against repaired Call §2.1, the existing full
PRINCIPAL contracts and the exact approved q1 scope. It returned PASS with
no finding and explicitly **closed the accepted canonical-record major**.
The primary accepted the result. Neither semantic-clause status was promoted.

Frozen reviewed generator SHA-256:
`187f007c48fc1354d13d0a47c2f00e96242fc2831a513f2aa0fa95a86e8f6db7`.
Reviewed generated JSON:
`8dd3975fdbcc5b9ca554732fd0023e4bd08fed5e80d9d806c31a9beafe59c085`.
The primary and curator compared the committed `31b97ed3` baseline ledger
(SHA-256 `e866faaf68a813b95c80dcf46904a1e1f8dfbc5906b3ca019cd8e565eca9ffae`):
exactly CALL_TYPE/PRINCIPAL changed status; exactly REC_INIT gained the new
REC_INIT_SELF prerequisite; all other existing statuses and edges remained.
The independent auditor subsequently verified that exact baseline delta from
a supplied byte-pinned copy, closing its initial unavailable-baseline caveat.

The canonical validator passed at 90 nodes, 195 edges and 32 families,
explicitly reporting `semantic_proof_checked: false`. Targeted Rust format
checks, the changed-path whitespace/relative-link check and `git diff --check`
passed. All four preserved historical ledgers are byte-equal to the starting
remote; all three approved q1 bundle files remain byte-equal to their approved
handoff commit, with the exact saved draft embedded in the answer. The new
shadow implementation's feature-on and feature-off checks passed as stated
above. These checks supply navigation/implementation evidence, not missing
source judgments or production cutover authority.

## 9. Concurrent remote operand candidate and canonical reconciliation

A further fetch found remote
`7423c12ac1269049a9159b5bb4355f761991d19c`: the independently reviewed
[operand-context candidate](2026-10-07-call-type-operand-context-clause-candidate.md)
and navigation recording the already published round-3 PRINCIPAL theorem.
The complete candidate and all remote navigation deltas were read before
resolution. There is no changed governing design or approved answer.

C1–C7 remain candidate environment/Return/carrier/Delay/pending laws, with
one original witness and universal current-world demand obligations. Their
conditional derivation does not realize its independent predicates or actual
source-world inputs. It therefore agrees with the repaired Call theorem's
open CI-Operands/CI-ArgFrame clauses and the recursive own-root dependency
cut. No new source semantic rule or user decision follows from the candidate.

Both branches promoted the same existing PRINCIPAL result. Their canonical
text conflicted with the newer local Call/self-init packet only in overlapping
records. Resolution retains the entire independently reviewed local premise
records, both promotions, exact q1 closure and all remote candidate content;
the duplicate principal-reference alias is normalized to the existing local
reference. The candidate file is byte-identical to remote. Current-task
navigation records the new candidate while correcting its historical OPEN
Call statement to the reviewed conditional-composition status. No semantic
dependency, licensed witness, worker code or approved bundle was discarded.

The merge does not change the 90-node/195-edge checkpoint or its statuses.
SOUND's new downstream proof is still independently under review at this
merge; no promotion is folded into the reconciliation without that review.

## 10. Continued attack: SOUND composition closed

The primary immediately attacked the aggregate audit's publication/use gap
through the **existing full HIR_WIRING contract**, whose target already
includes the actual emitter, solver, generalizer, instantiator and publisher
correspondence. A fresh producer constructed the
[SOUND synthesis](2026-10-07-sound-publication-synthesis-round3.md); an
independent falsifier, without reading that draft, attacked the strengthened
route. Its lifecycle circularity caveat was made explicit before proof review.

Fresh `round3_sound_referee` and `round3_sound_spec` both passed frozen proof
SHA-256 `16b88eb9e299f3cb3548e36a22e3100fa11b09dace0e9222c9b3dd63bab9b07e`
without findings. The primary accepted both. The proof reflects each actual
accepted finite joint use/result through the actual complete solver graph,
the use-indexed inverse fresh maps, whole original-scoped projection/evidence
and the same source/production semantic correspondence. An accepted residual
still imposes all its constraints. Independently licensed Option 2 extras
use upper containment, not source-image inversion. No ALL_VIEW or universal
Q-success premise is needed.

The fresh-snapshot argument uses actual maps, sharing, references, dependency
validity and publication barriers. It does not use REUSE's assumed
sound/principal rebuild as a premise proving that fresh snapshot sound.
Reuse follows only for a snapshot already covered by the proof; any separate
principality premise stays on its own route. The reviewers explicitly audited
the full pre-existing HIR contract, rather than strengthening a topology-only
shadow contract to obtain the result.

The curator added **only `HIR_WIRING -> SOUND`** and promoted SOUND to
CONDITIONAL-CLOSED. HIR_WIRING's definition and IMPLEMENTATION-ONLY status,
all semantic prerequisites and all other existing node statuses/edges remain
unchanged from §8's checkpoint. Its PROJECTION/FRESH_LIFE/RESOURCE cone already
contains the needed implementation correspondence. The narrower aggregate
countermodel remains valid without this full HIR premise; it does not refute
the stronger route. No actual upstream proof or compiler implementation is
claimed complete.

| Status | Starting remote | After reviewed SOUND delta |
| --- | ---: | ---: |
| CLOSED | 6 | 7 |
| CONDITIONAL-CLOSED | 17 | 20 |
| OPEN-PROOF | 46 | 43 |
| OPEN-SEMANTIC | 19 | 19 |
| IMPLEMENTATION-ONLY | 1 | 1 |
| BLOCKED-BY-USER-DECISION | 0 | 0 |
| Nodes / edges | 89 / 194 | 90 / 196 |

This is **65 -> 62 existing OPEN nodes**, by the three proved conditional
compositions CALL_TYPE, PRINCIPAL and SOUND. REC_INIT_SELF is separately a
new CLOSED exact approved subcase. No additional conditional node or semantic
postulate was introduced to obtain these reductions.

The canonical SOUND delta was compared exactly against the byte-equivalent
local/published checkpoint `19d000aa` / `64e459e3`. The only status change is
SOUND, the only new edge is HIR_WIRING -> SOUND, and every other node's gate,
premises, result scope and production-authority field is unchanged. The
outside-SOUND reference additions identify the unadopted remote Call candidate
and the reviewed structural shadow; they add no judgments. The generator,
rendered ledger and both navigation maps are synchronized.

## 11. Published checkpoints and remaining verification

The reviewed structural shadow was committed separately, followed by the
reviewed Call/PRINCIPAL/q1 and world/original/aggregate proof packet. The
remote `7423c12a` was merged after semantic dependency inspection. These
checkpoints were published nonforce to origin as `3c5b0058`, `8e4c0384`, and
`64e459e3da4bd1a347b554806df1b46991eb6765`; the final merge retains
`7423c12a` as a parent. The remote ref was checked immediately before its
expected-HEAD update. The fetched published tree is exactly
`af4075e6af32369d0cbfb4d6ea884b02e93b680d`, matching the local reviewed merge.
Original local history is retained on a checkpoint branch; no force update
or worker rollback occurred.

At this published checkpoint, the subsequently reviewed SOUND record delta
and narrow source/interface results still needed final navigation/whitespace
checks and another expected-HEAD publication. §§12–13 record their completed
review and the later external integration, which added a concrete code delta
and therefore received new focused integration checks. The exact final
published ref is reported by the primary after its expected-HEAD update and
fetched-tree verification; no document claims its own future commit hash.

## 12. Downstream attacks after SOUND: no further promotion

The primary immediately tested SOURCE_ADEQUACY and IFACE_FORM against their
full existing prerequisite contracts. Fresh independent research packets
returned the following exact remaining interfaces. Neither packet wrote a
standalone note or recommended another conditional node: the current
prerequisites do not discharge these additional actual correspondence laws.
The purpose here is to preserve the concrete next local targets, not to count
signature extraction as another OPEN-node reduction.

### Raw operational constructor correspondence

RAW_SOURCE's existing complete atom generation/inversion concerns independent
typing derivations. REF_SIM's simulation consumes decorated constructor and
world certificates. General source adequacy additionally needs, for each
actually included constructor `r`, the local head

```text
Emit_r(original constructor, children, decorated derivation, J_r; X,xi)
and the independent local/world/history/descriptor certificates
and OpCorr(child_i, decorated_child_i; same original witness family)
  => OpCorr(r(children), decorated_r; same original witness family).
```

`OpCorr` here abbreviates the existing target's two operational derivation
transports: actual `SourceExec` and the emitted decorated computation agree on
corresponding finite prefixes/admitted histories, actual provider roots,
entry/body/consumer/result ports, raw handles, pending suffix, re-entry
delimiters, original `nu,K,D` and witness scopes. It is a local rule to prove,
not a new source semantics or a new sufficient assumption to relabel the
aggregate closed.

The actual Lambda/source-function constructor was attacked after the already
covered Name/Return operand cut. [Ordinary computation semantics](../design/2026-10-02-ordinary-computation-semantics-package.md)
§3 and [typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
§§3,6 establish inert creation and the original retained lexical references.
Their source `ApplyValue(Closure(entry;body,...),t,Cnow)` and decorated
`Invoke(entry_P,X[body],t)` heads reduce future invocation to **actual raw
body Run versus the emitted decorated body relation**, at the same original
environment/current world and complete remaining consumer/return suffix.
Head reduction and identity retention do not establish that body square.
The independently supplied entry/world/history certificates remain required.
No interpretation of an unlisted raw wrapper, raw-source-as-core-image
definition, or full current-Authority countermodel is claimed. SOURCE_ADEQUACY
therefore remains OPEN-PROOF at this actual constructor correspondence.

### Finite interface records and actual accessor correspondence

If the full existing PROJECTION and GENERALIZE contracts are established,
the whole exported relation, ordinary-use/evidence transport, original eligible
binders and fixed imports are available.
Packing those outputs together with original typed ports and anchors covers
the ordinary-use observation class. IFACE_FORM additionally quantifies over
every actual downstream inference observer, as required by the
[Authoritative interface comparison boundary](../design/2026-10-04-scc-intrusion-cross-edit-rebuild-addendum.md)
and the [lifecycle theorem](2026-10-05-inference-lifecycle-interface-conditional.md)
§2's independent interface-only interaction hypothesis. Those sources do not
identify all such observers with ordinary scheme queries.

The minimum constructor record laws to derive are

```text
emit_iface_r(original constructor data, child records) = E_r;
decode_atoms(E_r) = RAW_SOURCE's exact original r-atoms;
Observe_r(original constructor/child data; xi)
  = Eval_accessor_r(E_r; xi).
```

The finite typed record must carry original sort/scope/binder and rigid-input
references, ordered primitive/kernel operands, recursive roots/operator back
references, original origin/receipt/owner/continuation/path incidence, evidence
and admission dependencies, and every field the actual observer reads.
For an actual required evidence accessor the smallest concrete equation is
its selected evidence reference equals the emitted record reference, with
all original scope/identity dependencies. This does not claim that the
current compiler exposes an additional selection observer: the actual read
interface must first be identified, then its equation proved. No opaque
AllFuture predicate, printed-scheme equality or allocation ID substitutes.

These laws are narrower than assuming a complete interface, but their actual
constructor/accessor instances remain unproved. IFACE_FORM and IFACE_EQUIV
therefore retain their existing statuses. No speculative evidence-selection
model is promoted to an actual Yulang counterexample or user-decision claim.

### Independent frontier review

Fresh `round3_final_frontier_referee` and `round3_final_frontier_spec` reviewed
only §12 and its direct governing contracts, independently and read-only.
Both verified frozen whole-file SHA-256
`a5a56f0b578c6d82f4adf70a38999f3e4c3e1f01201d8e3b3e6e63ba8388ba83`.
Neither found a blocking or major issue. The referee's one minor wording
clarification is applied above: PROJECTION/GENERALIZE supply those outputs
**if their full contracts are established**; their OPEN status is unchanged.
The spec auditor reported no findings. The primary accepted both reviews and
the exact clarification; no additional review round was required by either.
The canonical SOURCE_ADEQUACY and IFACE_FORM leaves now retain the reviewed
local operational and actual-accessor equations. There is no further node,
edge, status promotion, semantic adoption or user-decision blocker.

## 13. Final external delta and merged-state validation

The next pre-publication ref check found remote
`4a9d969db09be881bdc0ce6888cc3d651dfc2405`, whose first-parent work includes
`d48ed5eb` (three captured-Call original-fiber notes) and `bf66cec6` (current
Q/R capture and a historical Call crosswalk). The remote merge retains the
already published `64e459e3` checkpoint. The primary fetched it, committed
the reviewed SOUND and §12 changes separately, and merged it as local
`56c66234c51892db2af2dacd4eff1f4f0e271bd2`. Git merged the additive task
record cleanly. All eleven remote changed files are preserved, with no
governing design, approved answer or question receipt changed by this delta.

### Semantic dependency review

`round3_final_frontier_referee` received a separate read-only integration
packet for all three newly merged original-fiber notes and their direct
governing contracts. It found no blocking or major semantic finding and
confirmed that all three conditional closures and exact q1 remain valid at
their existing scopes. The primary accepted this review. Current bytes are:

| Remote artifact | Current SHA-256 |
| --- | --- |
| [Captured-Call construction](2026-10-09-original-call-fiber-construction-round4.md) | `2d55271aaaaa5d4af7b912116fa3299431bc10cc16926118767182695b2c4977` |
| [Joint-incidence obstruction](2026-10-09-original-call-fiber-adversarial-round4.md) | `86bca1a6fbb88479192bc548a9f8d35ca436766555998d8941b59d862db3a262` |
| [K-Owner pair audit](2026-10-09-original-kowner-underdetermination-round1.md) | `4856d0848d50cb07f2d10ef048970d2450a1328805a2d51b57da3b9ca7e1b6c8` |

These files visibly record their previous compiler-referee reviews but do
not identify those reviewer sessions or reviewed-byte hashes. This integration
review independently checked the **current** displayed contracts. The
canonical ORIGINAL_ASSOC leaf retains O0/O1/C0/C1/J0 separately, preserves
the stronger owned full-image and complete-family requirements, and adds
the actual joint-certificate/witness-linked-lossless-decomposition cut.
The even/odd parity example is a sorted algebraic information-loss theorem;
it is neither two complete Yulang semantics nor failure of the existential
original-fiber target. The unsuccessful K-Owner pair audit establishes no
user-decision blocker. No additional node, edge or status promotion follows.

The referee's one minor finding concerned dependency provenance. The K-Owner
note records a construction hash `a24dd836...`, while its present reviewed
dependency has the `2d55271a...` bytes above. The earlier producer snapshot
is not independently retained in this integration packet, so **no claim of
exact historical byte equality or metadata-only change is made**. The current
O0/O1 content was directly rechecked and agrees with the audit's substantive
use; its current-byte integration review is the evidence for this merge.
The original hash record is preserved unchanged. This closes the integration
accounting issue without rewriting history or certifying an unavailable
snapshot.

The primary also compared every plain recorded dependency hash against both
the pinned `7423c12a` objects and current files. Construction has 23 exact
matches and one historical canonical-ledger hash; adversarial has 16 exact
matches; K-Owner has 10 exact matches and the construction snapshot exception
above. The construction note's ledger is explicitly navigation only. Its
`152572e5...` hash matches that pinned baseline, while the current ledger has
the separately reviewed round-3 reductions. All governing design/answer/
receipt inputs in these lists are byte-identical. No obsolete navigation
status is treated as proof authority.

### Shadow dependency review and executed checks

`round3_final_frontier_spec` separately inspected the two remote shadow notes,
their exact implementation/test cone, and compatibility with the retained
initialization collection token. It found no blocking, major or minor issue;
the primary accepted the review. Reviewed note hashes are
`09d184cf3c1bf7e041ae58e2a338dbcc151b12d5cece77ceaf8051543bb48540`
for Q/R capture and
`61a559d11fa631f3c3211f231560224508d28382198fba8ba35c6e2a0f71ff69`
for the legacy crosswalk. The latter test still matches its recorded
`91452cb80f3cd51a9317779825973e4e077d6c0ccce50eac03d211022ec1eb42`.

Only the explicit shadow solve entrypoint requests Q/R capture; ordinary
solve stays uncaptured. Failed routes publish no successful evidence, and
incomplete retained traces remain `Unavailable`. The cold observer qualifies
rows by the capture, uses by the collection
and binders by the finalized scheme. Initialization keeps its exact token
and both pending q1 obligations. No directional protection or provider-role
judgment is produced. The crosswalk retains the ordinary refusal boundary,
empty semantic facts and every pending application/source-view premise.
The remote note's former task-record deferral is now reconciled: the current
task contains both slices, the canonical ledger and maps link them, and no
old index ambiguity remains in the primary's integrated tree.

On that merged code the primary executed, sequentially with the already
owned Rust 1.90/cache/target configuration, two Cargo jobs and a 180-second
per-command cap:

| Focused check | Actual result |
| --- | --- |
| Combined-feature `shadow_initialization` integration target | 4 passed |
| Combined-feature `shadow_legacy_local_application_provenance` target | 1 passed |
| Combined-feature library filter `fresh_capture` | 5 passed, 470 filtered |
| Feature-off `cargo check --locked -p yu-core -p yu-hir -p yu-solver --offline` | Passed without warnings |

The first two targets shared one Cargo invocation (`--offline`, both
`shadow-f5,shadow-scc-observer`, one test thread), compiling in 5.85 seconds.
The five capture tests compiled in 18.69 seconds and ran in 0.42 seconds;
the feature-off check finished in 1.04 seconds. These are focused integration
checks, not a broad suite, performance claim, semantic proof or rerun of the
historical Oracle. No further code changed after these checks.

The final canonical scope remains §10's **90 nodes / 196 edges**, with
7 CLOSED, 20 CONDITIONAL-CLOSED, 43 OPEN-PROOF, 19 OPEN-SEMANTIC,
1 IMPLEMENTATION-ONLY and no user-decision blocker. Existing OPEN nodes
decrease by exactly three from the original latest-remote baseline. The
current source/interface and original-fiber cuts are reviewed reductions of
remaining leaves, not additional closures. Production inference cutover
remains prohibited.

Final documentary checks passed after that synchronization: the canonical
generator validates 90 nodes / 196 edges and all 32 requested families;
an exact comparison to starting `6fb5d7f6` finds only CALL_TYPE, PRINCIPAL
and SOUND promoted, only new CLOSED REC_INIT_SELF, and exactly the two
added prerequisite edges REC_INIT_SELF -> REC_INIT and HIR_WIRING -> SOUND.
No previous edge or node was removed. All four preserved ledger/map files
remain byte-identical to the starting remote, and all three approved q1
question/draft/answer files remain byte-identical to `a814bc76`. The two
reviewed initialization code/test hashes are unchanged. All 706 relative
Markdown file-link targets in the complete changed-file set exist; this
checks file targets, not every fragment anchor. Baseline-to-worktree
`git diff --check` passed.

The final bounded round-3 Call/original checker rerun also passed under
the original 1 GiB address-space / 60-second cap: 64 finite assemblies,
128 analytical-diagonal instances, all 512 finite 3-by-3 coverage matrices
(169 positive), three independent-rule seams and the repaired Call-input
vacuity/coherent-witness checks. Its scope remains sorted algebra; it
constructs no original source kernel or admitted semantic world. The DAG
validator likewise explicitly reports `semantic_proof_checked: false`.
