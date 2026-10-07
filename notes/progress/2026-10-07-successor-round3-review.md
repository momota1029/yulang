# Successor round 3: closure, repair and integration record

Date: 2026-10-07 UTC
Branch: `research/simple-sub-intrusion`
Primary: Astra; source self-init synthesis and final proof adjudication
Start remote: `6fb5d7f697d5d592e0a39532ddb4967b54e18090`
External remote delta revalidated: `6cd43ea855acdd1e7f47a46408715a03d192ffd4`
First published checkpoint: `31b97ed3b56db5a642ae9eddeebda366af74233e`
Status: proof panels and canonical-record delta passed; final integration and downstream attack in progress
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
