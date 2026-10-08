# Captured step cut: phase-sensitive coordinate elimination

Date: 2026-10-08
Status: non-authoritative research; frozen on submission; independent review pending
Baseline: `521f1cc0c758a2e75c1bcae061045abe2a6ff400`
Lease: this file only
Method: constructor-relative counterexample and original-scope alias elimination
Production implementation, new source restrictions, aggregate gate closure: none

## 1. Objective and result

Audit the finite cut in [transformed export bridge](2026-10-08-generalize-export-constructor-bridge.md)
§§4.3, 6 for the selected source

```yu
my apply f = { my step x = f x; step }
```

One source-derived elimination is available: the descriptor abbreviation
`R_c := ReadInvoke(F_c,D_c,IF_c)` can be expanded at its original scope with
all dependent decorations. This removes the abbreviation, not the constructor's
operands or complete interpretation. It establishes no size bound.

The distinct attack here is **replacing the entry carrier and its phase
evidence by the eventual parameter result**. A pending entry has an actual
carrier, request, raw handle and suspended suffix, but no actual `x` result.
Consequently the source Return/rebind map is partial on the complete observation
domain. Treating it as a total definition loses an admitted prefix or invents
a result witness at the wrong phase. This remains a failure even with captured
f, original scopes, all static identities and all fixed dependencies preserved.

This falsifies a specific proposed shortcut, not the bridge's conditional
theorem: H-cut already requires the complete phase cases that exclude it.
No counterexample to a supplied complete H-cut certificate is established.
A reusable Strict phase schema retaining these cases could avoid storing
carrier allocations or body code. Its actual-root interpretation and complete
consumer proof are the remaining supplier, not another endpoint or copying
experiment.

## 2. Baseline and exact dependencies

All semantic inputs were read from committed `BASE:path`. Dirty shared task,
architecture, theory/DAG and index bytes were excluded. Committed task/index
reads were navigation only. No unfinished construction artifact or pending
`readinvoke-source-presentation` question was consumed. Narrow keyword reads
of the committed earlier interface-factorization and finite-boundary-cut
notes were used only to check method overlap, not as proof premises.

| Governing source | Exact scope used |
| --- | --- |
| [q1](../../questions/2026-10-08-successor-generalize-root-policy/question.md), [approved a1](../../questions/2026-10-08-successor-generalize-root-policy/approved-answer.md), [receipt](../../questions/2026-10-08-successor-generalize-root-policy/receipt.md) | Decision items 1–5: transformed actual export, displayable scheme plus necessary use information, no use-time traversal of the whole definition, actual-root safety/admission/membership and Option 2 obligations. No representation or sufficiency theorem adopted. |
| [Function views](../design/2026-10-05-inferred-function-call-views.md) | Authoritative §§1.1–2, 5: original joint indices and source incidences; admission independent of Q. |
| [Captured closure definition](../design/2026-10-08-captured-closure-constructor-definition.md) | Authoritative §§2–4: complete Strict composition, pending/raw/future cases, independent background, all W/Z alternatives. |
| [Captured closure theorem](2026-10-08-captured-call-closure-introduction.md) | Selected §§3–5 and Theorem Step §6: independent carrier progress, pending entry, actual Return as the first x-binding phase. Its original candidate wording is historical within the subsequently selected scope. |
| [Pure-read definition](../design/2026-10-08-pure-read-call-result-constructor.md) | Authoritative §§2–5: complete original indices, staged ReadInvoke, selected identity result, genuinely independent arm inputs. |
| [Contextual membership](../design/2026-10-08-contextual-function-membership-definition.md) | Authoritative §§2–3: independent complete challenges; divergent admitted carriers; separate inert Delay formation and designated execution. |
| [Source interface definition](../design/2026-10-08-call-source-interface-definition.md) | Authoritative §§2–3: slots preserve complete contracts; open carrier hole has a source diagonal and other independently admitted fillings. |
| [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md) | Reviewed conditional §§3.2–3.4, 3.7, 5.3: ordered Bind, independent complete histories, certified transformations, whole-tuple extras, ordinary complete query. No exhaustive production grammar selected. |
| [Bridge](2026-10-08-generalize-export-constructor-bridge.md) | Non-authoritative §§3–6: original-scope H-cut and actual transformed-root consumers; §4.2 explicitly requires totality. |
| [Candidate](2026-10-08-generalize-export-constructor-candidate.md), [prior falsification](2026-10-08-generalize-export-constructor-falsification.md) | Prior conditional lossless transport and structural attacks; used only to avoid repeating them. |

Rules read in full: design-authority, research-lab and git-concurrency.
Authority selection and the q1/a1 interpretation were not reopened. In
particular, this note neither changes result interpretation nor declares a
formal eligible from its name. Assume any needed eligible/fixed partition is
supplied separately; this attack leaves that partition unchanged.

## 3. An elimination justified by the selected definition

The selected pure-read definition §4 identifies the full decorated result
descriptor with ReadInvoke at the same original tuple. For a fresh abbreviation
introduced exactly by this identity, substitute

```text
Strict(I_x,x:A_x,R_c,IF_step)
  -> Strict(I_x,x:A_x,ReadInvoke(F_c,D_c,IF_c),IF_step).
```

Every reference to the abbreviation must receive the same substitution,
including admission, evidence and ordinary-query operands. No scope is moved,
no fixed input is rebound, and all constructor decorations remain. Expansion
and introduction of the abbreviation are inverse descriptions of the same
interpreted object. This is an established definitional elimination within
the selected scope, instantiated at this source.

This does not eliminate an independently fixed foreign `R_c`, `A_step`,
`F_c`, `D_c`, `IF_c`, current world, provider or evidence. Nor does it certify
an independently named transformed root `g_step`: that root still needs its
own interpretation and query law. If expansion retains a full source-dependent
interface graph, q1/a1's abstraction objective remains unmet.

## 4. Minimized attack: use eventual x to erase entry progress

### 4.1 Exact candidate premise

Consider a mutation of the proposed cut which keeps the captured f contract,
`I_x`, `A_x`, role, root incidence, original binder tree and fixed anchors,
but discards entry-carrier/phase evidence on the premise

```text
entry carrier and its complete entry evidence = t(eventual x result).
```

Its use checker substitutes the body-at-x contract for complete entry
progress, or recovers a result witness to justify that substitution. The
mutation is stronger than eliminating a carrier's allocation name while
retaining an independently interpreted complete Strict schema.

The only actual source map to x here is Force Return followed by typed rebind.
Theorem Step explicitly places x's binding at that Return. There is no total
source map from all admitted entry prefixes to actual x results.

### 4.2 Smallest constructor-relative witness

Hypotheses, all fixed independently of the cut/checker:

1. The selected Step theorem's actual captured f/background inputs hold.
2. At one genuine complete challenge of step, `I_x` admits a carrier with
   one actual typed pending request `Request(q,C,k_x)`, together with its
   original response/raw-handle/authority/world evidence.
3. The observation projection or a complete consumer reads this request or
   its pending evidence. The selected Strict contract does retain it.

At that prefix, after the one receipt and designated Force, the original
ordered relation contains

```text
Request(q,C,k_x) >>= S_x
  = Request(q,C,(response,C').k_x(response,C') >>= S_x)
S_x = actual-typed-rebind-x; body-Call; original-invocation-return.
```

There is no x-binding/result yet. The original prefix is admitted and has its
pending contract, while `t(actual x result)` has no operand at this binder
position. Requiring that operand loses the prefix. Inventing it violates the
selected Return/rebind incidence and creates evidence before its licensed
phase. Replaying receipt when resuming also changes the original suffix.

One pending request, one carrier, one invocation and one captured closure
suffice. No second use, recursion, handler ambiguity, port split, capture
freshening or root-shape collision is needed. No resume is needed to expose
partiality. If an admitted response resumes `k_x` to `Return(a,C')`, x first
exists there; this confirms the suspended dependency but adds no premise to
the initial failure.

The alternative no-operation separator is an independently admitted divergent
carrier: it has entry prefixes and no x Return at any time. This requires
its genuine full carrier certificate, and is not a declaration that every
`I_x` admits divergence.

### 4.3 Is this source-admitted?

The raw prefix and suspended suffix are selected source constructor cases,
not arbitrary Boolean transition rules. The Step proof's “Arbitrary I_x
carrier progress” and “Pending entry and divergence” cases supply their
conditional membership proof at the same original witness. A Name carrier
is not assumed for the receiver's outer argument.

The witness is therefore **source-constructor-relative**, conditional on the
genuine independently admitted pending-carrier packet in hypothesis 2. This
note does not instantiate a complete concrete world, primitive request,
license, `I_x` admission or production kernel proving that packet inhabited.
It does not claim a compiled Yulang counterexample. If the fixed `I_x`
contains only terminating request-free carriers, this particular request
witness is unavailable; the cut still needs a totality proof for that exact
domain. Restricting an otherwise supported domain to make it unavailable is
not authorized by this research.

This differs from earlier endpoint and fixed-capture models: the failure is
an actual missing result at an original operational phase, with the fixed
inputs and static interfaces held intact.

## 5. Surviving cut and exact missing certificate

The attack leaves a natural route: erase implementation allocation details
but retain an interpreted Strict schema which suspends x-dependent obligations
until actual Return and carries pending/raw/current-world evidence meanwhile.
Its finite syntax can quantify over unbounded finite histories; finite syntax
does not prove those histories irrelevant or bounded.

For the actual `g_step`, a finite cut certificate must give at least these
complete cases at their original scopes:

| Case | Required preserved fact |
| --- | --- |
| Independent challenge formation | Same whole-carrier/context/receipt guards and correlations, independently of Q or actual receiver acceptance. |
| Before Return | No x-result witness; actual receipt/Force phase, raw request handle and exactly the suspended suffix. |
| Actual Return/rebind | Same actual x/provider and live world; dependent body starts only now. |
| Body and later future | Same captured f; ReadInvoke's staged complete tuple and actual output provider/future ports. |
| Every retained W/Z alternative | Its own guard, admission/domain action and introduced provider/future interpretation; no source execution fabricated. |
| Complete ordinary query/evidence | Local complete-query derivation at `g_step`, with necessary evidence already compiled into interpreted boundary data. |

The producer's code derivation may prove these equations once. An ordinary
use must read the resulting schema/evidence without following a source token
back to reconstruct the code. Preserving a source-only result theorem does
not certify the extra arms. Definition expansion of `R_c` also supplies none
of the arm-local domain laws.

No absence or impossibility of a finite complete boundary schema is proved.
The precise blocker is a source-derived, phase-complete public constructor
interpretation and its actual-root admission/query certificate. It is not
the number of identity names. Earlier lossless packaging and retained-root
certificates leave this same premise untouched; a third checker accepting a
desired transition table would add no source evidence.

## 6. Claim classes, independence, coverage and resources

- Established dependency reused: the selected decorated ReadInvoke identity
  permits abbreviation expansion; complete Strict keeps actual pending cases.
- Conditional derivation: eventual-result erasure fails under the independently
  admitted pending-carrier packet above; the full H-cut theorem survives.
- Candidate assumption not proved: a particular concrete `I_x`/world/primitive
  package inhabits the pending case. No production source acceptance claim.
- Bounded characterization: one symbolic source constructor case and one
  alias elimination. No numeric enumeration or all-source characterization.

The oracle is the committed selected constructor equations and independently
supplied carrier/primitive contracts. The argument shares their interpretation
with the bridge and is not an independent validation of those contracts. No
transition checker, compiler test, build or mutation run was performed. The
named mutation is analyzed deductively. Seeds, numeric ranges and experiment
samples are not applicable.

Unverified scope: concrete request/world inhabitance, foreign descriptors,
all Option 2 arm laws, actual public Direct acceptance, local semantic
eligibility, all valid-view coverage/principality, general recursion/State,
solver conformance, compactness and production implementation. Finite source
proof and structural source/interface searches were not exhaustive. Broad
task/theorem reads produced truncated output and were used only for locators
or subsequently targeted selected sections; no exhaustive-reading claim.

Failure conditions for the separator: no independently admitted pending
carrier; a projection/consumer that legitimately ignores the entire pending
distinction under an independently proved complete contract; or a cut retaining
equivalent phase evidence instead of erasing it. The last case is a valid
response to the attack and still needs its own `g_step` certificate.

Resource envelope: one sequential lightweight read/check process at a time,
zero Cargo/heavy processes, no calculation wave and one output path. No
explicit numeric wall-time/CPU/RAM budget was provided in this assignment;
elapsed research time and peak CPU/RAM were not instrumented. No performance
claim. Freeze checks and fingerprints are recorded below. Writes stop before
submission; producer inspection is not independent review.

Recommended next action: the owning constructor-cut producer should retain
Strict's phase schema and prove its actual-root complete admission/query
cases, including independently licensed extras, rather than derive entry
behavior from the eventual parameter result.

## 7. Freeze checks and dependency fingerprints

Freeze dependency check: current HEAD `521f1cc0c758a2e75c1bcae061045abe2a6ff400`. All 19 direct
semantic/rule/bundle/history dependencies are byte-identical between the baseline,
current committed HEAD and working-tree files. The committed a1 draft is
embedded unchanged in the approved answer. All 14 local Markdown link
targets exist; no trailing whitespace was found. Narrow commands used read-only
Git plus one Python process; no compiler tests/builds. Final artifact SHA-256
is supplied in the submission report.

```text
925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5  rules/design-authority.md
5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6  rules/research-lab.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e  rules/git-concurrency.md
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1  notes/design/2026-10-05-inferred-function-call-views.md
6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd  notes/design/2026-10-08-captured-closure-constructor-definition.md
0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f  notes/theory/2026-10-08-captured-call-closure-introduction.md
8d1eb7ecea3e63d7ba0ae091dc673f3321e52fc0e31c5d824bdf4f1656b99488  notes/design/2026-10-08-pure-read-call-result-constructor.md
0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0  notes/design/2026-10-08-contextual-function-membership-definition.md
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c  notes/design/2026-10-08-call-source-interface-definition.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186  notes/design/2026-10-05-source-contracts-and-common-allowance.md
0b52e7af26f91f894a01cb69b22e295627566cfb15dfede7967128e9253e79bb  notes/theory/2026-10-08-generalize-export-constructor-bridge.md
29dab9a94f73cf094aaf4490025dac6a0c380ac27656683ba773f228d5badb05  notes/theory/2026-10-08-generalize-export-constructor-candidate.md
8ff978afb5250bb7f7b217c504962df69734498f612f5382cbf0380a21df2f4f  notes/theory/2026-10-08-generalize-export-constructor-falsification.md
69f43d833a0237523c88a26125f3cf4878e599e38903f84b458d437da662072b  questions/2026-10-08-successor-generalize-root-policy/question.md
6234a26dd6491b67d92b3f86421160becf52779ef3188b12fbe49fa84c28bbed  questions/2026-10-08-successor-generalize-root-policy/answer-draft.md
e358a5d796f0a26b2d7dbe5891b3d1f21d0ac9089ab655796fa0b696a13194e5  questions/2026-10-08-successor-generalize-root-policy/approved-answer.md
c3bb6fbab0e3ba431fca56b4b7cdca54278d66a3711eb47bf8b9f9a812322a42  questions/2026-10-08-successor-generalize-root-policy/receipt.md
3e68f03311dffd892433e1d99b5f7f77a1d162df72bedef95b67474d1a5210fd  notes/theory/2026-10-08-captured-step-interface-factorization.md
4eaeb482aaf23d42809a8253a3e755ef7105395be711f7c94dce9d900fe53f45  notes/theory/2026-10-08-captured-step-finite-boundary-cut.md
```

## 8. Commit packet

- Exact leased path: `notes/theory/2026-10-08-transformed-step-constructor-cut-falsification.md`.
- Baseline SHA: `521f1cc0c758a2e75c1bcae061045abe2a6ff400`.
- Dependency hashes/changes: §7; committed inputs only, no concurrent inputs.
- Claim/review: non-authoritative constructor-relative separator and scoped
  definition expansion; independent review pending; no gate closure.
- Checks already run: final dependency/byte integrity, local links and
  whitespace checks reported in §7; no tests/builds or executable probes.
- Proposed one-line research-checkpoint commit message:
  `research: audit phase-sensitive captured step boundary cuts`.
- Shared-record deltas intentionally left for primary/curator: cite this
  source-relative pending-entry obstruction and retained Strict phase cases;
  keep actual transformed-root/Option 2/query coverage gates open. Do not
  reopen source constructor or native Generalize selection. No task/index,
  authority, theory-map, manifest, lockfile or question-board changes made.
