# Callback profile applicability at symbolic value leaves

Date: 2026-10-15
Status: independently reviewed authority/source obstruction analysis; accepted
major finding repaired and independently closed.
No complete-profile theorem, semantic underdetermination theorem, or gate closure.
Pinned baseline: `5e7d44f3251514c17762a8c61c9be8e371cb4994`.
Production baseline supplied by primary: `266da3dd6cf73b4b6267919384cce9389d653f46`.
Exclusive lease: this file. No implementation or semantic authority.

## 1. Frozen claim and outcome

The parent is the source-component/B-delivery obligation of
[Function callback profile construction](2026-10-15-function-callback-profile-construction.md):
for every originally supported known ordinary `Value(Function)` formal,
construct its original static `beta` and complete original profile before the
callback literal body is elaborated. Cover its applicable complete-call and
latent-result observations, including symbolic value leaves and higher-order
inputs/results, without enumerating future inferred shapes or narrowing source.
Keep original owner `d`, formal `x`, annotation `a`, binding scope `S`, original
path identities and one joint `xi=(nu,K,D)`. Keep rigid/existential binders in
their original scopes. No per-port or per-history witness choices are allowed.

This pass does **not** discharge that parent. It identifies a governing
source rule absent from the historical profile note's dependency list: the
[directional protection addendum](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
§§2–6, and its independently reviewed
[local constructor](../progress/2026-10-06-directional-protection-source-generation.md)
§§2–5. A generic symbolic leaf is not a license to default-mark every effect
position of its eventual type. Its already selected local introduction is a
source upper-exposure rule with a protected-variable premise.

**Decisive result:** an annotation/type-shape-only interpretation of the
requested constructor loses information the selected rule requires. The
finite original source provenance can supply that information; an exhaustive
future shape inventory and complete endpoint-membership solver cannot replace
it. The exact residual is classification of the actual source receipt,
result and use: derive a justified seed/exposure or independent typed-profile
transport where applicable, or establish justified non-applicability of this
directional introduction. Preserve independently inherited evidence; absence
of this seed does not establish semantic absence of protection. Connect each
applicable constructor to the original callback template. No two complete constructions satisfying all
authority have been established, so no new semantic decision is requested.

## 2. Exact authority and the apparent parent mismatch

[Callback context](../design/2026-10-03-callback-context-delivery.md) §§2–2.1
requires an already instantiated formal and supplied original `beta,Slots(beta)`
before **the callback literal's** body constraints. It does not state that
arbitrary profile applicability is a function only of annotation syntax, or
that the callee's own source definition/use evidence must be unavailable.
Its B rule still selects Handler/boundary, synthesizes independent literal
endpoints and checks the complete inequality. Nothing here changes B.

The directional addendum §6 explicitly retires the old unconditional
`Applicable_original -> p0` target and requires enumeration of source-justified
directional exposures with their original seed witnesses. Sections 2–3 specify
both the positive upper-use conclusion and the no-backflow conclusion;
§5 rejects automatic whole-result traversal. These are direct user decisions
within that document's stated scope, despite its Draft formalization header.

Consequently the historical profile note's phrase “from the original
declaration/formal/annotation occurrences” has two different readings:

- **Annotation-only:** all applicability follows from the original type tree
  and its eventual substitution. This reading cannot cover the directional
  source rule. Adding a leaf that means “all later descendant effects” repeats
  the explicitly rejected strengthening.
- **Source-indexed:** original declaration/formal identity anchors the profile,
  while actual source uses and valid seed transport introduce incidences.
  This is compatible with B's supplied-context requirement. It remains an
  unproved constructor for the original broad domain.

The first reading is a failed proof method, not a counterexample to B or a
license to remove the parent. The linked profile note has since received a
separate independently accepted authority correction to the source-component
obligation. Its old dependency hash below records the inspected historical
snapshot, rather than the corrected current text. Static original profile identity can stay
original while its source exposure witnesses differ. The old directional
proof explicitly says that distinct use witnesses can share an original slot;
it does not equate the number of source uses with `|Slots(beta)|`.

[Typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md) §6
introduces profiles at applicable signature positions and transports them
through matching paths. Its Receiving-side consequence does not introduce
missing input profiles. The
[receiver-relative clarification](../design/2026-10-15-callback-identity-forwarding.md)
fixes protection against handling within the receiving boundary and its
outward limit. It does not erase the earlier explicit upper/lower distinction
or select a whole-result schema. Whole-carrier entry and latent transport
preserve complete observations and evidence once their source correspondence
exists; they do not turn private closure fields into public received inputs.

## 3. The existing symbolic-leaf rule and its exact limit

Freeze a source seed `k`, original endpoint `v`, scope `S`, and an actual
source upper exposure `u` with complete Function demand `U_u`. The existing
rule is:

```text
ProtectedVarAt(k,v,S,u)
SourceUpperUse(u,v,U_u,S)
---------------------------------------------- Dir-Protect
NewProtection(k,beta,u,S,outEff(U_u))
```

This is a finite rule schema. It does not enumerate the shape assigned to
`v` by `nu`, inspect concrete effect membership, solve the demand, or independently
choose a provider. The original local proof already establishes exact coverage
of this one rule, no backward propagation to provider lowers, and coherent
renaming of its whole seed/exposure inventory. Those results are reused, not
reproved or promoted to full-source completeness.

At a symbolic leaf, this rule is applicable **only when its two premises
are source-derived**. It concludes one upper output-effect incidence; it does
not seed the upper argument, result value, all nested latent effects, or a
provider lower. Using this directional rule at a subsequent result exposure
conditionally requires that exposure's own protected-variable premise and
source upper demand; the rule does not demand a new seed at every returned
symbolic leaf. Independent typed-profile transport may apply instead, or this
particular introduction may justifiably be inapplicable while inherited
evidence remains. An arbitrary substitution that replaces `v`
by a Function shape is not such a premise. Transporting an already constructed
certificate under an admissible same-use substitution must retain its original
variable-stage/use identity; rerunning a shape traversal on the substituted
type forgets precisely that identity.

Here is the exact obstruction, reusing the reviewed directional proof §4:

```text
H_up   = seed(k,v,S) + original source upper v <: Fun(a,b,c,d)
H_down = seed(k,v,S) + provider lower Fun(a,b,c,d) <: v
```

Both can have identical endpoint names, Function shape and assignment `nu`.
After erasing source direction/provenance their shape input is identical.
The selected new incidence is at `c` in `H_up` and absent in `H_down`.
Therefore no function of that erased input can implement both required local
outputs: equal inputs force equal outputs. This is an information-loss
argument about an inference constructor, not a pair of executed programs or
two admissible alternative language semantics. It does not prove that a
source-indexed finite schema is impossible.

For any finite source exposure inventory the existing local join is finite.
Arbitrary future calls can reuse source templates and have fresh execution
occurrences. That fact alone does not prove that all future exposures have
valid seeds or that their slots belong to the supplied finite original
inventory. An induction that insists on using Dir-Protect positively at every
previously symbolic result value lacks a justified premise and exceeds the
selected rule. The actual transition instead needs source classification:
its own justified seed/exposure, independent typed-profile transport, or
justified non-applicability of this introduction. None of these cases may
erase independently inherited evidence or infer absence of all protection.
Invocation entry protects the designated carrier; `Force` does not recursively
execute or mark a returned latent value. No transport induction is offered
with a fabricated seed hidden in its invariant.

## 4. Actual constructor/consumer boundary

The following are reads of the pinned native sources, not conclusions drawn
from missing field names or from the older consumer note's stale baseline.

| Owner | Actual construction and relevant limitation |
| --- | --- |
| `yu-hir/src/module/source_annotation.rs:68–94` | Retains annotation owner/position and recursive Function/Variable structure. A symbolic leaf supplies a scoped name; it supplies no original source upper-use occurrence merely by having a possible callable instantiation. |
| `yu-solver/src/candidate_effect.rs:1037–1056,1113–1160` | The Variable branch uses `candidate_annotation_variable(scope,name,level)` and returns the shared polar row pair. Function recursion creates exact AE/RE and child fields. This constructs the coordinate association proved in the prior note; the leaf branch does not construct a nested seed/exposure certificate. |
| `yu-solver/src/candidate_source.rs:618–628,691–715` | Formal Name registration and actual whole-binder `parameter.annotation.is_none()` construct `OmittedFormal`. Omission of a port inside an explicit Function annotation is not this whole-binder condition. |
| `yu-solver/src/shadow_apply.rs:1593–1621` | The actual Apply joins `source_call.formal_name`, original registration/Lambda and `omitted_formals`, then records its complete demand and exact `ResultEffect` before constraint admission. It is an existing source-indexed upper-demand owner. It does not identify every nested annotation leaf or arbitrary returned alias as such a formal. |
| `yu-solver/src/candidate_context.rs:2872–2917,3043–3053` | In scoped mode the original slot-0 introduction creates `ScopedDemand`; authenticated Function-port decomposition clears that demand and applies `protect_body` at ResultEffect, `stamp_input` at AE, and no transformer at Argument/Result value fields. This is current bounded native behavior, not the older identity-only implementation. It supplies no recursive blanket leaf seed. |

The last row does not prove complete native activation, receiver scope, semantic
`ProtectedVarAt`, or hygiene. The independent native-context lane owns its
role/equation derivation. This note does not duplicate that lane. In particular,
neither the successful direct omitted-formal path nor `formal_domains` by
itself classifies all applicable source constructors for a symbolic value
leaf under an annotated callback. An explicitly annotated formal intentionally
lacks `OmittedFormal`; that absence proves neither missing protection nor an
empty profile.
The previous acyclic source-root/capture/FreshUse zip remains reusable with
its original hypotheses, but transports the authenticated root association,
not a newly proved nested profile.

## 5. Minimized residual and next action

A source-shaped discriminator for the missing step is the following schematic
ordinary source (not an executed fixture or claimed current native admission):

```text
receive f at an ordinary Value formal annotated Unit -> alpha
g = call f Unit
call g Unit
```

`alpha` is the original symbolic **value** result leaf, not a computation
effect row. The outer call has an explicit Function coordinate. The second
call has its own source upper demand on the returned result. Classify its
actual source receipt/result/use and all independently inherited evidence.
To use Dir-Protect there, establish from the original source receipt/result
correspondence whether and with which original witness that result endpoint
is protected at the second exposure. Do not infer it solely from `alpha`
later having Function shape, the outer call being protected, or equal rows.
Retain the actual returned value's independently inherited evidence as a
separate source. Alternatively derive applicable independent typed-profile
transport, or justify why this directional introduction does not apply at
that exposure. The latter is not proof that the resulting view has no
protection. This also distinguishes default protection from an outer
concrete grant, which cannot be copied to the nested result port.

**One next action:** a normal Sol source-constructor packet on this exact
result-leaf transition. Inputs are original annotated formal/root, actual
source first Call/result binding, and actual second Call upper demand.
Required output is the source classification of that actual receipt/result/use:
derive the second call's justified seed/exposure and original `beta`/slot
association when this rule applies, derive independent typed-profile
transport when applicable, or establish justified non-applicability of this
directional introduction. Preserve independently inherited evidence in every
case; lack of this seed is not a semantic absence-of-protection result.
Connect the classification to `candidate_formal_value_pair`, the Apply result
owner and the existing directional introduction/typed-transport owners. The
falsifiers are source/provenance erasure, reverse marking of provider lowers,
outer annotation copied to nested grant, or private-binding contamination.
Do not ask for another supplied-profile transport theorem, enumerate future
type shapes, or make complete endpoint solving a prerequisite. If that
classification cannot be derived, report the precise missing source premise
and its owner; missing positive seed evidence alone is not an authority
contradiction. Establish two
authority-conforming distinguishable source constructions before claiming
semantic underdetermination. Higher-order argument leaves remain in the
parent domain and require the corresponding direction-preserving source
analysis; the example does not restrict them away.

Economy audit: correct introduction and natural higher-order behavior remain
A/B. Recovering source exposure from solved shape is D and is avoided by
using the existing source Apply witness. Actual source applicability is not
resolved by retaining a certificate whose premise is still unknown, and it
does not require a positive seed at every returned leaf. Full future-shape
enumeration is not established as a prerequisite. After the two previous
coordinate/transport attempts and this bounded authority/source pass, another
equivalent profile-assuming proof would leave the premise untouched. No
parent status, source domain, or authority is changed here.

## 6. Checks, resources and commit packet

Method: bounded source/authority analysis and reuse of the already reviewed
local directional theorem. Commands: `cat`, `sed`, `rg`, read-only Git status,
branch/revision inspection, SHA-256 comparison and note integrity checks.
No build, tests, execution, probe, network, benchmark, Git mutation or child
agent. Zero measurement samples; lightweight shell inspection only. One
25-minute allocated original pass; wall time and CPU/RAM not instrumented.
The normal Sol repair is a separate five-minute bounded textual delta on this
file only, with no code/tests/probes/Git mutation or further delegation.

Requested routing: `prover`, `gpt-6-astra` / `low`, one primary-authorized
localized escalation following the two stated Sol routes. Observed effective
model/effort: unknown; runtime metadata unavailable. The live schema exposes
prover and model/effort arguments; `.codex/config.toml` registers prover and
`.codex/agents/prover.toml` omits model/effort pins. This does not prove that
the requested override ran. No further escalation or delegation was launched.
Repair routing requested: normal Sol/high; observed effective repair settings
unknown. The original requested Astra routing above is producer provenance,
not the routing of this repair.

Unverified: broad profile introduction, all source reachability, admissible
instantiation/future-history preservation, complete Call, actual receipt and
Observe, runtime lifetimes, native all-path activation, hygiene, soundness and
principality. The whole parent remains OPEN. Fresh independent review belongs
to the primary; this artifact is not certified by its producer.

Commit packet: exact changed/leased path
`notes/theory/2026-10-15-callback-profile-applicability.md`; baseline
`5e7d44f3251514c17762a8c61c9be8e371cb4994`; proposed message
`research: distinguish conditional callback seed applicability from inherited protection`.
Shared-record deltas left for primary/curator: add the directional addendum
and local constructor as dependencies of Function-profile construction;
distinguish the invalid annotation-only method from the still-required
source-indexed B supplier; record source receipt/result/use classification,
applicable seed/exposure or independent typed transport, and justified
non-applicability of this directional introduction as the next exact case
analysis. Preserve inherited evidence and keep parent gates OPEN and all implementation
authority unchanged. Do not promote this note to proof closure.

Dependency hashes and static integrity results are appended at freeze below.

Original producer freeze checks: all 25 dependency hashes below matched the
pinned baseline. In particular the first hash is the historical original-profile
note at that baseline; it does not purport to hash its separately corrected
current text. Original checks found all 6 links resolving and clean fences/
trailing whitespace. No semantic executable verification ran.

Repair input artifact SHA-256:
`c08fe9070c4aff6eb1f92b25472228cf4ddc2c4d218ffe0eb548eba2c49f4f52`.
The accepted major finding was the nonexhaustive demand for a positive
second-call seed or an authority contradiction. This delta repairs the matching
claim, conditional-rule description, residual, next packet and shared-record
handoff. The information-loss argument is unchanged. Fresh referee delta review
accepted repaired artifact
`78bbc8faed23d91c02c89adc18e0e56be8ce9ddaf47781535607ec0dc5b9cd08`
and closed the major finding with no remaining blocking, major or minor findings.
The previous clean information-loss/native-direction and source-component
correction verdicts carry forward. No repair producer certification is claimed.

```text
484ccf440bcbb004954e41dbe7512247de0b4b469ba5a3c4ac840b7ad65257ba  notes/theory/2026-10-15-function-callback-profile-construction.md
f11c6594e43c29fbfdbca1638b5c548cecc12a5beb192cac743e60f022c1cc73  notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md
3702eb2ea5108eba1adc8ab7a557542abb9993cee09f70b738e2999a05a2d185  notes/progress/2026-10-06-directional-protection-source-generation.md
df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5  notes/design/2026-10-03-callback-context-delivery.md
1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb  notes/design/2026-10-02-typed-boundary-realization-draft.md
c544ed3c7b83686a740aa43b1db92d901de31a3b197f81f90a4c9dbdae561134  notes/design/2026-10-15-callback-identity-forwarding.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
4a98b5136a9d0d1bdddf135727c5e8779b579bf3c0b76d0524d01c951df34fd4  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e  notes/design/2026-10-02-typed-computation-core-elaboration.md
0fe7dba1af48f7bf60d5cbc7933c1d3562dade5d1f6fac023cd19d25bdd67794  notes/design/2026-10-02-source-realization-and-symbolic-basis.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed  notes/design/2026-09-29-scc-intrusion-redesign-charter.md
f8f8a1934d9961d443b2a0b55a79aa3272ec7cd820f7a40d9bd6217f3456ae38  crates/yu-hir/src/module/source_annotation.rs
deee5a0892b02bc9ee23a1f2a35c76175094c558ed7dfb2cf55a7e115ac54225  crates/yu-solver/src/candidate_effect.rs
90db34173d366ed826b34492da0fb2f1c5422b1b41e43fcda14892ec8415e7ab  crates/yu-solver/src/candidate_source.rs
270ee70b331e4095f404fafafdf0731b57dd451c130cdf251aea2b5944d7cc6c  crates/yu-solver/src/shadow_apply.rs
9f71c8c40d6850bffccb27d7393bf6219f0ceca5cf1fe1e738073ea943706083  crates/yu-solver/src/candidate_context.rs
4689e2ee34c69c9492ecc1a58af15d7c802f44dca82d69f76e3e1520d8d5f3dd  crates/yu-solver/src/candidate_call.rs
993d4c2a7743669b4c7a6c46f054c4caae492873f0a5f20a1ea566ebf9dea3c1  .codex/config.toml
485a26c7409e16c692ad10095031ab0e7084726ec5da5666082b3bbc4a5daf98  .codex/agents/prover.toml
8b418f8ed02606205ecdfedcf5da72dae074e1c799237b8cc034fdfbd71ab7a1  rules/agent-orchestration.md
3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69  rules/research-lab.md
e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1  rules/design-authority.md
4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9  rules/compiler-engineering.md
2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6  rules/git-concurrency.md
a0a114b589e8920af8e8fd871d15f63d68b735fc1a553f5a89952b1eab8489e5  rules/orchestration-budget.md
```

Repair freeze checks: all 25 recorded hashes still authenticate their pinned
historical inputs; the other 24 dependencies also match current contents.
All 6 local links resolve; fences and trailing whitespace pass.
The separately corrected original-profile dependency at repair freeze has SHA-256
`0aab6ee4d9206f93bc70498a41560c54590647000976ebfc6780cebee32619f6`; this is the reviewed dependency delta,
not a replacement for its historical baseline hash above. No tests/builds/probes ran.
