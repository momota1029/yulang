# Direct mu_result kernel: proof recognition and same-prefix decision

Date: 2026-10-08
Baseline: `d69474d7286717d53aa7ede30ef2d3153a839040`
Status: unreviewed research; frozen on submission
Gate/method: JOINT_DEC; inversion of the actual native result-check slot
Exclusive lease: this file only
Semantic/design/implementation authority: none

## Objective and result

Determine whether checking and transporting a submitted finite
`mu_result: J.payload -> A` certificate supplies complete effective input
reflection and negative decisions at the original prefix. No fully specified
search algorithm was supplied in this assignment. The attack therefore targets
that proposed implication, rather than attributing an algorithm to the source.

**Result class: bounded source characterization and conditional obstruction.**
The selected rules give a sound action on a supplied, genuinely typed proof.
They expressly supply neither extensional completeness of their proof grammar
nor a terminating decision procedure for its inhabitation. A direct kernel can
avoid challenge classification by manipulating proofs parametrically, but it
still owes same-prefix joint synthesis and justified terminating negatives.
No counterexample to a complete direct algorithm, actual failing Yulang
program, or Yulang undecidability theorem is established.

There is one minimal source-rule discriminator: a rejected submitted identity
proof can coexist with a lawful Top/Any proof at the same result-check slot.
It refutes only the shortcut that turns rejection of that submitted term into
a negative admission answer. It is not a refutation of proof search.

## Governing sections and fixed meanings

- [Uniform value entry](../theory/2026-10-08-uniform-value-entry-constructor.md)
  §§4.2–4.3: complete independently typed J, original hereditary same-value
  `mu_result`, mandatory whole Delta proof and original observation domains;
  §5.2: exact checked-frame injection and no replacement of a failing frame's
  prechosen A; Joint-ID in §6: all non-definitional checking choices remain
  in the given shared strategy.
- [Source Generalize proof](../theory/2026-10-08-source-generalize-definition-and-proof.md)
  §3.2: independent finite checking constructors, complete Function inclusions
  as proof conclusions, and the explicit absence of a claim that all true
  inclusions are derivable; §7.1 supplies the concrete lawful `Int <= Any`
  checking example. Its §1 separates proof-directed source completeness from
  effective solving of open predicates.
- [Native certificate constructors](../theory/2026-10-08-native-projection-certificate-constructors.md)
  §§2.1,3: full retained evidence, independent registry L and local laws,
  explicit proof alternatives/intermediates, open catalogue parameter, and
  no assertion that all true extensional inclusions have finite proofs.
- [Canonical JOINT-DEC](../theory/successor-proof-obligations.md#joint-dec):
  every original active predicate, exact admitted source envelope,
  preservation/reflection and simultaneous original-witness completeness.
- Prior [direct route](2026-10-08-direct-effective-residual-route.md),
  “Candidate and exact obligations,” and
  [source-route falsification](2026-10-08-direct-residual-route-falsification.md)
  §§1–4: supplied-witness action, original-prefix reflection and totality
  remain separate. Their equality, Identity/Compose size and constrained-q
  examples are not repeated here.
- [Source observer inventory](2026-10-08-joint-observer-source-inventory.md),
  “Inventory and telescope”: the actual admission condition is result
  inclusion, not a newly emitted fixed-ground equality.

Rules/research-lab, design-authority, git-concurrency and compiler-engineering
were read in full. Accepted independent admission, complete Option 2 arms,
other-program/future contexts, fixed original `xi=(nu,K,D)`, original binder
order and caller-owned initial JointWF remain unchanged. Their authority is
the primary's accepted baseline; no question bundle is reinterpreted here.

## 1. Invert the actual source-owned slot

At the original typed result incidence, write

```text
Der_L(B,A;tau) = the genuine finite local same-value proof objects
                from B to A at the original full telescope tau.
B = the independently supplied J.payload.
```

This is notation for the existing checking judgment, not a new emitted atom,
new binder, inclusion oracle or chosen meaning. Its objects retain all local
laws, raw/decorated value, provider, world, source consumer, restrictions,
proof choices and intermediate evidence required by §3.2 and L. When B or A
is Function-shaped, its original complete domain/observation obligations
remain inside this judgment. Scalar endpoint reachability cannot discharge
them. When an actual conversion is required, it belongs to its independently
selected conversion constructor; it is not a same-value mu_result.

Uniform entry §4.2 requires an object of this judgment as one field of gamma.
It separately requires J's formation/Car evidence, original_port_map,
delta_static, whole delta_check and current_guards. Consequently an algorithm
for this one judgment is a local subkernel, not already a solver for gamma or
the whole original residual. Bare-id's concrete Delta projection proof does
not construct every independently supplied input field.

Given a typed d in Der_L(B,A;tau), the independent local interpretation gives
the same-value hereditary action on B evidence. At Return, apply d to the
same decorated J result and obtain A evidence. At a pending/divergent prefix
there is no completed result to invent. The selected inlet/body action
preserves all original fields and later restrictions. This is the existing
conditional certificate transport, with an effective implementation still
requiring faithful finite codes and effective eliminators for its inputs.

Neither transport nor `PackGeneric` supplies d. In §5.2 the injection uses
the checked frame's already supplied gamma and prechosen A. It cannot search
the raw sum for another presentation that makes the original frame succeed.

## 2. Minimal rejection discriminator

Fix a genuine independently formed frame with prechosen A=Any and a genuine
typed argument contract J whose payload is Int. Assume the actual complete
Car, world, incidence and other checked-inlet fields at their original scopes;
these are hypotheses, not constructed by this note. Bare-id's selected Delta
schema adds no operation bound. No observation is restricted to actual runs.

At the distinguished result-check slot compare the two finite proof terms:

```text
submitted d_bad  = Identity(Int)   : Int -> Int
available d_good = Top/Any(Int)    : Int -> Any
required slot                    : J.payload=Int -> A=Any
```

Identity's exact endpoint rule does not type d_bad at that slot. The genuine
Top/Any rule does type d_good, retaining the same value/provider and required
guards. Source checking §3.2 lists both rules; §7.1 explicitly demonstrates
lawful Int-to-Any checking. These are two single-rule terms. There is no
composition, new effect predicate, conversion or changed earlier endpoint.

Thus rejection of d_bad does not entail that the required proof slot is
uninhabited. With the remaining gamma fields genuinely supplied, replacing
the submitted ill-typed term by d_good repairs that slot at the *same* prefix.
A checker that inserts Top/Any after rejection has begun constructing a
different proof; it must justify that construction rather than regard the
rejected term as a negative certificate.

This witness is shaped by actual native inlet and source checking rules. It
does not assert that F5 emits either term, that surface syntax exposes gamma,
or that an ordinary source compiler submits an ill-typed identity proof.
The earlier source §7.1 example is an outward check; its genuine local
Int-to-Any rule is reusable in the mu_result slot by §4.2's selected grammar,
without identifying the two checking occurrences. The witness falsifies
only `reject(d) => no lawful mu_result`, not a complete enumerator or solver.

## 3. Exact unsupported premise

There are two possible completeness claims, and neither follows from finite
proof recognition.

**Proof-directed local decision.** For the exact actual input catalogue L
and telescope tau, terminate with a lawful d when Der_L(B,A;tau) is inhabited,
and terminate with an independently justified negative when it is empty.
If one additionally assumes effectively enumerable finite terms and decidable
rule checking, fair enumeration can find an inhabitant. Those extra assumptions
are not established for every open authentic catalogue here, and enumeration
alone gives no terminating negative result or sufficient search bound.

**Semantic inclusion decision.** If the proposed kernel instead decides the
original complete semantic inclusion, it also needs a proof that every
required true inclusion has a representable lawful derivation or other
effective certificate. The two cited source sections explicitly decline this
extensional-completeness claim. Absence of a proof in a currently selected
grammar cannot by itself justify rejection of an otherwise supported program.
The exact supported observable contract determines the required completeness
domain; this note does not replace it by today's proof grammar.

For JOINT_DEC, even local decision must be lifted to the *whole* original
residual. Let p be any lawful fixed earlier prefix and R_p that residual
with its original remaining Boolean/binder tree. The necessary constructive
claim is:

```text
If R_p has a lawful joint strategy extending p, construct an effective,
faithfully interpreted joint strategy extending that same p;
otherwise return a terminating, sound negative for that same R_p.
```

Every mu_result choice may depend only on its original permitted preceding
operands. If its owning choice is ViewLogic before a challenge, it cannot be
selected after inspecting that challenge; an EventProof choice stays at its
actual event. All universals still range over the independently admitted
complete J/context/response/raw/future domains. Shared proof/client fields
remain joined, and all alternatives observed by the original relation or W
remain retained. This formula does not move any source binder or require
encoding every individual semantic challenge: a uniform interpreted symbolic
action is permitted when its interpretation is actually established.

Joint-ID's input is already one such shared strategy, including nondefinitional
mu_result choices. Its transport theorem therefore does not prove the
antecedent, construct the input strategy, or decide its absence. A checked
individual proof supplies no law saying independently found local witnesses
can satisfy every other actual shared predicate together.

Under proof-obligation economy, sound same-prefix interpretation is A and
complete inference on the required actual source envelope is B. Encoding all
arbitrary extensional strategies is a different, potentially stronger C
claim. Retaining a genuinely known source proof can avoid D reconstruction,
but cannot certify the absence of every lawful proof for a new open check.
The prior two routes leave this premise untouched. Another checker sharing
L's assumed rules would not close it; this lane stops at this exact cut.

## Evidence, omissions and recommended next action

Documentary derivation only; no executable oracle, seeds/ranges, mutation run,
enumeration, tests, builds, formatter or semantic probes. The sole logical
mutation considered is treating one proof-term rejection as residual falsity.
It fails on the two-rule discriminator above. There is no claimed coverage
outside those supplied source laws and that slot. Independent ground truth
is the genuine source checking/registry interpretation, independent of tested
id membership or Direct success; a checker assuming it does not prove it.

Failure conditions include false Top/Any local laws, wrong original incidence,
missing full carrier/world evidence, changing A/J/provider, incomplete Function
or J arms, illegal proof dependency, erased observed proof fields, an
undecidable/unrepresented local operation, or missing negative termination.
Unverified: exhaustive actual-emitter inventory, full catalogue effectiveness,
global semantic inclusion completeness, whole joint search, production
correspondence, resource policy, principality and F5 cutover. No semantic
impossibility or gate closure follows.

Commands used: bounded cat/sed/rg reads, sha256sum snapshot/recheck, output-path
absence check and final leased-note integrity checks. An initial read-only
`git rev-parse HEAD` was run despite the packet's no-Git restriction; no Git
mutation occurred and no further Git command was used. The initial task-file
capture was truncated; only narrowly reread relevant clauses support this note.
No exhaustive repository or catalogue search was performed.

Resource use: lightweight sequential shell reads and one leased note write;
zero test/build/probe processes. No numeric CPU/RAM/wall-time budget was given.
Total CPU, peak RSS and wall time were not instrumented and are unknown.

**Recommended next action:** specify one finite actual mu_result input class
and its authentic L owner, then derive a terminating synthesis/negative law
for that exact class at the unchanged telescope. Start with genuine structural
checking to discriminate certificate recognition from complete proof search;
retain complete Function and unknown primitive cases as explicit open scope.
This is a research recommendation, not a selected restriction or implementation
authorization.

## Frozen dependency snapshot and commit packet

Direct dependency hashes at initial and final inspection were unchanged:

```text
5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6 rules/research-lab.md
925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5 rules/design-authority.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e rules/git-concurrency.md
1ff144d376052d2e01d2e97ba3290e6942f126765067fbf11dfeffc06f89b442 rules/compiler-engineering.md
273e8dae447e9997d586fc07abf48883c76b90988c8906094dd428a48339c2e5 notes/theory/2026-10-08-uniform-value-entry-constructor.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 notes/theory/2026-10-08-source-generalize-definition-and-proof.md
04c5699dfaaf5f98ee9db54df5bd124f25e7131abb6bc3104e1675a5490f74a8 notes/theory/2026-10-08-native-projection-certificate-constructors.md
59442db205d0bc381de74a373f1d58a753e3366ae0ba845e8c9c877465e738fc notes/theory/successor-proof-obligations.md
86ac0dba2946bab46c1c27a160f54e10cc95da8ce5de1d91f74a0957cb8c43eb notes/progress/2026-10-08-direct-effective-residual-route.md
cee3b1884d2e1014709d72ed5ed69f46dd64b89dd48ac481672308d6cf20eb30 notes/progress/2026-10-08-direct-residual-route-falsification.md
11bf4ba93fa1a3211a704c595b73a67b2b62277b7ba7aa0032967ed3405cf340 notes/progress/2026-10-08-joint-observer-source-inventory.md
```

- Exact leased/changed path:
  `notes/progress/2026-10-08-direct-mu-result-kernel-falsification.md`.
- Baseline SHA: `d69474d7286717d53aa7ede30ef2d3153a839040`.
- Changed dependency hashes: none observed during assignment; primary must
  verify pinned-commit equality and any subsequent branch/dependency movement.
- Review status: unreviewed bounded characterization/conditional obstruction;
  producer claims no independent review. Frozen on submission.
- Checks already run: governing-section reads, dependency SHA-256 recheck,
  leased-path/link/whitespace/final-newline integrity. No executable semantic
  checks, compiler tests or builds.
- Proposed checkpoint message:
  `research: isolate mu-result recognition from same-prefix joint decision`.
- Shared-record deltas intentionally left to primary/curator: optionally link
  this local kernel cut under JOINT_DEC; retain OPEN-PROOF, original domains,
  predicates, dependencies, proof alternatives and production prohibition.
  No shared task/index/authority/code/manifest/lockfile/question file changed.
