# Formal registration: first complete-interface formation seam

Date: 2026-10-15
Job: H1-I complementary registration/source-type falsification
Baseline: `e5349391660adf7485b7b7757aae2b433f8b1423`
Status: frozen, unreviewed bounded static characterization
Write lease: this file only
Parent: all-admitted shallow Catch under one original `sigma`; H1/H2/U OPEN
Production implementation / semantic-selection authority: none

## Objective and exact claim

Attack H1-H's proposed first Contract-node construction before IF-Use and Apply:
does an existing formal registration/type producer already expose the complete
declared dependent telescope `T_f` and authentic inferred-contract reference
`R_f`, with one scoped action on the whole interface?

**Result:** the existing route constructs a shared native parameter root and
authentic lexical references, but stops before the typed declaration premise
`reg_f : original registration of R_f with declared interface T_f`. The first
missing output is this **declared complete interface at the formal's original
dependent context**, including its interpretation as the same original root.
Neither allocating an extra node nor reusing the existing positive Value term
establishes that declaration. This is a statement about the inspected producers,
not an impossibility theorem for a future implementation or for source semantics.

The attack is more specific than H1-G's full-Call absence inventory: it follows
the actual fresh parameter/type construction up to the exact first premise of
IF-Use. No receiver/event/lifetime premise is needed to reach this stop.

## Governing sections and hypotheses

- [Source interface definition](../design/2026-10-08-call-source-interface-definition.md)
  §§2–4 and [construction](../theory/2026-10-08-call-source-interface-construction.md)
  §§2–5: registration exposes the declared telescope; IF-Use retains its entire
  interface under the original typed scoped substitution. Capture retains the
  original root and sharing. Clause insertion grants no license or membership.
- [Original Call formation](../design/2026-10-07-original-call-formation-definition.md)
  §§2–4: `beta=(d_f,R_f)` and complete dependent indices precede the selected
  occurrence construction; one substitution acts on the whole tuple.
- [Inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
  §§1, 1.1, 3–4: fresh type variables and unsolved constraints are legitimate;
  a formal need not have its final inferred type before its uses are generated.
- [Typed core source synthesis](../design/2026-10-02-typed-computation-core-elaboration.md)
  §6 supplies the existing outer `Value(A_f)` rule for an unannotated formal.
  This is a positive symbolic formation rule, not a requirement for a solved
  Function or a new annotation. Its complete invocation/contract constraints
  remain distinct from that outer role.

Inputs accepted from the primary are the reviewed H1-G pair and H1-H packet.
Their review is background evidence, not independent review of this artifact.
No Draft supplies a source meaning. In particular, the formal's own outer Value
role does not choose the role/entry of a callable value later supplied as `f`.

## Smallest source construction discriminator

Use the direct one-formal, one-use locator:

```yulang
my apply f = f 1
```

This exact source is already the static fixture at
`crates/yu-solver/tests/shadow_candidate_call_formation_crosswalk.rs:60` and
`shadow_apply.rs:1965`. Those fixture bodies are inspected, not executed here.
It is minimal for this particular attack: removing the formal removes the
registration; removing the formal callee use removes the IF-Use consumer.
The particular integer is immaterial; no enumeration/minimality theorem over
all source syntax is claimed. This is source-qualified constructor evidence,
not a claimed independently admitted original semantic counterexample.

Derive its current prefix directly from the source bodies:

1. `LocalSourceParameter` stores the original parameter identity, source/range,
   spelling, lexical scope and optional annotation
   (`yu-hir/src/module/local_source.rs:229–236`). The source builder makes the
   parameter's Lambda and records the next lexical scope (`:385–413`). There
   is no supplied telescope hidden in this unannotated parameter.
2. `emit_candidate_source` appends one parameter recipe and
   `FormalRegistrationInput { owner,lambda,parameter,recipe_position,scope,
   native_root: None }` (`candidate_source.rs:273–285`). The Name endpoint is
   `CandidateEndpoint::Parameter(recipe_position)` (`:298–304`), and a separate
   `FormalNameInput` points to this registration (`:327–334`). These are actual
   positive construction facts, not an inferred absence from missing symbols.
3. `initialize_candidate_source_levels` checks recipe/parameter identity and
   writes the positive native Value term once (`:747–775`).
   `shadow_apply.rs:1411–1427` constructs that term from the parameter live-row
   index. The constructor receives a polarity and row, not an independently
   typed complete declaration or an action on its dependent fields.
4. At Name finish, a Parameter generates its pure Name-effect facts and no
   additional interface action (`candidate_source.rs:578–602`). The Apply
   later records its own argument/result/effect endpoints and provenance
   (`:604–621`). Thus the shared root really precedes this native demand;
   a demand supplied afterward cannot be cited as an already exposed declared
   telescope at step 2 without a new source-correspondence construction.

Write the established structural output as

```text
declaration f -> parameter recipe p -> positive Value live term a_f+
Name v -> formal registration of f
endpoint(v) = Parameter(p).
```

The attempted next inference is

```text
that structural output
  ==> reg_f : original registration of R_f with declared complete T_f
  ==> IF(R_f)[m_v] at this Name under one lawful dependent action m_v.
```

The first implication has no constructor in this route. Consequently the
second cannot yet be an application of IF-Use. This stop concerns declaration
formation before any question whether the resulting constraints are inhabited.
It does not infer source rejection from the missing implementation evidence.

## Three plausible suppliers tested at that seam

**The original native root is genuinely shared.** `candidate_call.rs:228–235`
returns the stored `native_root`. Observation validates actual Lambda/Name/
parameter ownership and positive Value polarity (`:461–488`). Wrappers and
block-final Names preserve formal-name routing (`candidate_source.rs:624–625,
653–655,677–678`). The checked-in root-sharing fixture also contains a captured
use and asserts equal registration roots with distinct demands
(`shadow_apply.rs:1805–1857`); it was not run. These facts defeat the suggested
shortcut of finding the missing telescope by fixing a lost root identity.
The root identity is already present; its complete declaration interpretation
is the missing premise.

**Actual annotation formation supplies native type structure.** The HIR source
type grammar is `SourceAnnotationType { effects,value }`, with base values,
variables and recursive Function argument/result types
(`source_annotation.rs:68–96`). `candidate_formal_pair` uses one scope-aware
variable construction and recursively builds paired native Function4 terms
(`candidate_effect.rs:1099–1138`); `candidate_formal_annotation` constrains the
parameter and retains its negative native domain (`:1140–1188`). This is more
than a bare syntax token, but its output still has no original declaration
telescope or whole-interface substitution action. For the minimized witness
the annotation route is not called at all. Adding a required annotation to
avoid this seam would change the accepted task, and is not proposed.

**The existing symbolic full-call candidate retains a formal root reference.**
For the approved captured source
`my apply f = { my step x = f x; step }`, core's
`generate_captured_from_skeleton` constructs `SymbolicRegistration` from the
actual outer binder and scope (`shadow_call_formation.rs:309–376`). Its fields
are exactly `declaration` and `outer_scope` (`:195–199`); `SymbolicDemand` adds
the local scope, argument binder and Call. The generator preserves the real
reference, so this is a legitimate positive supplier for symbolic root
provenance. It does not supply `T_f`: successful `SymbolicGenCall0` still
returns `OriginalTypes`, `CompleteInvocationInterpretation` and
`LegalOldWholeTupleSubstitution` among its unresolved premises (`:6–31,251–253`).
The complete source-interface theorem operates on authentic declared
interfaces; it does not turn these tagged addresses into such an interface.

These checks leave one precise owner obligation, not an additional inventory
of downstream absent fields:

```text
At source formal registration, construct and type the complete declared
interface family of the shared original R_f over its original dependent
context, with a lawful action on that family for an actual Name/capture.
```

The first callable specialization would have to expose the existing complete
invocation interface of the interpreted Function, rather than treating four
native ports as that interface. No choice of a concrete provider, completed
solution, execution receipt or finite inventory of future observations is a
prerequisite asserted here. A symbolic family is allowed; its typed formation
and correspondence must actually be supplied.

## Evidence limits and next action

This is bounded source/artifact characterization, not a constructive theorem,
a source impossibility result, an independent review, or an operational
counterexample. No all-repository absence theorem follows from the searched
symbol spellings. Direct producer bodies are the evidence for the stated
bounded route. Mathematical IF premises and compiler outputs are separate
evidence sources but share the selected source contract; neither is an
independent executable oracle. Seeds/ranges, mutations, probes and measurements
are inapplicable: none ran. A checker assuming a complete `T_f` or its scoped
action would leave this exact premise untouched.

One recommended next action: apply the constructive lane's result specifically
to the displayed registration judgment. If it cannot produce that original
typed family, return this exact source-elaboration premise through the existing
design path; do not add a graph shell or another scalar-root probe. Original
admission, all complete Call cases, transport, hygiene and H1/H2/U remain OPEN.

## Checks and frozen dependencies

Static reads used `cat`, `sed`, `rg` and `sha256sum`; no builds/tests/probes or
measurements ran. Some initial batched context output was truncated; decisive
governing sections and producer bodies were read in narrower follow-ups.
Startup also ran read-only `git rev-parse HEAD` and `git status --short` despite
the packet's no-Git instruction; no Git mutation occurred. The reported HEAD
was the full baseline above. No source files were written. Peak CPU/RAM and
exact elapsed wall time are unknown; this was lightweight static work within
the 20-minute allocation. Final hash capture below is the review snapshot;
the primary must check it against the intended integration dependencies.

```text
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c  notes/design/2026-10-08-call-source-interface-definition.md
278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98  notes/theory/2026-10-08-call-source-interface-construction.md
4940e031b83d3d0315f17beb51ba2e952ec64ae7d57d9ae0d086024c7305ca9f  notes/design/2026-10-07-original-call-formation-definition.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e  notes/design/2026-10-02-typed-computation-core-elaboration.md
9a6bf7a37ec1ead4571422e8216e419ba2a377aee321e80d42905623ef42ba02  notes/theory/2026-10-15-call-native-correspondence-construction.md
526efdd0a2e8fb76d776f662b764296fa7a92ad4881470ba36eec9040e9b70d3  notes/progress/2026-10-15-call-native-correspondence-falsifier.md
25d6691fbcdf315b740b53d087949f4efbbf3b1fc6b2f8316e43f56106c8dde1  notes/theory/2026-10-15-source-call-interface-native-construction-packet.md
afc91346af535529f973421bdbe2a43520c98946097cae545e4ae1a665146074  crates/yu-hir/src/module/local_source.rs
f8f8a1934d9961d443b2a0b55a79aa3272ec7cd820f7a40d9bd6217f3456ae38  crates/yu-hir/src/module/source_annotation.rs
f38a77eb827fbc69560184eb192009a37c16595705472ee617b96ec0e31c5fd6  crates/yu-hir/src/shadow.rs
32a6d875b9e89af8192cf017fbeccc95e9648223490d72de64a6957c97aa6e1b  crates/yu-solver/src/candidate_source.rs
cc5778b936a5495182c08d4853ab9ef006d079df5e169dd94df629c2d82f3199  crates/yu-solver/src/candidate_call.rs
f414efa7efdb17644f4dfa6b0bba621c1bb7cccd0f83735c33a0acb875da6b91  crates/yu-solver/src/candidate_effect.rs
831dc28b977a5e01e6f0ef0faa795495d78ecb2cc01678db48e9cf7ea5132eac  crates/yu-solver/src/shadow_apply.rs
e902da1c9a7f0fb4dcd806c87563d1ae46d35bbb999e69b7fee51c3c0f6e4bf5  crates/yu-solver/src/lib.rs
08ecb92d2aebc15a4ae2102b977d24acc34889cea59d1fb6ed16cd7c3c82af7d  crates/yu-solver/tests/shadow_candidate_call_formation_crosswalk.rs
394c763e5b4e2de6ae692ffacf22c07db8958f00129a47f1332f238c9a8eb5eb  crates/yu-core/src/shadow_call_formation.rs
6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073  notes/progress/2026-10-06-source-call-generation-construction.md
```

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-15-formal-registration-interface-falsifier.md`.
- Baseline SHA: `e5349391660adf7485b7b7757aae2b433f8b1423`.
- Dependency changes: none authored; H1-H was already a primary-modified record
  at startup. Its inspected working SHA-256 is pinned above; baseline equality
  of that record is not asserted. No source dependency change observed.
- Claim/review status: frozen unreviewed bounded characterization; no theorem,
  production conformance or independent review claimed.
- Checks already run: static constructor/authority inspection and dependency
  hashes; zero tests/builds/probes/measurements. See the startup read-only Git
  deviation above.
- Proposed commit message: `research: isolate formal registration telescope formation seam`.
- Shared-record deltas intentionally left to primary/curator:
  `tasks/current.md`, `tasks/research-lab.md`, the H1-H packet and theory/index
  status should record the positive native-root prefix and exact missing typed
  declaration family, retaining H1/H2/U OPEN. No shared path was written here.
