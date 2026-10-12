# Exact nested g: unresolved source proof, corrected evidence, and rejected completion claims

Date: 2026-10-12 UTC; filename follows the 2026-10-13 parent research series.
Status: independently reviewed investigation report and conditional structural lemma.
Parent goal: **NOT SOLVED**. No source preservation/principality theorem,
source-qualified counterexample, or semantic-independence theorem is claimed.
Compiler changes and new semantic/publication/source restrictions: none.

## 1. Outcome and what this report is for

The current request demands a direct construction of the exact nested g's
source publication and independent-use obligations, or a genuine refutation
or verified insufficiency result. This investigation has not met that demand.

It would be misleading to turn the following findings into a completed
source theorem:

- Native freshening retains one low-level C between the two g uses.
- A finite native relation with supplied use-image equalities is inconsistent.
- An extracted partial rule calculus cannot create a registration tuple that
  was explicitly excluded from all its input leaves.
- A new, empty correspondence predicate satisfies a soundness-only implication.
- The structural recursive computation has no finite Return derivation.

The first two have useful, reviewed native evidence. The third and fourth
were **rejected as solutions of the user's task by fresh independent review**.
The fifth has the conditional structural proof in §6; it does not construct
complete semantic typing or admission. This report preserves these distinctions
and the concrete corrections, rather than adding another equivalent
registration-frontier theorem.

A missing implementation payload, an unconstructed proof instance, a missing
formal premise specification, and logical independence of the selected
semantics are four different conclusions. Only the first three were observed
in the bounded senses stated here. **Logical independence was not proved.**
No new choice is requested or adopted on the basis of this investigation.

## 2. Exact source and frozen evidence

The requested source, with all binders and the written annotation retained, is:

~~~yulang
my answer = {
  my f x = {
    my g y = { my drop z = y; drop (f y) };
    my first: int = g 0;
    g ()
  };
  f
}
~~~

The multiline witness with a final LF has 116 bytes and SHA-256
bffcb9619342e28de83b54ff39871ccfe5be55f1791814f652af91d2dcebeaa2.
The companion native note additionally locates syntax in its explicitly
identified 97-byte single-line whitespace variant. No parser execution in
this investigation establishes a new correspondence between these variants.

Initial remote HEAD was 38bda20257d58069097a3e42c358b6759fb26d58.
Before the native checkpoint, remote HEAD advanced through f8166d3 to
beceb0bc91b35e84b4f62b353fc6c2abf18e0414. GitHub's full comparison showed only
tasks/current.md and tasks/research-lab.md changed. Every mathematical and
compiler input of this investigation therefore remained byte-identical.
The reviewed native note and checker were saved at
[0bae7392c350e0d66244aaf8ea2a502ff1d2aa78](https://github.com/momota1029/yulang/commit/0bae7392c350e0d66244aaf8ea2a502ff1d2aa78).
This report is integrated in a subsequent records-only commit; the native
checkpoint above remains an immutable evidence reference. No branch was force-pushed.

The first four notes read in full were:

1. [Active-root Call source construction](../theory/2026-10-13-active-root-call-source-construction.md).
2. [Nested live-root Generalize derivation](../theory/2026-10-13-nested-live-root-generalization-derivation.md).
3. [Intrusion source preservation](../theory/2026-10-13-intrusion-source-preservation-proof.md).
4. [Source publication classification](../theory/2026-10-12-source-publication-classification-proof.md).

Direct selected sources, not just those summaries, were then read:

| Abbreviation | Original source and decisive scope |
| --- | --- |
| SG | [Source Generalize construction](../theory/2026-10-08-source-generalize-definition-and-proof.md), selected by [its definition](../design/2026-10-08-source-generalize-definition.md); §§3.1–3.3, 4, 5.1–5.3, with genuine L1–L5 still required |
| CI | [Call input construction](../theory/2026-10-07-call-input-construction-proof.md), §3 actual Name/capture/Parameter/Code-Call premises |
| IF | [Call source interface construction](../theory/2026-10-08-call-source-interface-construction.md), §§3–6 actual clause insertion, reference maps, complete frames and finite cycles |
| CC | [Captured closure introduction](../theory/2026-10-08-captured-call-closure-introduction.md), §§3–5 selected by [captured closure definition](../design/2026-10-08-captured-closure-constructor-definition.md); §6 for the conditional Step proof |
| PHI | [Simultaneous immutable introduction](../theory/2026-10-08-simultaneous-immutable-root-introduction.md), §3 actual positive value/world/carrier/observation readouts |
| V | [Parent/copy operation](../design/2026-10-10-parent-copy-scc-intrusion.md), [event association](../design/2026-10-12-intrusion-value-type-association.md), and [copied-row ownership](../design/2026-10-12-value-reference-copied-row-ownership.md) |
| LSR | [Local self-recursive binding](../design/2026-10-10-local-self-recursive-binding.md) |
| SS | [Original Typer.scala](https://github.com/LPTK/simple-sub/blob/9bae772624c23b52a93c1b226157e16898b4d9db/shared/src/main/scala/simplesub/Typer.scala), reference commit 9bae772624c23b52a93c1b226157e16898b4d9db |

The source-signature incidence construction and its selected definition,
complete same-value bound accumulation, pure-read Call construction,
contextual Function membership, native pair, nested-block interpretation,
and exact-source/native correspondence notes were also checked. None was
treated as an all-source theorem merely because it had a reviewed header.

## 3. Status of the five requested obligations

| Requested obligation | Established in this investigation | Not established |
| --- | --- | --- |
| Actual K_g, typed f edge, y declaration and scope | Exact lexical ownership; y's description precedes g's challenge by Parameter; generic runtime external Mono capture is potentially applicable | The actual component/member relation, complete capture substitution, and original full dependency telescope Delta_y |
| Actual f y demand, pairs and approved equality | Reviewed native formation/incidence; actual pairs in the declared finite scalar analogue; normative source Value graph F -> G -> F | Full current Rust settlement/effect-pair trace, selected event readiness, and a complete source interpretation of the equality |
| Complete Call/checking program | The exact source constructors and complete input fields required by CI/IF were inverted; no literal native-event tag is a necessary source field | An authentic complete Application/Q_c instance and a lawful correspondence of its whole scoped fields with this generated native relation |
| Generalize(g), then independent g 0 and g () | Actual native maps in the declared analogue; current capture/fresh-use consumer rules; source allocation rules once supplied authentic input | Actual source fixed/template classification and allocation maps for this exact N_g |
| Typing and required principality | Conditional finite native inconsistency and conditional structural nonreturn lemma | A source typing witness, preserved principal coverage, a source-qualified counterexample, or two complete semantic models proving independence |

This table is a status report, not a claimed insufficiency theorem. The
original source preservation, required principality, complete Call, effects,
progress, termination and production gates remain open.

## 4. Concrete native and source-incidence corrections

### 4.1 The exact absolute target is 2

The current candidate starts answer's RHS at level 1 and raises the level
for each block-local initializer. It preserves level through Lambda, Apply
and Group. The source owner is candidate_source.rs:245–328,527–555.

| Site | Absolute inference level | Publication boundary when applicable |
| --- | --- | --- |
| answer RHS / final f Name | 1 | answer: 0 |
| f initializer and x | 2 | f: 1 |
| g initializer and y | 3 | g: 2 |
| drop initializer and z | 4 | drop: 3 |
| first initializer / g 0 | 3 | first: 2 |
| final g () | 2 | — |

Thus the concrete scalar demand crossing to f has pairs
(C,B,+,2) and (D,R,-,2). The requested target-1 notation is valid as an
explicit relative convention on the f subtree, subtracting one. It is not
the compiler's absolute target for this whole source. Normalization does
not remove drop, first, or either publication boundary.

This is also not an equality between a numeric level and a source telescope.
In the current Rust route the actual receiving level and canonical parent
when the comparison is reached still matter.

### 4.2 The named drop and both independent maps matter

Under the explicitly declared scalar reference analogue:

~~~text
drop publication:  Poly(3, Function(Z@4,B@3))
drop use:         Z@4 -> Z*@3; B@3 -> same B@3

f y:              o <: Function(B,R)
extrusion:        B <: C; D <: R; o <: Function(C,D)
drop application: R <: Z*; B <: S

g publication:   Poly(2, Function(B,S))
first g Name:    B -> B0@3; S -> S0@3; C@2 -> same C
second g Name:   B -> B1@2; S -> S1@2; C@2 -> same C
~~~

The ordinary use relation includes:

~~~text
int  <: B0 <: S0 <: V0 <: int
unit <: B1 <: S1 <: V1
B0 <: C; B1 <: C
D <: R <: Z*
~~~

Adding the **supplied use-image equalities** C=B0 and C=B1 gives the finite
derivation unit <: B1 = C = B0 <: S0 <: V0 <: int. The primitive comparison
rule rejects unit <: int. D=R alone remains consistent in the checked finite
relation.

The checker does not derive these use-image equalities from the initial
equality C=B. That transport is precisely not certified. It extends the
finished native store; it chooses no pre-Generalize or later activation
schedule. This is a conditional finite result, not the requested source
counterexample.

C is shared at this g-use cut, not a forever-fixed global variable.
Final ordinary Name f freshens o, A, V1, D and C to level 1 in the finite
analogue. A source account must preserve the enclosing-instance distinction
rather than call C globally fixed.

### 4.3 Actual facades and Value ownership

Current argument Name y selects the parameter endpoint B. Copy creation
records its canonical representative, rep(B). The active callee Name has a
distinct facade N_f with L_f <: N_f. Group around f y has another facade J
with R <: J, which is the actual drop argument. Current Function comparison
has four value/effect ports and can produce additional effect-parent pairs.
These facts come from candidate_source.rs:220–226,375–443,
shadow_apply.rs:1291–1405, candidate_extrusion.rs:89–126,224–256 and
lib.rs:12411–12536.

Under the approved definition-root ownership, the graph is:

| Owning root | Reference edges relevant here |
| --- | --- |
| answer | F, through final f |
| F | G, through final g () |
| First | G, through its own initializer g 0 |
| G | F through f y, Drop through drop, and y through its argument Name |
| Drop | y, through its captured result Name |

The g 0 reference belongs to First, not to F's owned initializer/body
fragment. Nevertheless F -> G -> F holds, so the full approved Value graph
qualifies a genuine G/F event with its actual produced pairs. It determines
neither validating K_g nor event readiness before a particular publication.
The current intrusion consumer still uses type/effect rows and bounds;
that is an implementation observation, not the selected Value graph.

The complete finite native derivation, source locations, effects/facade
limitations, dependency hashes and reproducible checker are in
[the reviewed native evidence](2026-10-13-exact-g-native-source-evidence.md)
and [the research checker](../../tools/research_exact_g_native.py).

## 5. Rejected attempts at proving specification insufficiency

### 5.1 Registration support was not a faithful no-derivation theorem

One attempt defined an open calculus with an owner tuple
O(p_g,g;K,N,edge_f,T_y). It excluded every input containing that tuple and
proved by constructor induction that Name, capture, IF, Build, publication
and allocation could not originate it.

That narrowly stipulated induction does not resolve the source task. The
earlier publication-classification note §8 already asked for the same tuple:

~~~text
Reg_g(h) =
  (p_g(h), K_g(h), N_g(h), R_g(h), edge_f(h),
   Desc(K_g(h),q_y,Value,sigma_y(h),Delta_y(h))).
~~~

More decisively, SG §3.3:219–235 calls these records **outputs** of the
indicated source rules. SG §4:364–387 defines Build by source recursion.
SG §5.1:428–435 says definition/recursive-group registration supplies C.
The attempted inversion treated the registration producer's actual instance
as an input containing its output, without a printed generic premise
specification establishing that inversion. It therefore did not prove that
the extracted calculus exhausted the selected rules.

Reading registration as an implicit total producer is a genuine challenge
to that negative argument. It does not, by itself, calculate the actual
member relation or telescope. Neither reading was adopted here. The
unavailable formal producer application cannot be converted into a proof
that no authentic registration exists.

**Adjudication:** reject the claimed task resolution and any promotion to
logical insufficiency. Do not add another theory note merely renaming Reg_g.

### 5.2 Empty correspondence was not a semantic independence model

A second attempt observed that an empty new correspondence relation makes
a soundness-only implication vacuously true over a supplied base model.
This is mathematically true and useless for deciding this source unless
the existing semantics themselves have genuine, distinct models with the
required opposite outcomes. No such models were constructed.

A refinement tried to trace native-event provenance through q/Q_c/N_g as
though it were an existing literal field. IF's displayed clause grammar
retains source declarations, source constructor origins and whole scoped
references. It does not require the native extrusion event or signed pair
to be a literal subfield of the source clause. A legitimate external typed
witness could relate that source clause to the actual native event.

Consequently absence of that proposed native-origin field is not absence
of every possible lawful correspondence witness. Requiring that field
would introduce a stronger, unselected representation prerequisite.

**Adjudication:** reject semantic independence and the proposed origin-field
cut as solutions. Both scalar S/F assignments and an empty new predicate
remain insufficient. In particular the F scalar assignment that freshens C
already contradicts the actual native cutoff map.

### 5.3 Native inference chronology does not prohibit source Mono

At native g installation, inference is still traversing f's initializer.
At a genuine runtime publication p_g(h), an actual invocation h has entered
an already formed f closure. These are different events.

A genuine incoming outer frame j can supply Mono(j,Contract_j) to the
generic external-capture rule, fixing that entire installed contract.
The original recursive code edge can simultaneously retain its
Internal(K_f,f) provenance. SG §5.3:605–624 explicitly distinguishes
installed external instances from retained Internal edges.

Thus “f is not installed during inference, so a runtime external Mono
capture is impossible” is invalid. This removes an obstruction; it does
not construct the required capture substitution, component registration,
or source/native equation transport.

## 6. Changed method: positive construction and structural nonreturn

### 6.1 The positive construction attempt

Instead of excluding registration, the retry tried to apply it positively.
An authentic generic definition-registration application would provide
C_g and its actual relation. Parameter would then produce y's Desc and
original telescope, and the own returned closure would have its raw
OneShot fields plus its separate Internal interface edge.

The generic external Mono rule can consume the genuine outer j contract.
Local drop captures the actual rebound y and introduces z before its own
challenge. Those are real available schemas. Their application still needs
the actual owner outputs and complete operands; an opaque symbol C_g is
not a constructed member map or Delta_y.

The single-local self-recursion rule establishes sequential local binding
groups. Equating one such group with the complete validating-component
relation remains unproved. No singleton K_g or Value-SCC K_g was selected.

### 6.2 Conditional lemma: no finite structural f Return

**Scope and premises.** Fix the exact structural core translation of the
displayed source using the original ordinary Lambda, immutable same-root
Name/capture, ordered Bind, Call, and Value-entry equations. Assume actual
closure/capture identities and finite structural operation derivations at
those original constructors. This lemma does not establish those source
formation/admission inputs and does not quantify over independent W/Z
contractual alternatives.

Height below is measured in the expanded structural operation derivation
using the actual code, Force and Bind equations. A finite ME-Call source-base
certificate may instead take receiver observation o_U as an opaque input;
that certificate alone is not this expanded operation derivation and supplies
no subderivation-height argument.

**Claim.** There is no finite completed structural Return derivation of an
invocation of that f.

**Proof.** Suppose one exists, and choose an f Return derivation of minimum
finite height, across its actual invocation events and arguments.

Its Value entry and body must complete the sequential RHS of first before
reaching the final g () suffix. Therefore this derivation contains a
completed g 0 invocation. That g invocation forms its actual named drop
closure, capturing the same rebound y, and must complete drop (f y).

Drop has Value entry. Its designated Force must complete the whole delayed
f y computation before z is rebound and drop's body can Return y. Hence
the chosen f Return derivation contains a completed invocation of the same
captured f as a proper subderivation. Here y has been rebound from g 0;
the descent argument does not otherwise depend on the argument's value.

The proper subderivation has smaller finite height, contradicting the
chosen minimum. This uses the named drop, its actual entry Force and the
ordered first suffix, without inlining or erasing them. QED.

The original raw rules are CC §4.1 (Name/closure/Result), §4.2 (ordered Bind),
§4.3 (actual Call operation witnesses), and §3.1 (Force/rebind/body/return).
No finite proof of an infinite execution is assumed.

**Consequences within this structural branch:** first obtains no reached
Return witness from its RHS, and the later g () call is not reached beyond
that RHS. The source checking clauses and pending suffix still remain.
The lemma cannot justify erasing the written int boundary or the Unit
Call, assigning arbitrary complete result contracts, or asserting that
the complete source relation has no returning alternative.

### 6.3 Why a source typing coalgebra was not obtained

The retry also tried a simultaneous semantic construction containing the
one f closure, event-indexed actual g/drop closures, all invocation worlds,
carriers and finite pending prefixes. Structural nonreturn alone does not
prove its postfixed condition.

PHI §3:179–187 requires the actual f's complete value readout: Act,
original formation/role/entry/profile/scope/incidence guards, valid captures,
actual acceptance of every independently fixed complete challenge, and the
entire observation/development contract. Its inert-root registration case
at :253–268 requires original joint registry and guard evidence. Those exact
instances were not constructed for this recursive f initializer.

Even granting an initial registration instance, CC §6:539–581 proves its
Step body Call by first obtaining an **ordinary hereditary captured-f
certificate**, applying genuine same-value inclusion and whole-carrier
checking, and only then embedding the resulting readout. Putting the new
recursive f in a declared hole does not supply that ordinary certificate.
A different simultaneous postfixed proof must discharge the full readout.

Strict retains pending argument effects, responses, worlds and future
obligations. The selected [pure-read constructor](../design/2026-10-08-pure-read-call-result-constructor.md)
§5, premise 7, also retains the complete contracts, guards, admission and
future evidence of every original W/Z/non-source alternative. None is
removed by the structural nonreturn descent.

No full typing coalgebra, primitive/annotation application or exact source
witness was completed. This is a failed constructive attempt with a concrete
conditional operational lemma, not an impossibility theorem.

## 7. What is needed and what has not become a design choice

The outstanding work still belongs to actual source constructors:

1. Instantiate generic definition/recursive registration for this f and
   nested g/drop, with actual member relations, inherited complete contract
   substitutions and the original y telescope.
2. Construct the exact original Application/Call/checking program for f y
   and its consumers, retaining all complete carrier/provider/effect/
   result/future and alternative fields.
3. Establish a lawful relation between that whole source program and the
   actual native demand, extrusion and qualified equalities. An external
   witness is sufficient in principle; no extra source Desc for C/D or
   literal native-event tag in q is required.
4. Compute SG's actual fixed/template walk and both original-scope use
   allocations on that constructed input, and prove the required equality
   transport and source coverage.

These are obligations, **not completed results of this report**. Another
conditional theorem that merely assumes them would not advance the task.
No evidence here decides that two different semantic completions are both
legal, that a special source restriction is needed, or that the user must
choose a new publication policy.

Current candidate_source/candidate_call/candidate_scheme payloads and
candidate_intrusion settlement do not furnish this proof. That observation
does not prove that no source construction or adequate implementation can
exist. A compiler change is therefore not proposed as a substitute for the
missing proof.

## 8. Independent review, verification and final disposition

The initial work used three separate methods: source registration
construction/inversion, semantic-independence falsification, and native/
source-owner correspondence. A fresh compiler-referee-equivalent worker
reviewed the two proposed insufficiency results and returned:

- **BLOCKING for task completion:** the supposedly new cuts retain the old
  registration/native-to-source premises under new notation.
- **Major:** generic registration was converted from an owning producer
  into an input without an exhaustive selected-rule extraction.
- **Major:** the proposed native-origin projections were not exhibited as
  existing q/Q_c/N_g fields; an external correspondence witness is possible.

The primary accepts those findings and does not integrate the two attempts
as new proof-theory results. Their frozen submission hashes were
1e598b36b6fc28a50026412e988f571b49719097129877eb1162af430be60cc9
and 3237035d4a3fd1d6040686bee8f196c19a4fe7a5f22c490c69e337d307452cd4.
Sections 5.1–5.2 record the rejected arguments and why they fail, so those
arguments are reviewable without treating unpublished drafts as authority.

The native note/checker passed independent bounded review. The primary then
corrected First -> G ownership in the note; a delta review passed with no
findings. Reviewed native-note SHA-256:
e47bd16b14fdc5fb790cbc33f0550be012dc1a7f0930681ec08bc78ef6beea22.
Checker SHA-256:
b064989f15dd9767f00e7336d01afc5465cd5d452f5029d490ab97014d8da917.

The checker was run once by its producer and once by the independent
reviewer. Both observed the stated 20-variable and 25-variable analogues
and the supplied-equality failure. No Scala/Rust/compiler/parser execution,
build, production test or compiler edit occurred in this investigation.
Research checker additions are not compiler implementation changes.

After the first review rejected the claimed insufficiency, two read-only
retries changed method to positive generic registration and exact structural/
coinductive source construction. Their actual outputs are in §6. The
repository yulang-next-action skill and an independent selector were applied
once; they found no supplied independent third producer input and recommended
adjudicating these retries, not another equivalent conditional packet or
an unsupported user-facing semantic choice.

Observed worker identities were generic equivalents; repository-role pins
were requested for the read-only referee and selector. Effective backend
model/effort telemetry was not exposed and is not inferred from configuration.
The runtime ceiling was four concurrent agents including the primary.
Reads and deterministic native checks were lightweight; no heavy process ran.

Final report review is recorded below. **The parent source obligation remains NOT SOLVED regardless of
a passing review of this report's limited, honest conclusions.**

## 9. Final report review and integration

A fresh compiler-referee-equivalent review inspected the frozen report at
SHA-256 af53a754b11b8dd7b54526b15c0ddea9c923e506e578361a0482436e3f0b14fd
against the original CC/PHI/SG/IF rules and returned PASS for the limited
conclusions, with no blocking or major findings. It expressly retained
original-task FAIL / NOT SOLVED.

The reviewer confirmed the minimum-height lemma for expanded structural
operation derivations and warned that an opaque receiver observation in a
finite ME-Call certificate is not itself that expanded derivation. The
clarifying paragraph in §6.2 makes that existing scope explicit. Final status
and this review record are integration metadata; they add no source theorem.

The primary accepts the limited review and the earlier rejection of claimed
semantic insufficiency. The final shared-record delta preserves the original
goal and records the failure to solve it, alongside the actual bounded
evidence. All compiler sources and selected design definitions are unchanged.
