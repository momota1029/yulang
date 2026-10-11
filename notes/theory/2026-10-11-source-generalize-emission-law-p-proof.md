# Source Generalize emission law P: constructor induction stops at formal rebind

Date: 2026-10-11
Status: frozen research-only constructor correspondence analysis; independent review pending.
Baseline assigned by primary: `35e88c8113c9c6516e260170503bea753e4ede6`.
Branch assigned by primary: `research/simple-sub-intrusion`.
Exclusive output lease: this file only. One Sol/high leaf attempt; no delegation.
Claim class: bounded source/implementation characterization and a localized missing premise.
No theorem, implementation, production, or parent Generalize gate closes.

## 1. Objective, authority, and frozen statement

The objective is to establish the source-emission law P identified in
[the prior correspondence note §5](2026-10-11-value-generalize-level-correspondence-proof.md#5-first-unprovided-source-law),
from actual constructors and consumers. The method is induction over the
owning source rules and their contract-field incidences. It does not repeat
the prior numeric level/capture derivation or retained-evidence inventory.

The governing definition is
[native source Generalize §§2–4](../design/2026-10-08-source-generalize-definition.md),
selecting [construction §§3–5](2026-10-08-source-generalize-definition-and-proof.md).
In particular §§3.1,3.3,4,5.1–5.3 supply the source constructor inventory,
original binder regions, Fix/Internal edges, publication, and allocation.
The [complete captured closure definition §§2–4](../design/2026-10-08-captured-closure-constructor-definition.md)
and its selected [Strict/source rules §§3.1,4.4](2026-10-08-captured-call-closure-introduction.md)
give the concrete formal-entry case used below. The 2026-10-11 top-level
inference principles §§1–5 govern proof direction and necessary abnormal safety.

Freeze the original domain: every finite resolved source/contract graph S,
its original binder tree T, genuine local laws L1–L5, actual initialization or
inert-closure anchor, actual publication p, validating component C, and final
formed root R_b admitted by the selected source rule subsystem. This includes
its full original source/checking grammar, finite recursive proof grammars,
and complete contract fields. It does not assume the private HIR inventory
exhausts this domain. The reference is

```text
Generalize_source(S,b)
  = ScopedClosure(p,C,T,anchors_b,templates_b,N_b,R_b).
```

P has the following unchanged required conclusion, for every source rule
instance in that domain:

1. Every complete free dependent field and original binder incidence of an
   actual Mono/Established, Executed/OneShot, or Shared contract has one
   correlated candidate representation arising from its owning constructor.
2. Every source Fix incidence preserves the same field assignment or original
   binder across incoming frames, transitively through the complete free
   admission, latent/future, provider, world/allocation, and evidence telescope.
   A Family's bound parameters stay bound; an actual instantiated Mono's free
   fields have their own fixed incidences.
3. An Internal incidence retains the whole simultaneous component relation
   and every conjunct. Fixing a raw member/provider identity does not fix its
   separate inferred descriptions. An actual Established/OneShot dependency
   may still fix such a description, and Internal traversal does not undo it.

Correlation here requires preserving the original joint tuple and strategy;
it does not prescribe one compiler row per source field or a new runtime tag.
For every retained ordinary declaration q, the original parent conclusion is
still exactly `template_impl_b(q) iff Desc(C,q,sort,sigma,Delta) is retained
and q is outside Fix_source(p,C)`, at q's original scope. The full parent
also retains new/alias, Shared/ViewLogic/EventField/EventProof incidences and
the same final-root lawful-use fiber for

```text
forall finite independent joint d_U and well-scoped W.
  exists finite allocation m_d, before assignments/challenges/histories,
    preserving the original scoped strategies and joint public fiber.
```

P is a necessary construction premise of that parent, not its complete
conclusion. L1–L5 are genuine source laws, not assumptions that the compiler
emits those laws. No all-local envelope, source-role recovery from IDs/levels/
shape, successful-query premise, restricted constructor class, independently
chosen marginal witness, or extra genericity premise is introduced. Complete
Call retains callee computation, inert whole carrier, returned callee, receipt,
entry/Force/rebind, body, invocation return, and pending suffix. Attachment,
provider, witness, and residual lineage remain distinct.

## 2. Constructor induction and its first unfinished case

An induction proving P must apply each source rule's actual operand telescope
to the corresponding emitted native constraints and their consumers. At a
Name rule, lexical resolution identifies the read operand; the induction
premise must already supply the operand's whole installed certificate and its
original binding incidence. Resolution alone cannot provide that premise.

Use the already selected source

```yu
my apply f = { my step x = f x; step }
```

The source construction §5.3 states the relevant classifications directly:
at step publication the actually rebound f is external Mono, whose full
contract is fixed. At outer publication this formation remains under the
original outer invocation event. f's ordinary Desc declaration precedes the
outer challenge; its actual installed value/certificate comes from entry/
rebind. The classification is supplied by that source rule, not by the native
formal row's age or shape.

The selected Strict constructor spells out the source dependency:

```text
receipt;
Force_I(wholeCarrier) >>= (a_f,r_f,C');
  typed-rebind(f,a_f,r_f,C');
  body[f := (a_f,r_f), current := C'];
  original-invocation-return
```

At a pending Force there is no installed returned f yet; the continuation
retains rebind and the unfinished suffix. At an actual Force Return the
returned value/root/provider, current world, hereditary certificate, and
rebind edge share that exact dependent tuple. The local closure then captures
that same f. These are selected source laws, not a request to invent a new
foreign contract or to choose its witness independently.

Thus the first induction premise needed by this supported nested capture is:

> For the original formal introduction, the native registered parameter and
> its uses interpret the whole certificate installed by actual Return/rebind,
> with every free dependent field at the original outer-event telescope. The
> step capture refers to that installed Mono contract, and every incoming
> step frame shares its fields/binders within that same actual event. Pending
> entries retain their future rebind incidence without installing it early.

This is the formal-entry instance of P, not an additional hypothesis adopted
for a different theorem. It asks for the actual source-to-native bridge at
the whole-interface and formal-introduction owners. The actual source laws
already specify the required incidence; what is missing is their native
emission/interpretation derivation.

## 3. Actual producers, and what their consumers establish

| Owner | Actual emitted/retained fact | Unfinished premise of the induction |
| --- | --- | --- |
| `yu-hir/src/module/local_source.rs:288–318,329–383,637–660` | Lambda/formal introduction, lexical scope, resolved Parameter identity, original source occurrence; local publication restores and installs its lexical binding. | Interpretation as the actual Return/rebind's whole dependent certificate and event telescope. |
| `candidate_source.rs:188–201,211–217,238–246` | One parameter recipe, FormalRegistrationInput, and FormalNameInput; a formal Name uses that Parameter endpoint. | The complete installed Mono contract incident to that registration. |
| `candidate_source.rs:543–558` | Validates the same parameter recipe and retains its positive native root once. | Source whole-interface/actual introduction meaning of that root. |
| `lib.rs:11233–11368` | Lambda emits the parameter/body four-port Function and distinct entry/return effect rows; entry and body effects flow to return effect. | Complete receipt/Force/Return/rebind/world/certificate incidence, including pending source suffixes. |
| `candidate_source.rs:394–415`; `shadow_apply.rs:1304–1403` | Apply stores the source operands/checking cause and constructs the native negative Function demand, callee/argument/effect/result terms. | Actual complete Call and same returned formal certificate, including provider/future fields. |
| `candidate_call.rs:16–58,289–431` | Its observer validates source Lambda/Name/Apply correspondence, lexical ownership, registered root, four native ports, and invocation row. | It supplies no derivation of the registered whole source interface or actual formal introduction. |
| `candidate_source.rs:300–326,624–655`; `candidate_scheme.rs:1320–1337` | Initializer effect inclusion is scheduled once; local installation stores LocalScheme(id,root,boundary). | Original source Executed/OneShot/Shared field assignments and binders at the actual nested publication event. |
| `candidate_scheme.rs:1352–1383,984–1021` | Local use recaptures the selected root and prepares one canonical row map; restoration consumes its captured bounds. | Transport of the source contract fields and original event/shared incidences that the unfinished constructor premise must supply. |

These are compile-time inference actions. Executing the source schedule is
not itself execution of the original carrier or a source Return/rebind event.
The driver visits the nested Lambda body and creates its local publication
state during inference. A correspondence proof must interpret this symbolic
construction under the original source binders; it cannot identify that
single compiler scheduling step with every actual outer invocation. Nor can
it move the nested local initialization into the outer definition's initializer.

The parameter registration's actual payload is owner, Lambda index, parameter
identity, recipe position, and optional native root. FormalNameInput joins
its resolved lexical occurrence to that registration. The Lambda and Apply
owners genuinely preserve scalar ports and source causes. Neither operation
provides a proved interpretation of all free fields of the formal's complete
installed certificate. A four-port representation could be part of such a
proof; its construction alone does not supply the missing contract/telescope
implication.

There is direct confirmation at the actual boundary, beyond absence of a
record name. `PendingCallSupplier` at `candidate_call.rs:81–91` explicitly
identifies missing compiler suppliers. For an observed formal Call,
`PendingCallConstruction::suppliers` at `:225–254` returns
`OriginalRegistrationWholeInterface` and `ActualFormalIntroductionRoute`,
along with checking/seed exposure and the remaining complete Call suppliers.
The `native_registered_root` accessor establishes a retained native root, not
those missing source interfaces. Its `observe` consumer validates provenance
and port shape, and returns the same pending construction. The source-to-
whole-interface/formal-entry premise is therefore located at an existing
construction boundary rather than inferred from a row metadata flag.

The observer is exposed by `shadow_apply.rs:187–188`. It is an observation
surface, not a proof or production discharge of those suppliers. This note
does not treat that pending list alone as an impossibility theorem: an
independently established native denotation/constructor theorem could supply
the required meaning without adding stored tags. No such theorem is supplied
by the inspected producers or the packet's pinned proof inputs.

## 4. Consequences for the other P incidences

At local step publication, preserving f's canonical scalar row is insufficient
to discharge this premise. P also requires every genuinely free field of its
installed certificate, any original binder in that telescope, and correlations
with its actual event operands. This applies to fields that exist under the
genuine local contract; no arbitrary new field or hypothetical primitive is
postulated here. The native consumer can faithfully remap every captured row
while that source interpretation remains unproved.

Executed/OneShot and Shared are not alternate classifications of the native
formal row. In this source the local RHS/Return/rebind occurs inside the outer
event. Source §5.1 fixes its actual one-shot dependent tuple and retains any
Shared binder at its own original scope. Native Work::Install's effect fact
and LocalScheme root do not prove that full tuple's emission or its original
binder sharing. The first formal-entry premise must be supplied before a Name,
capture, and publication induction can use it; repeating freshening lemmas
cannot create that premise.

Internal remains a separate required case. Actual native component scheduling
at `candidate_scheme.rs:844–938` registers all active roots/uses, runs all member
schedules, and stages a separate root capture for each member. Open use routing
at `:939–947` validates both active members and delegates to `route_internal`.
This establishes source registration/routing facts, not the full semantic
simultaneous relation. The existing discarded-peer note demonstrates the
f-root representation omission for `my f x={my u=g;x}; my g y=f`; it supplies
no lawful distinguishing client or proved reconstruction. This attempt does
not repeat that capture audit or classify y from its row/component identity.
P still requires the whole original component relation and its clauses at
each incoming frame. Solving the formal-entry premise alone would not close
that independent Internal bridge.

The full-domain inventory also includes Record/tuple, explicit Delay, handlers,
general checking/conversion grammars, and State when genuine local laws are
provided. `LocalSourceForm` at `local_source.rs:107–141` supplies its narrower
private inventory; `Builder::expression` at `:482–695` rejects other syntax
cases and tuple delimiters on this route. That is an additional implementation
coverage boundary. It is not the reason the selected nested capture stopped:
Lambda, Parameter Name, Apply, and private Block binding all have authentic
construction branches. Exact parsing/execution was not tested in this packet.
The result is a correspondence theorem gap on a source case with selected
local semantic laws and authentic HIR constructors, rather than evidence of
an unsupported source semantics or authority to exclude the original domain.

## 5. Economy audit, result, and next action

The prior level argument and evidence-table audit both left P untouched. This
attempt followed the existing economy audit by changing the method to owning-
rule induction. It reduces the first supported capture premise to the existing
`OriginalRegistrationWholeInterface` / `ActualFormalIntroductionRoute` seam,
with the exact source Return/rebind telescope above. It does not pretend that
localization proves P or advances the parent to closure.

Under `rules/compiler-engineering.md`'s economy rule, preserving installed free
contracts/binders is A; natural nested capture/publication is B. Reconstructing
the formal's contract incidence from native row IDs, levels, or solved shapes
would incur D. Its lexical introduction and use incidence are already known
at HIR/source construction. Complete semantic certificate/telescope meaning
still needs the original entry law and its native interpretation; adding a
certificate that assumes that meaning would merely restate the gap. No new
representation, semantic restriction, or implementation strategy is adopted.

Result: bounded constructor correspondence; exact first unprovided formal-
entry emission premise. P and full-domain source Generalize remain OPEN. No
source-qualified semantic counterexample, independent certification, complete
Call, hygiene, soundness, or principality theorem is claimed.

One next action: the primary should assign the existing whole-interface/formal-
introduction owner to derive the complete native interpretation of the actual
returned formal contract at its original event telescope, and apply it to this
step capture. Require the same tuple and pending rebind cases; do not substitute
another operational level proof or assume P. Internal/whole-component coverage
retains its independent owner and OPEN obligation.

## 6. Checks, dependencies, and resource use

Checks performed: `cat`, bounded `sed`, `rg`, and `sha256sum` on the named policy,
authority, pinned proof inputs, constructors, and consumers; leased-note creation;
final dependency hash comparison and static note integrity inspection. No Git
command, build, test, Oracle, numerical probe, benchmark, or compiler mutation
ran. No delegation occurred. The primary remains the verification owner.

Budget consumed: one bounded leaf derivation; zero heavyweight processes,
probes, or measurement samples. Read-only startup calls used at most five
concurrent lightweight commands; later source reads were sequential. No numeric
CPU/RAM/wall limit was supplied in the leaf packet; exact cumulative wall/CPU
and peak RAM were not measured. Requested runtime: `gpt-6.1-sol` / `high`.
Observed model/effort runtime metadata: unknown. Role config was inspected:
prover has no model/effort pins, and repository defaults request Sol/high.
This configuration inspection does not establish effective runtime settings.

The primary supplied the baseline SHA. No Git access was authorized, so this
producer records exact live dependency hashes and their final stability, and
leaves baseline-equality validation to the primary. The inspected hashes are:

```text
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35  crates/yu-solver/src/candidate_call.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6  crates/yu-solver/src/shadow_apply.rs
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38  notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240  notes/theory/2026-10-08-source-generalize-definition-and-proof.md
4b63cc39c0d1dab2809e7f7948bf323857fd7461618a5350687897280f6c3325  notes/theory/2026-10-11-value-generalize-level-correspondence-proof.md
e0e5518a04d55850979e71170fa3b776499495a40314f88c519bede374390b7a  notes/progress/2026-10-11-value-generalize-level-falsification.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd  notes/design/2026-10-08-captured-closure-constructor-definition.md
0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f  notes/theory/2026-10-08-captured-call-closure-introduction.md
```

Unverified scope: actual parse/acceptance and runtime consumer experiments,
whole native contract interpretation, all-language constructor coverage,
complete Fix/Internal replay/activation, original binder-strategy transport,
abnormal publication/suspension coverage, complete Call, effects/protection/
attachment hygiene, soundness/principality, public projection, and cutover.
Source laws selected in the governing documents are dependencies, not new
theorems proved here. This artifact is frozen for primary-assigned independent
review; its author does not certify it.

## Commit packet

- Exact leased changed path: `notes/theory/2026-10-11-source-generalize-emission-law-p-proof.md`.
- Baseline SHA: `35e88c8113c9c6516e260170503bea753e4ede6`.
- Changed dependency hashes: none during final producer recheck; comparison
  against the assigned baseline is unverified by this leaf and remains primary-owned.
- Honest review status: research-only localized missing premise, independent
  review pending; P and original full-domain Generalize parent OPEN.
- Checks already run: static owning-rule/consumer trace, dependency SHA-256
  stability, note integrity/whitespace inspection; zero executable verification.
- Proposed checkpoint message: `research: localize Generalize emission law P to formal rebind interface`.
- Shared-record deltas left for primary/curator: retain original P and Generalize
  statements/statuses; link the supported nested capture to the whole-interface/
  actual-formal-introduction source owner; retain Internal whole-component
  coverage separately; do not promote localization to theorem or source
  restriction. No shared record was edited.
