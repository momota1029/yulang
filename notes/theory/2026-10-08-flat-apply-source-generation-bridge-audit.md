# Flat literal Call: source-generation bridge audit

Date: 2026-10-08
Baseline: `435af7d5820dad2a84c22e7220e6013cee7f8010`
Branch: `research/simple-sub-intrusion`
Status: frozen unreviewed research; bounded source correspondence and conditional derivation
Exclusive lease: this file only
Method: trace the input/output judgments and the first constructor of each argument coordinate
Semantic adoption, implementation, aggregate closure and independent certification: none

## 1. Objective and result

For the inner elimination `c = Apply(Name(u_f),Literal(a_1,"1"))` in
`my apply f = f 1`, determine whether source generation already supplies an
adapter into the selected original Name/Name Gen-Call-0 family. It does not
in the inspected envelope. It supplies a literal expression root, normalized
literal code, a complete local Call relation and dependent ReceiveSchema.
The missing connection is the original source constraint-generation owner's
typed registration and installation of a literal introduction in the family
consumed by OC-CallEff. A source expression ID is available before that cut;
generating another expression ID cannot discharge it.

This audit adds the producer/consumer trace and distinguishes the registered
expression table from H-R's original typed port operation. It does not repeat
the [argument-origin extension](2026-10-08-literal-call-argument-origin-extension.md)
§§3–4 injection/action proof, the earlier
[applicability audit](2026-10-08-flat-apply-original-emission-applicability.md)
§3 nonderivability argument, or their searches. The reduced source above is
their retained dependency witness, not a newly claimed semantic counterexample.

## 2. Exact premises, dependencies and authority

**H-source:** an actual resolved finite acyclic source/binder graph, original
body scope and formal binding `Gamma(d_f)=Value(A_f)`, one joint `xi=(nu,K,D)`,
and the independently interpreted existing literal primitive at `a_1`.
`Value(Int)` below is conditional on that primitive. The literal spelling and
a shadow Int result do not establish it.

**H-gen:** the reference source-generation judgment and local operations of
[initial-context construction](../progress/2026-10-06-initial-context-source-construction.md)
§§3–4.4 and [typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
§6. They are a conditional reference subsystem; the typed-core header remains
Draft and total raw-source elaboration remains open.

**H-old:** the supplied Name/Name Gen-Call-0 introduction in
[source Call construction](../progress/2026-10-06-source-call-generation-construction.md)
§3 and §§4.2–4.4, including its genuine argument Name/Return child. This is one
established generator instance, not an exhaustive original inventory.

**H-completion, unestablished:** the H-R and H-E operations/laws at this exact
literal source tuple from the
[literal introduction proposal](2026-10-08-flat-apply-literal-original-constructor.md)
§2, retaining all original atoms and the proposed family's old image. Section
5 gives consequences if this missing premise is supplied; this audit does not
select, construct or certify it.

The selected original consumers are
[formation](../design/2026-10-07-original-call-formation-definition.md) §§2–6
and [ownership](../design/2026-10-07-original-call-owner-definition.md) §§1–4.
Formation §1 expressly limits its adoption to already emitted records and
preserves other Calls' old derivations. Ownership consumes actual registration,
callee route, emission and an independent directional SeedExposure. Neither
definition is permission to manufacture the upstream literal emission premise.

Accepted decisions stay fixed: integrated Function-view `q1/a2`, decisions
1–6, requires shared source inference, original scope/xi, Q-independent
admission and separation of the inferred protected formal from an actual
provider's role/entry. Integrated ReadInvoke `q1/a1`, decisions 1–4, places
finite rule insertion/lookup evidence at its source-construction owner in
the identity Name/Name seam. It supplies neither new rule meaning nor a
literal scope extension. Both approved drafts were checked against the pinned
bytes and occur exactly inside their approved answers; their receipts record
integration. No pending approval is consumed or edited.

Claim classes: section 3 is a conditional generation derivation under
H-source/H-gen; section 4 is bounded correspondence under H-old and the
inspected paths; section 5 is a conditional consumer consequence under
H-completion. Existing selected O0/O1 results remain established in their
own scopes. Original authenticity, semantic typing and production conformance
are unestablished here.

## 3. What the source judgment receives and emits

The reference judgment is explicitly

```text
Delta; H; R |- e => (I_e,d_e,n_e ; Phi_e,J_e).
```

Initial-context §3 preallocates one `r_b` per source binding/expression.
Section 4 supplies independently interpreted declarations/imports in Delta,
the two-hole typing context H where applicable, and registered root table R.
Its output has source interface I, inert descriptor d, normalized consumption
code n, relation Phi on one original tuple X, and static source incidences J.
It does not require a satisfying assignment. Instantiate the ordinary rules
with no occurrence referring to H; H remains an input context. This is no
closed-world admission or context-weakening theorem, and installs no tested
filling.

For the flat formal, the actual Name rule (§4.1) references `d_f`'s registered
root; it creates no provider. Literal (§4.1) uses its independent primitive.
Typed-core §6's disjoint normalization yields:

```text
u_f -> d_f; Gamma(d_f)=Value(A_f)
I_f=Value(A_f); d_f_use=name(d_f); n_f=result(d_f_use)

a_1 is the literal expression occurrence, not a Name use
I_1=Value(Int); d_1=literal(a_1,"1"); n_1=result(d_1)
Result(I_1)=Comp(empty,Int); J_1 retains this actual primitive/Return image

I_c=Computation(E_c,A_c)
d_c=reify(call(n_f,n_1))
n_c=Normalize(I_c,d_c)=eliminate_(c's designated port)(d_c)
```

The existing administrative result normalization can present the complete
Call as `call(n_f,n_1)` under its same-context law. This final result reify is
distinct from Call's inert whole-argument construction `Delay(n_1)`.
The lambda body/result skeleton does not turn `E_c` into a bare body row or
prove the full advertised Function contract.

Initial-context §4.4 introduces one scoped complete Function variable F at
the resolved callee/root scope and emits, with both child relations retained:

```text
Phi_c includes Phi_f and the literal primitive relation Phi_1, and
 WF_Dec(F;xi)
 VIncl(A_f,F;xi,e_f)
 WholeArgCompatible(Result(I_1),CarrierContract(F);xi,e_1)
 ReceiveSchema(c,F,original callee root,Delay(n_1),call view;xi)
 CIncl(ExecuteCallableImage(n_f,Delay(n_1),F,e_f,e_1;xi),
       Comp(E_c,A_c);xi,e_out).
```

These are independently interpreted semantic propositions, emitted before
solving. `Result(I_1)` alone is not its exact source image: the retained
primitive and Return child distinguish this literal from arbitrary carriers
with the same printed interface. The image retains callee evaluation, inert
argument construction, receipt, actual provider entry/body/designated consumer
and complete return. ReceiveSchema's producer ports depend on the later actual
provider; the generator does not invent that provider's parameter binder.

The expression root `r_(a_1)` in R and static source references in J are
useful source evidence. The displayed judgment does not conclude
`e_c : emitted Gen-Call-0`, an original per-atom insertion/lookup witness,
or the full registered Result/Reify/checking/result/suffix attachments of
Code-Call. Calling its source references "original" does not supply those
different judgment heads. H-R requires the typed origin terms, source-parent
and scope projections, freshness/reuse and whole-map laws for these ports;
preallocation of R alone proves none of that additional contract.

## 4. Where the argument coordinate is first created

| Layer and exact locator | Argument coordinate and evidence | Consequence for the bridge |
| --- | --- | --- |
| Source Call construction §3, then §4.2 | `u_x -> d_x`, `Gamma(d_x)=Value(A_x)`, `J_x=ReturnImage(Name(d_x),environment)` | Gen-Call-0 reuses a genuine Name child already fixed in its input; it does not create a generic argument expression |
| Initial-context §§3,4.1,4.4 | expression root `r_(a_1)`, actual literal primitive, `n_1`, whole `Delay(n_1)` | a literal argument has source-derived reference evidence without Name resolution |
| Shadow HIR `shadow.rs:2618`, `:2723` | IntegerLiteral calls `push_expression`; Chain stores that returned ExprId as `Form::Apply.argument` | expression identity is created at the literal leaf and attached to its parent Apply |
| Shadow HIR `shadow.rs:2371`, `:2173` | `push_expression` assigns ExprId; scan projects existing Apply operands | neither address allocation nor scanning types an original port |
| Core `shadow_call_formation.rs:117` | `PendingSourceCallStub.argument: ExprId`; `argument_use=Some(UseId)` only for `Form::Use`, otherwise None | the generic structural carrier can retain the literal; it deliberately lacks original typing/emission conformance |
| Core `shadow_call_formation.rs:201`, `:309` | SymbolicDemand needs `argument_declaration`; captured builder pattern-matches argument `Form::Use` and nested Lambda/Bind/returned Use topology | this narrower symbolic family has no literal adapter and itself leaves original membership unresolved |
| Formation definition §2, ownership definition §2 | original `Idx(e)` retains `u_x`; Route is the **callee** Name/capture route | an available callee route supplies no argument Name child or family introduction |

The source registration owner is typed source constraint generation
([source-introduction contract](../design/2026-10-07-original-call-source-introduction-contract.md)
§2). Resolution supplies lexical facts; generalization/instantiation transports
facts already established there. The Name/Name argument coordinate is created
before original consumers see the record. Therefore changing the consumer's
parameter spelling from `u_x` to `a_1` cannot repair the input family's missing
literal constructor.

The proposed `Keep(old)+Add(literal candidate)` representation has an explicit
old-image injection and inverse. The original target is the emitted family,
not that proposed representation. No inspected source rule identifies Add
with actual emission, supplies H-E's installation, or upgrades expression R
registration to H-R's typed original port law. This is the exact remaining
owner boundary, not a claim that the language lacks ordinary literal Calls.

An alternative surrogate declaration, such as `my x_1=1; f x_1`, changes the
source graph, child constructor and binder/scope incidences. Even if a separate
administrative proof showed equal execution for this pure literal, it would
not provide an identity-preserving record at the original literal c. The
selected old instance also has its own nested formal topology; introducing
one Name does not establish that instance's premises. Such a route requires
an independently authorized source transformation and origin/constraint
transport theorem. None is supplied or selected in this audit.

Ordinary production remains a distinct path: `module.rs:1940`'s
`lower_simple_chain` rejects an associated non-leaf Apply as Unsupported;
`module.rs:1547` turns that into UnsupportedExpression. This preserves the
known rejection before solver collection. Shadow evidence cannot be read as
a production Call judgment or semantic authority. No compiler implementation
or production test is performed here.

## 5. Conditional bridge and exact next supplier

H-completion must supply two independently checkable owner outputs:

1. **H-R:** register the shared formal-contract root once and return authentic
   typed operand Result, whole-argument Reify, checking, complete-result,
   elimination and dependent suffix origins at this literal c. Preserve the
   source-parent/scope projections and one legal action on the whole tuple.
2. **H-E:** install the actual literal source introduction at the original
   owner/root and embed its output into the original emitted family, preserving
   the literal child, all original atoms, original indices and old Name image.
   Retain actual original insertion/lookup and interpretation correspondence.

Given these outputs, the existing independent literal/Name constructors and
Code-Result yield the two operand codes. Carrier-Delay uses the original
whole-argument ReifyOrigin; Code-Call bundles their actual checking origins,
complete result and suffix ports into Check. Separately OC-CallEff reads the
same actual e_c's demand, uses `Inv(Id(F),F)`, and forms O0. Reg/Route/O0 give
the selected shared slot. An independently derived flat SeedExposure is
still required for paired O1; an Int argument or annotation absence alone
does not supply that seed. None of these consequences proves Phi truth,
inlet acceptance, original CallInitial/I0/action or source semantic typing.

This is a conditional composition of existing constructors, not a derivation
of H-completion. Two prior methods leave that same premise untouched; this
trace confirms its first owner instead of running a third checker assuming
it. Recommended next action: the primary should adjudicate and supply the
bounded original literal emission completion at typed source constraint
generation, with the proposed family's preservation and H-R/H-E laws reviewed
at that artifact. Any needed semantic authorization stays with the primary.

## 6. Independence, coverage, failures and resources

No executable oracle, seeds/ranges, enumeration, mutation run, build, test or
performance sample was used. The method is a bounded source-judgment trace.
The reference generator and candidate proposal share the literal primitive,
descriptor operations, source tags, scopes and joint xi. Agreement of their
templates is consistency under shared assumptions, not independent proof of
those source rules. The code reads independently establish retained Rust
output sorts, with no claim that those sorts implement the source semantics.

Analytic mutations identify failure conditions: replace literal with a fake
Name and the original child/graph changes; split xi per port and the joint
input law fails; pass a pending ExprId to Code-Call and its original-origin
premise remains unsupplied; erase a separate original result atom and H-E's
inventory law fails. These are documentary checks, not executed mutants.

Coverage is this flat literal Call and the displayed selected source rules
and directly implicated structural owners. No repository-wide absence search
was completed. Other original introducers, computed callees/arguments,
annotations, recursive/State/method sources, conversion adapters, complete
admission/profile/contribution laws, source typing truth, principality/export,
Option 2, F5 and production correspondence remain unverified.

Resources: one producer, one Markdown output; zero children, heavy processes,
builds, tests, formatters, scratch outputs or Git mutations. Read commands
were lightweight; at most seven independent shell reads were in one batch,
not compute probes. Dependency hashing used one Python process and sequential
read-only `git show` subprocesses. No numeric CPU/RAM/wall budget was supplied;
CPU, peak RAM and reasoning wall time are uninstrumented. Some initial combined
captures truncated; all relied-on source sections were reread in narrow slices.
Writes stop at submission for frozen review.

## 7. Dependency freeze and commit packet

All 23 direct dependencies below match pinned-baseline bytes. Both current
approved drafts embed exactly in their answers. No dependency hash changed;
the primary must recheck at integration. Task/index reads located accepted
work and governing files; they are not used as independent semantic premises.

```text
5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6 rules/research-lab.md
925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5 rules/design-authority.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e rules/git-concurrency.md
8c617ceb978dfa26ce12f4f71ecc8ece22ffd8f1cf1982125b33142f645ae1c0 rules/question-board.md
6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073 notes/progress/2026-10-06-source-call-generation-construction.md
4940e031b83d3d0315f17beb51ba2e952ec64ae7d57d9ae0d086024c7305ca9f notes/design/2026-10-07-original-call-formation-definition.md
0b86e367cf8170f4f9d095f0afe8e9f6003209189dc358e294941727962ff110 notes/design/2026-10-07-original-call-owner-definition.md
c825c668dd8f523a8274aa37a3b11665c177e07b1aa1f1d9559c3f6807a9baa5 notes/theory/2026-10-08-flat-apply-literal-original-constructor.md
8796711fcea9deadc4a86873cfb387eb2f66ceccd64d1a92cd506084ea1f11ff notes/theory/2026-10-08-literal-call-argument-origin-extension.md
10e86ed3bac72d91f03c83acf50ed8e8336ab3c3d0df4a90a03cbe4efdc7ef75 notes/progress/2026-10-06-initial-context-source-construction.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e notes/design/2026-10-02-typed-computation-core-elaboration.md
f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6 notes/theory/2026-10-07-call-input-construction-proof.md
1dcdfc40990a93c52ced1ae3ee11fd393014634864da8c480f8f943a2065ebc0 notes/design/2026-10-07-original-call-source-introduction-contract.md
5e2575d74027d248f0fef0207cab89f6ac0b7d78ab889ec345c581f3a5092292 notes/theory/2026-10-08-flat-apply-original-emission-applicability.md
1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536 questions/2026-10-05-function-call-view-formation/approved-answer.md
585211d345ead07c8401576c84d216be858d3c7c81e8b412e8ba36a28460d35c questions/2026-10-05-function-call-view-formation/answer-draft.md
6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0 questions/2026-10-05-function-call-view-formation/receipt.md
1920f732c255136e4d12f8dba13b2320480d250bdd4b2f778a33cabd3f405f13 questions/2026-10-08-readinvoke-source-presentation/approved-answer.md
9b47291c227bc8c7f3f3bf7209572fb5ec31391fd3b92b3bc3ccdae13d3d2d2d questions/2026-10-08-readinvoke-source-presentation/answer-draft.md
fb87e7eed0b8ffcb069cd18f9972758df919825c64baef1f4f2c840a66783ab0 questions/2026-10-08-readinvoke-source-presentation/receipt.md
394c763e5b4e2de6ae692ffacf22c07db8958f00129a47f1332f238c9a8eb5eb crates/yu-core/src/shadow_call_formation.rs
5a3c61bf87a3f6147897816beea369df49059a49141607af9cca8c720c43386f crates/yu-hir/src/shadow.rs
3bb488f9d9e13b43e79e472a65a35197ae4f2c76ae21a6f0f8f77195661f4363 crates/yu-hir/src/module.rs
```

- Exact leased changed path: `notes/theory/2026-10-08-flat-apply-source-generation-bridge-audit.md` only.
- Baseline SHA: `435af7d5820dad2a84c22e7220e6013cee7f8010`.
- Changed dependency hashes: none.
- Review status: frozen unreviewed source correspondence/conditional derivation;
  no self-certification, semantic adoption or gate closure.
- Checks already run: scoped `rg`/`sed`/`cat` reads, read-only HEAD/branch
  inspection, SHA-256 and pinned-byte equality, exact approved-draft embedding,
  leased output link/whitespace/hash-table checks. No model, test or build.
- Proposed checkpoint message: `research: trace flat literal Call source generation boundary`.
- Shared-record deltas intentionally left to primary/curator: retain the
  distinction between expression-root registration and H-R typed port
  registration; retain original typed source emission/installation under H-E
  as the next owner cut. Keep flat SeedExposure, source typing, CallInitial/I0
  and production gates separate. No task/index/authority/question edits or
  status promotion is included.

Writes stop before frozen submission.
