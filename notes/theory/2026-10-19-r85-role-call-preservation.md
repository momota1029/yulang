# R85 positive InterfaceMatch role preservation

Assignment `R85-POSITIVE-PROOF`, handoff revision 1. Sole author and writer:
`/root/r85_positive_proof`. Status: **candidate finite proof for the frozen Draft
positive relation, plus conditional ordinary-Apply specialization**. This is a
frozen review target. It is neither an independently reviewed theorem nor an
adopted semantic rule, source/native correspondence, runnable result, or
production authority.

## Authority and unchanged parent

R85 sprint contract revision 1 is
`tasks/agent-loop/sprints/effect-hygiene-runnable-role-positive-20261019-r85.md`,
SHA-256 `6bab1a76954829dee5c84e438dee66ebb3bac43b7ea7abb403485ae8bd51c62e`.
The **only proposed semantic decision** is
`notes/design/2026-10-19-r85-role-call-positive-contract.md`, SHA-256
`fee3feaec5e8873fe4f056df3a9ae9ca16c342f0a8b314c027a35719eedd4609`,
authored by Luna. This note derives consequences of its exact positive premises;
it adds no decision, classifier, mismatch rule, adapter, diagnostic or source
restriction. Baseline `af3ccf2d63ba7f87e0359e183568db548ea53307` is
Luna-supplied and was not Git-observed here.

Charter §21 fixes executable entry roles from the **outer source annotation**:
unannotated or ordinary value-annotated binders enter as Value; explicitly
outer `[_]` computation-annotated binders enter as Computation. It also fixes
whole arguments as inert at call construction, Value forcing exactly once at
entry, and Computation retention. Its R81-pinned SHA-256 is
`547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed`.
The Authoritative top-level inference principles, R81-pinned SHA-256
`7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`,
retain ordinary Simple-sub generation, accumulation, propagation, levels,
extrusion, qualifying intrusion and generalization. The original
Simple-sub/evaluator class A/B claims retain their accepted source domain,
universal quantifiers and source/native correspondence. Their status is
**OPEN 0→0**; R50 remains **NOT_ADOPTED**. F1 and FK1 quantify independently,
including foreign continuations; no local Apply frame action resolves them.
Provider, annotation, receiver, request, residual and witness lineages stay
distinct.

Direct reusable frozen artifacts are R84 finite proof
`notes/theory/2026-10-19-r84-role-call-preservation.md`, SHA-256
`9f2520f0e5b13ddd0bb630f2fca43813037739170296cae1e38f5280b2cc987d`,
author `/root/r84_role_call_proof`; R84 source path
`tasks/agent-loop/inbox/20261019-r84-source-path.md`, SHA-256
`c5cb26e5e70739b7ea467c13ccd89bf0219aa538ba78a3917ea75ae1240f4165`,
author `/root/r84_source_path`; and R81 conditional prefix
`notes/theory/2026-10-19-r81-role-call-request-prefix.md`, SHA-256
`d3b3d52e19332506c6fab8eea7878a5ff1c81f90cf96dff548b30ab5f88c767f`,
author `/root/r81_prefix_proof`.

## 1. Finite positive role lemma

Fix a pair for which the frozen R85 `InterfaceMatch` relation holds. Let
`b_0,...,b_m` be **every actual executable binder** of its implementation,
with `b_0` its receiver, and let `s_0,...,s_m` be the paired signature slots.
The relation requires an authentic implementation and exactly the same finite
number of simple binders and slots. It also requires ordinary endpoint
evidence at every paired receiver/formal position and §21 equality between
the signature slot role and the role derived from each **executable binder's
own source annotation**. `b_0` and `s_0` are Value/int; the explicit slots
are restricted by the canonical decision to Value/int, Value/unit, or explicit
`[_] int` Computation. No premise supplies a body result.

Define `rho(b_j)` by §21 on the original annotation of `b_j`, and `sigma(s_j)`
as the corresponding checked signature role. `InterfaceMatch` gives the
bijection of positions and `rho(b_j)=sigma(s_j)` for each `0<=j<=m` directly.
Because the relation only reads the implementation binders and inserts no
annotation, adapter or binder, the executable source binder at position `j`
still has `rho(b_j)`. Thus **every actual executable binder's §21 role is
preserved and agrees with its paired signature slot**. The proof needs no
case for an unmatched or unclassifiable declaration pair: outside this
positive premise, R85 issues no certificate and asserts no language error.

The quantifier over *actual executable* binders matters. A signature cannot
give an unannotated `selected` a Computation role, even if an inferred endpoint
is later represented with latent effects or a solved-empty row. Its Value role
is fixed by its own absent outer annotation. Conversely an explicitly
`[_] int` executable binder retains Computation; the wildcard is symbolic
and supplies no concrete family grant. Ordinary inference must establish the
endpoint separately, through its own constraints. This is the reusable core
of R84's finite binder lemma within the **narrower R85 positive premises**.
R84's total Compatible/Incompatible/Unsupported partition, guard order,
mixed-failure outcomes and body-result assumptions are **not imported** into
R85. Failure to establish `InterfaceMatch` yields no R85 conclusion.

The source-to-runtime corollary has an explicit extra premise: if P2 preserves
these same original binder IDs and annotations in an admitted ordinary Lambda,
the pinned ordinary `program.rs:414–433,488–509` consumer derives Name
consumption and Lambda role from that original annotation, and
`machine.rs:910–1050` enters the resulting closure according to that role.
The mathematical `InterfaceMatch` relation alone does **not** prove P2 or
that today's role source constructor emits such a Lambda. It establishes role
agreement *if and where* the authentic binder is materialized.

## 2. Three independent gates and the exact call

`InterfaceMatch` concerns the finite interface positions and ordinarily
established endpoints only. `CheckedBody` is a separate ordinary body/result
and effect-checking judgment; it must establish the actual body against the
declared result and effects. `ValidatedTarget` is a separate authentic,
unique identity, binder/body/root/environment, graph and complete admission
obligation. Neither follows from role equality. The positive relation is not
an executable target, and neither a selected spelling nor an existing effect
declaration exemption supplies target validation.

For the exact source

```yu
role SecondInt { my second: int -> int -> int }
impl int: SecondInt { my second self selected = selected }
my answer = SecondInt::second 1 2
```

both actual binders are unannotated and hence Value by §21. If ordinary
inference supplies their `int` endpoints, the finite role portion of
`InterfaceMatch` holds. The **whole** positive certificate additionally needs
authentic membership, the matching finite slots and all stated endpoint
evidence; `CheckedBody` needs the separate ordinary result/effect derivation.
The body `selected` suggests result `int` only once its Name/binder and
ordinary constraints are actually checked. None of those premises is silently
deduced from this source sketch.

Now assume `InterfaceMatch`, `CheckedBody`, `ValidatedTarget`, R81 P1–P4 and
successful ordinary literal, Name and Call transitions. P1 resolves one
specific role/member/receiver implementation without evaluating operands;
P2 retains its original body, binders, annotations and lexical environment;
P3 emits exactly `Apply(Apply(C_member,E_receiver),E_argument)` with whole
operands, caller environments and source provenance; P4 admits complete
candidate/root/target metadata before RuntimeProgram publication. P2 plus
§21 supplies R81's P5. R81's ordinary-consumer induction can then be applied
to this *same emitted graph*. Its inner Apply delays and then Value-forces `1`
for `self`, yielding the second closure; the outer Apply delays and then
Value-forces `2` for `selected`; the checked body Name returns `2`. The
conditional result is **`Completed(Integer(2))`**. This derives a precise
post-adoption implementation target, not a current executable receipt.

For R81's distinct no-handler source
`SecondInt::second (io::observe 1) (io::observe 2)`, assume the same P1–P4,
matching Value binders, and successful ordinary operation construction. The
first Value entry forces only its whole receiver operand. Executing its
`io::observe 1` creates event `q` with payload `1`; absent a matching outer
handler, the outcome is `UnhandledRequest` at that first observe source and
resolved operation. Its saved suffix retains the pending `ValueEntry(self,
member-body, member-env)` and outer `Frame::Callee(argument=io::observe 2,
caller-env)` among crossed frames. The first Value entry and inner call have
not returned, so the second argument has not entered. The observation prefix
is exactly **`[observe(1)]`**. No `observe(2)`, returned `2`, arbitrary
response, complete root-frame capture, or later resumption follows. R81's
request/event/suffix identity is kept at that occurrence, with no merger into
a provider, residual or witness lineage.

## 3. Source/native correspondence and parent application

The R84 source-path handoff pins the concrete route and its missing owners:

| Stage | Existing bounded evidence | Exact missing premise |
| --- | --- | --- |
| Parser/occurrence | `role_decl.rs:189–224`, `impl_decl.rs:168–203`, `fixed_access.rs:184–213`; `shadow.rs:888–899` retains occurrences. | P1: source validator resolves authentic unique role/member/implementation IDs; occurrences alone are not semantic identities. |
| Member closure | `module/local_source.rs:595–623` retains ordinary named Lambda binders/annotations. | P2: role member producer retains actual binder IDs/outer annotations, body and lexical environment. |
| Call graph | `module/local_source.rs:892–970,1088–1101` emits ordinary Apply but current `::` becomes Operation in effect namespaces. | P3: selected role member emits the two ordinary Apply edges with whole operands, caller environments and source sites; ordinary Call typing remains independent. |
| Constraints/admission | `candidate_source.rs:826–882,1000–1021,1201–1222,1258ff,1662,1692` authenticates ordinary HIR roots and emits FormalEntry/Annotation/Operation/Apply actions; `shadow_apply.rs:385–427` exemption is for effect declarations. | P4: complete role metadata, selected roots and ordinary generated/accumulated/propagated constraints pass candidate and runtime admission without partial publication. Missing native `candidate_operation` and `candidate_formal_entry_annotation` definitions/`K,D` residual consumers remain OPEN. |
| Ordinary runtime | `program.rs:249–321,414–433,488–566`; `machine.rs:629–657,879–1105,1706–1775,1929–1960` consume actual Lambdas, Apply, Value/Computation entry and requests. | A role source producer must establish this exact input graph; runtime inspection of an assumed graph cannot establish it. |

This lemma discharges only the finite **interface role-agreement conditional**
in the parent route. It does not establish actual P1–P4, ordinary endpoint or
body evidence, the complete constraint/residual correspondence, or original
A/B. Two previous methods, forward producer inspection and backward runtime
inspection, left P1–P4 unchanged. Repeating a transition simulation would not
fix that. The next discriminating input is an adoption-backed, leased vertical
source materialization that inspects emitted identities, binders, graph,
constraints and admission at those owners; Luna owns authorization and
integration. No production file is edited here.

All six R84 hygiene frontiers stay **OPEN**: ordered handler matching needs
actual Catch projection; Value/Computation entry needs P1–P4 for role members;
wrong/sibling permission needs protected sibling/native residual proof;
shallow unmatched outward request needs authentic separate contribution and
residual correspondence; one continuation capture path lacks full template
transport and independent F1/FK1; one static-to-runtime operation path lacks
complete projection and native `K,D`/residual owners. R84's exact owner and
falsifier table remains the reusable breadth map at its frozen hash. This
local lemma closes none of those rows.

## 4. Mutual TODOs, checks and stop boundary

| Request / owner | First missing evidence and falsifier |
| --- | --- |
| `R85-ROLE-ADOPT` / Luna | Obtain fresh independent review of this frozen candidate and explicit user adoption of the sole canonical decision. Falsifier: decision bytes move or an interface mismatch is silently made a language error. |
| `R85-P1-P3` / future HIR role-resolution/member/LocalSource owner under a new Luna lease | Emit unique identity, original binders/body/environment, and two ordinary Apply edges. Falsifier: `::` stays only Operation, lookup is eager/spelling-based, a binder is synthetic or annotation-inherited, or an operand/source site is lost. |
| `R85-P4-CHECK` / future solver and runtime admission owners under a new Luna lease | Show ordinary endpoint/body/Call constraint generation, accumulation and propagation plus complete candidate/root/target admission. Falsifier: an endpoint is copied from the signature without ordinary evidence, partial target publishes, or an unrelated effect exemption admits it. |
| `R85-NATIVE-HYGIENE` / Luna to pin original native owners | Establish candidate Operation/FormalEntry definitions and joint `K,D`/residual consumers; keep F1/FK1 and protected sibling quantifiers separate. Falsifier: permission becomes inflow, FreshUse/original endpoints merge, surviving contribution disappears, or one local frame stands for foreign continuation. |

Checks: read-only exact SHA-256 of the R85 contract/decision and three frozen
dependencies; bounded read of governing §21/top-level authority and prior
frozen source evidence; finite symbolic proof and application to R81's
conditional induction. No new source read, test, build, probe, compiler CLI,
Git, external contact, delegation or scratch output. Requested model/effort:
`gpt-6-sol`/high. Observed effective model/effort: **UNKNOWN/UNKNOWN**; no
routing metadata was exposed. R85 proof grant **300 seconds charged in full**
at issue, no carryover; actual CPU/memory and pre-clock elapsed time UNKNOWN.
First explicit clock receipt: `2026-10-19 02:30:58 UTC`.

Exactly two new paths belong to this assignment: this note and
`tasks/agent-loop/inbox/20261019-r85-proof.md`. No descendants, coauthors or
unresolved descendant leases. No further in-envelope stage remains after
the handoff hash receipt. **STOP: writes cease on freezing the handoff;
independent review, adoption, implementation and shared-state updates belong
to Luna.**
