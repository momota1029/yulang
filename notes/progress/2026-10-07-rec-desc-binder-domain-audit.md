# Returned Function binder and witness-domain audit

Date: 2026-10-07
Baseline: `e8a05ef15a6f896af3041e1c10a32e76593f65f1`
Status: frozen research characterization; compiler-referee reviewed, no findings
Method: bounded source/document correspondence, with a conditional expansion of the explicit candidate Function clause
Scope: returned/latent Function obligation binders in the assigned sources
Implementation authority: none

## Result and exact premise

The audited clauses do **not supply a complete original binder tree for
production latent Function `DescMem`**. They preserve an input binder tree;
preservation is not construction. The coupled-core candidate does supply an
explicit Function universal prefix, and expanding its returned Function
conjunct yields nested universal call obligations without introducing an
existential witness. The reference constructor rules supply a joint finite
derivation witness for each reference observation, with sharing preserved
within that derivation. Neither fact identifies which additional descriptor
witnesses, if any, must be jointly bound across incompatible future challenges.

This is bounded absence in the listed windows, not an impossibility result,
a countermodel to FH, or a selection of per-use production semantics. In
particular, the audit does not conclude that all witnesses are event-local.
Fixed `(X,xi,w)` coordinates remain fixed wherever their original scopes
require it. An unknown additional binder is left unknown.

The new evidence beyond the prior
[latent clause audit](2026-10-07-rec-desc-latent-function-clause-audit.md)
is the explicit candidate's recursive universal expansion and the separate
operand-domain inventory below. The earlier audit's H1–H5 and generic
descriptor map are not repeated as proof attacks.

## Authority and dependency boundary

The production-denotation approved answer, decisions 1–5, selects Option A:
complete typed observations in the original `Rel_C` fiber, independently
interpreted endpoint/role/entry/path/origin/continuation/scope/authority/
dependency predicates, and separate comparison-independent admission. Its
receipt records integration at `0b6f326a`. The bound-membership approved
answer, decisions 1–4, selects Option 2: licensed extras need not have source
constructor evidence, while ports alone cannot license arbitrary dependencies.
The inlet-context approved answer, decisions 1–5, includes all independently
typed compatible punctured contexts, including future and unreached uses,
with whole-carrier holes and fixed original `(nu,K,D)`; its receipt records
integration at `28dddc75f`. The observation-boundary answer selects typed
projection, retaining typed events, continuation/origin relationships and
`nu,K,D` while removing concrete data identity/correlation. No choice is
reopened here. All four leave concrete proof/implementation obligations open.

Exact governing windows, with line numbers at the pinned baseline:

- Source contracts, `notes/design/2026-10-05-source-contracts-and-common-allowance.md`
  §2 opening L79–81, §§2.1–2.2 L83–142, §§3.1–3.6 L146–285,
  §3.7 L287–408.
- Source-indexed realization,
  `notes/design/2026-10-04-source-indexed-callback-realization.md`
  §2 L44–78, §§3.1–3.3 L89–174, §4 L176–204; §1 and §7 delimit
  reference interpretation from production conformance.
- Coupled core, `notes/design/2026-10-01-coupled-effect-interface-core-draft.md`
  common-carrier clauses L41–114 and candidate Function contract L930–995.
- Typed core, `notes/design/2026-10-02-typed-computation-core-elaboration.md`
  §6 L303–506, §9 L904–1121.
- Expressly referenced binding discipline: source-generated Theorem C
  `notes/design/2026-10-04-source-generated-callback-structural-theorems.md`
  §2.4 L167–202; parametric linking
  `notes/design/2026-10-02-parametric-component-linking.md` §3 L107–129.

Task/index reads served as navigation. Semantic reads used `git show` at the
pin, not another worker's moving source. The three required operating rules
and question-board rule were read. No numerical process/CPU/RAM/wall-time
allocation was supplied in this packet; work used serial bounded metadata
reads only, with no heavyweight calculation.

## Binder inventory

`B_orig` below denotes the source's **unspecified input** original binder
tree. It is not a proposed quantifier prefix. Keeping it symbolic prevents
an accidental replacement of `(X,xi,w)` by fresh independent witnesses.

| Clause and exact locator | Binder order actually supplied | Operand domain and omitted information |
| --- | --- | --- |
| Approved denotation, decision 1 | Fixed original descriptor and same `(nu,K,D)`; constraints on complete observations. | Endpoint, role/entry, paths, origin, continuation, scope, authority, dependencies. No explicit latent `DescMem` prefix, witness sort, or future-use witness-sharing rule. |
| Approved admission, denotation decision 2 and inlet decisions 1–3 | Independently typed compatible contexts at fixed interface/fiber; no comparison-success premise. | Callable and whole argument carrier fill holes; other environment values need independent validity. Scope includes unrealized/future uses. Exact environment/admission judgments and witness scope remain unfinished. |
| Source contracts §2.1, L89–105 | Primitive: supplied whole tuple. Conjunction: same shared tuple. Union: one whole-tuple alternative. Renaming: all incident operands. Scoped binding: `B_orig`, at its recorded position. Constructor image: independently supplied relation. Recursive reference: registered root. Positive recursion: least finite derivations/prefixes. | Each relation's whole operands are inputs; the table does not enumerate independent descriptor witness sorts. Positive recursion does not bind a witness across every possible future branch. |
| Source contracts §2.2, L120–130 | At given `h,xi`, membership requires `M_E(h,O,w;xi) ∧ DescMem(R_E,O,w;xi)`, then one `Pi_xi(O)`. `w` is bound at its original scope under `B_orig`. | Same observation/provider tuple and same witness feed both predicates. `DescMem` is explicitly independent of source image. Its internal binder tree and complete obligation domains are not defined by this display. Do not read the display as permission to hoist `∃w` outside all hidden universals. |
| Source contracts §§3.1–3.2, L155–198 | Preallocated monomorphic roots; original shared tuple. Bind preserves result/rebind/state and ordered suffix. Request resumes its original witness without freshening or replaying receipt. | Immutable field/capture/alias roots; closure role, entry, body, consumer; declaration-instance operands; whole call carrier and receiver/receipt. These specify actual source operands, not an independent latent descriptor obligation. |
| Source contracts §3.3, L208–222 | Admission derivations extend an independently valid finite history; no new explicit universal/existential prefix. | Initial context; typed response at exposed request; that request's raw handle; future call/force at actually returned provider's original typed port. All finite extensions are covered by the contract, but a concrete binder tree over counterfactual challenges is not stated. |
| Source contracts §3.4, L226–233 | Whole freshening/graft; joint hiding at `B_orig`; shared witnesses not hidden per segment; rigid imports fixed. | All `K,D` incidence moves together. Certificate preserves known sharing; it does not determine an absent descriptor witness scope. |
| Source contracts §§3.5–3.6, L243–280 | Induction on each finite derivation with the same scopes and joint witness. | Assumes §2, local descriptor typing lemmas, exhaustive source-base certificates. Syntactic binder matching can validate supplied rules; it cannot prove those local rules. |
| Source contracts §3.7, L295–338 | Fixed `xi,h,B_orig`; `H_G(R)` is a least relation. Step arm: `exists x,z. H_G(R)(x) ∧ W(x,y,z)`, guarded by `G(y)`. External environment and rigid assignments are parameters. Fixed universals stay pointwise at their original positions. | Here `x` is a predecessor whole tuple and `z` the abstraction relation's step witness, **not** an argument value or automatically a returned-provider witness. `Z(y)` may supply extras without source anchors; its internal witnesses are independently supplied. All future/provider operands and scopes must be declared in `W,Z`. Ordinary `DescMem` remains inside `G`. |
| Source contracts §3.7, L363–391 | On each checked-admitted fiber, paired grammars retain identical/contained hard envelopes and matched parameters. | Abstract-provider future-use rules and unchanged-domain certificates are additional hypotheses. Positivity does not prove admission preservation. This cannot turn reference evidence into exhaustive production evidence. |
| Source-indexed §2, L63–74 | Fix `xi`, `C_old`, and shared `X`; local witnesses hidden only under `B_orig`; shared witness bound once around its joint formula; rigid binders retain positions. | `X` includes shared roots/endpoints/argument/body-result/continuation/owner-view coordinates. A finite joint relation's scope is supplied; no single binder is explicitly asserted around all mutually incompatible future histories. |
| Source-indexed §§3.1–3.2, L93–141 | Inert introduction/Return; later certified use unfolds the retained label at current context. Same captured roots and request witness continue. | Name, lambda, operation, delay, result, eliminate, bind, call operands are source-indexed. No universal satisfaction clause for independent latent production `DescMem` is given. |
| Source-indexed §3.3, L145–168 | Given `e,h,xi`, a finite derivation has full witness `w`; `Der_ref(e,h;xi,w)` precedes final whole `Pi_xi(Obs(w))`. | Reference membership inversion recovers a finite constructor witness. That witness includes the derivation's latent structure. It is not an existential completion certificate for every alternative future challenge, or an ordinary descriptor-failure inversion. |
| Source-indexed §4, L181–204 | Initial and history-extension certificates independently determine `h` before the query. | Carrier/result-rebind path, lexical/provider roots, compatible current owner/view, paths and `xi`; response/handle/future call-force domains retain exact request/provider incidence. Same-type responses from other histories cannot be substituted. |
| Coupled core common carrier, L43–114 | Fix imported `rho` and admissible assignment `nu` to owned `beta`. `Rel_C(rho)` contains `(nu,O)` pairs. One common assignment constrains all occurrences sharing a source-owned binder. | Complete immediate/latent root interfaces; sharing and dynamic boundary conditions. Source rules choosing declaration-binder sharing are explicitly open at L112–114. `K,D` transport vocabulary does not specify another existential witness domain. |
| Coupled candidate Function, L942–995 | For fixed `rho,nu,f`: `forall x in ⟦A⟧`; then `forall c in CallCfg(f,x)`; then `forall (tau,o) in Beh_c(f,x)`; row check and `Return(v) ⇒ v in ⟦B⟧`. | Argument values; complete configurations from all compatible punctured contexts and other-free-variable environments; finite typed prefixes and returns. `CallCfg`'s projection includes context execution but has no displayed existential completion prefix. No witness binder appears in the candidate equation. |
| Typed core §6, L320–358, L396–423 | Synthesizes `(I,d,n)` under given `Gamma`; fresh inferred endpoints and source binders stay at generated positions. | Name copies `Gamma`; lambda creates `Value(Fun(P,Result(I_b)))`; application relates whole `Result(I_a)` to parameter interface. Fresh symbolic endpoint generation is not by itself a logical existential rule for latent membership. |
| Typed core §6, L469–499 | Admissible substitution/renaming preserves source tags, binder paths and `K,D`. Latent result is returned without recursive force. | Conditional skeleton transport and simulation, not complete endpoint satisfaction or latent witness-scope construction. |
| Typed core §9, L917–976 | `J_arg`, `J_body`, `J_call` use the same receiver/configuration and operation witness; suffix resumes in current state. | Complete producer `ExecuteCallable` image parameterized by argument carrier, environment, configuration. No new universal/existential binder ordering is stated. |
| Typed core §9, L1006–1083 | Signs propagate over supplied typed interfaces and shared recursive nodes. Same response/continuation witness correspondence and global `K,D` stay joint. | Returned values preserve direction; Function input reverses it. A path-sign witness is a classification derivation, not a future-use completion witness. |
| Typed core §9, L1087–1108 | At same `nu`: `D_checked ⊆ D_actual`; `forall d in D_checked`, `P_actual(d) ⊆ P_checked(d)`. Thus, for each `d`, every actual observation has checked membership. | `d` contains complete initial configuration/carrier and admitted future input history with shared dependencies. Set membership's internal hidden witnesses remain under their original scopes; inclusion states no exchange with `forall d`. |
| Theorem C §2.4, L178–188 and linking §3, L112–129 | Schematic `P_G(X)=exists Z.F_G(X,Z)` at original scopes. Linking gives the **example** `exists Z_shared. forall kappa_arm. exists Z_body.K`. | Shared/captured coordinates cannot move inside the arm universal. This example establishes the importance of the missing order; it is not the actual returned Function's binder tree. |

## Conditional expansion of the actual Function candidate

Hypotheses: use precisely the coupled candidate equation at L989–995;
interpret a returned type `B = A_1 ->[E_1] B_1` by that same equation; retain
its fixed `rho,nu` and independently supplied `CallCfg`/`Beh`. No production
adequacy or descriptor-reflection hypothesis is added.

For an outer returned value `v`, substitute the candidate into its result
conjunct. Its original order becomes:

```text
fixed rho,nu,f
  forall x in ⟦A_0⟧_(rho,nu)
    forall c in CallCfg_(rho,nu)(f,x)
      forall (tau,o) in Beh_(rho,nu,c)(f,x)
        supp_now(tau) subset TypedRow(E_0,nu)
        and, if o=Return(v):
          forall y in ⟦A_1⟧_(rho,nu)
            forall c' in CallCfg_(rho,nu)(v,y)
              forall (tau',o') in Beh_(rho,nu,c')(v,y)
                supp_now(tau') subset TypedRow(E_1,nu)
                and (o'=Return(v') implies v' in ⟦B_1⟧_(rho,nu)).
```

This follows by substitution into the result conjunct; neither quantifier
exchange nor a source-image argument is used. It checks **the same returned
`v`** under every admissible candidate future call, at the same assignment.
It is stronger than checking only future calls realized in one current
program. Its explicit tree has no `exists e` placed before or after those
universals. Hidden binders inside `⟦A_i⟧`, `CallCfg`, `Beh`, or the descriptor
interpretation are not exposed by this expansion.

Consequently, a formula requiring one new completion witness over all future
calls cannot be read off this displayed candidate. Nor can a formula choosing
independent completions per call be read off it. Universal semantic checking
of one `v` and globally binding every metatheoretic witness are different
statements. The original shared `nu` already stays fixed; it must not be
mistaken for an arbitrary new completion witness.

The candidate has an older evaluated-argument presentation, while approved
typed-core/inlet decisions require whole carriers. This derivation preserves
the candidate as written and labels its status. It does not use its argument
value domain to narrow the approved production challenge domain or select
its historical application equation.

## Minimum unresolved evidence and failure conditions

The missing input is one independently interpreted latent Function clause at
the actual returned provider, specifying the descriptor and old `(X,xi,w)`,
the universe of compatible future-use operands, and every additional witness
sort/dependency/scope. In particular it must state whether any completion
witness is shared across alternatives, retained only within one admitted
history, or event-local after a rigid binder. The rule's link to local
Return/lookup typing and future-use checks must then be proved, preserving
those scopes. Existing references cannot supply that tree by analogy.

For an Option 2 provider, the input must include all declared extra-member
and extra-provider future-use cases plus their independent domain evidence.
Returning `Der_ref` alone covers reference observations. Returning `G(y)`
alone assumes ordinary descriptor satisfaction. Returning a checker that
accepts supplied binders validates syntax against its inputs, not that those
binders are the source rules.

This bounded finding fails if an in-scope approved or governing source
already supplies that complete rule/tree and operand domain. Such a locator
would require a targeted revision. A change to an approved denotation/domain
decision, a dependency change in the audited windows, or an unaccounted
abstraction/admission arm also invalidates the corresponding row. Merely
larger finite probe ranges cannot settle an unspecified witness scope.

Recommended next action: have the descriptor-clause producer return that
single independent latent rule and its exact binder/domain tree for primary
adjudication, before instantiating an all-future witness-completion attack.

## Checks, coverage and resources

Commands used: bounded `rg`/`sed` navigation; pinned
`git show e8a05ef15a6f896af3041e1c10a32e76593f65f1:<path>` with `nl -ba`
section reads; `git rev-parse HEAD`; serial Python SHA-256 and byte comparison
of the 19 dependencies below against baseline, current HEAD and working bytes.
All 19 matched before writing; output path did not already exist. Initial
combined output was truncated; relevant semantic windows were reread in
bounded captures. This inventory covers the named windows, not a completed
repository-wide absence search.

No Oracle, semantic checker, executable experiment, mutation, random seed,
range enumeration, test, build, compiler edit, Git mutation or child launch
was used. Thus there are no execution-case counts or timeout claims. Sources
share local primitive, source-context and owner/view assumptions; their
agreement is documentary correspondence, not independent semantic evidence.
The conditional expansion establishes only the implication under its explicit
candidate hypotheses. No independent review of this producer's artifact is
claimed.

Reads and hashing used serial short-lived metadata processes; no heavyweight
process, output cache or temporary artifact was created. Aggregate CPU,
peak RSS and total wall time were not measured. Unverified scope: complete
production `DescMem`/admission, hidden operand denotations, arbitrary mutable
or opaque worlds, recursive-member adequacy, finite-failure reflection,
SEM_JOINT and REC-DESC. Only the leased note is changed.

## Frozen dependency hashes

SHA-256 over pinned blobs; no changed hashes observed at the pre-write check.

| Path | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `rules/question-board.md` | `8c617ceb978dfa26ce12f4f71ecc8ece22ffd8f1cf1982125b33142f645ae1c0` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-04-source-indexed-callback-realization.md` | `76874a219ac86068027b1f08a5bc27a12d93a0169a52cebd896a6ff6f2c6b671` |
| `notes/design/2026-10-01-coupled-effect-interface-core-draft.md` | `9eca7e45d1f0927397763481b0280bf54182408bd3c562aa2f6e80454f57ba3d` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` | `568bb4649ba278519f3ad01af2091dd1baaca42850cd19e3b5734b3c47c2eefe` |
| `notes/design/2026-10-02-parametric-component-linking.md` | `108fb9ab91c79aedc716ae476a07d567447644892ae1e32671c8fa4bce96efca` |
| `notes/progress/2026-10-07-rec-desc-latent-function-clause-audit.md` | `1e1be907e5d22576816cd6ac8f04c831b842150f95b0c58007250327af569b75` |
| `questions/2026-10-05-production-function-denotation/approved-answer.md` | `7e7f3c717b16a70fc754c930a1654666c8b61a89a4861fca27b0ae3fa5f1890a` |
| `questions/2026-10-05-production-function-denotation/receipt.md` | `8654359c41d2bf4871904d017d0282155d8763496986a3254405a1220318708b` |
| `questions/2026-10-05-production-function-bound-membership/approved-answer.md` | `d9ddea04a44d2307cf587bc4ae9b2a1c50d062c4077306a5bf9ea9da00eca179` |
| `questions/2026-10-05-production-function-bound-membership/receipt.md` | `f69a924b52e0cfb198df62a33e7e5c358ee1d0799ecf7c16cf32b9f8cb2f7e98` |
| `questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md` | `9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3` |
| `questions/2026-10-05-production-function-inlet-context-domain/receipt.md` | `a952c4588f6020ba1c51f69c623bf12ef695d73fe086496bf6ecdeee37450021` |
| `questions/2026-10-04-function-bound-value-observation/approved-answer.md` | `5a349fd0a87397372097701ca96b4dd45a0c37efb59a7e821eae53f3cddba22f` |
| `questions/2026-10-04-function-bound-value-observation/receipt.md` | `07df4adf651e4bfec25a80c52efc4a05064d327832d1bb1bcba58c39d45e4c57` |

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-07-rec-desc-binder-domain-audit.md`.
- Baseline SHA: `e8a05ef15a6f896af3041e1c10a32e76593f65f1`.
- Dependency hashes changed: none observed; 19 baseline/current/working comparisons passed before writing.
- Review status: frozen unreviewed bounded characterization and conditional candidate derivation; no independent review or gate closure.
- Checks already run: assigned pinned sections and serial dependency byte/hash checks; no builds/tests/experiments. Primary owns final lease/diff and dependency revalidation.
- Proposed one-line research-checkpoint commit message: `research: inventory returned Function binders and operand domains`.
- Shared-record deltas left to primary/curator: if accepted, distinguish the candidate's nested universal Return obligation from the unspecified production latent witness tree; retain DESC_CLAUSES, ADMISSION_CLAUSES, SEM_JOINT and REC-DESC open; request the single independent latent clause/tree before a joint-completion probe. No shared record, authority file or question bundle was edited.

Writes stop at submission for frozen review.

## Independent review

The compiler-referee confirmed the candidate Function quantifier expansion
and the narrower claim that the audited clauses preserve supplied scopes but
do not supply the production latent-Function binder tree. No blocking, major
or minor findings. The review does not claim repository-wide absence, baseline
provenance, hidden-denotation coverage or production/FH/REC-DESC closure.
