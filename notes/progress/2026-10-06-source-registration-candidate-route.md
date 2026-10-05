# Source registration: candidate association constructor

Date: 2026-10-06
Status: Non-authoritative research candidate; independently reviewed with no findings
Baseline: `3946e2592a27e5f1436da1114b7625870ffeed34`
Branch supplied by primary: `research/simple-sub-intrusion`
Exclusive lease: this file only
Method: constructive rule proposal with classified premises; static analysis only
Implementation authority: none

## Objective, result and authority limit

Propose the first association-producing judgment for the exact source

```text
my apply f = { my step x = f x; step }
```

The proposal allocates one **symbolic association** for the resolved formal,
its captured use and its call constraint. It separates that construction
from validation of its position/profile, typed incidence and interpretation.
It never installs a completed Function type in `Gamma`. This changes method
from the reviewed attempts' last-rule analysis: the first constructor is
explicitly new, rather than another application of a preservation rule.

Current authority permits proposing this rule, not deriving it as an
established Yulang source rule. Inferred-call-view §§1.1–5 selects the
formation direction and preserves the open rules/proofs. The Authoritative
nested-block addendum §§2–4 fixes this candidate's lexical meaning and
structural core correspondence, while leaving registration and typed capture
open. Typed-core §§6,9 is conditional Draft machinery. Source-contract
§§2.2,3.1–3.5 is a Reviewed conditional package with concrete clauses Draft.
The theorem map is navigation, not another premise.

Claim classes here are: approved lexical facts; a conditional ordinary
constraint skeleton; a candidate registration rule; and a conditional
bookkeeping lemma for that proposed rule. No source-registration theorem,
soundness, principality, source adequacy, production acceptance or gate
closure is claimed.

## 1. Premises and the proposed output

Use proof labels `b_f,b_x` for resolved formals, `l` for the local closure,
`u_f,u_x` for its body names, `c` for `f x`, and `p_f` for an original source
position to be selected by a position certificate. `p_f` is not defined to
be a binder label, call label or byte range. Let `C` contain this exact
resolved candidate; taking its two definitions, captured use and call as
one research component is a candidate component choice, not a general
component-selection or local-polymorphism policy.

Every input used below has one of these classes:

| ID | Premise | Class / source |
| --- | --- | --- |
| L1 | Sequential binding; final `step` returns the function without calling it | Approved lexical/structural fact: addendum §2 |
| L2 | `resolve(u_f)=b_f`, `resolve(u_x)=b_x`; `l` retains that outer `b_f` | Approved lexical fact: addendum §2 |
| L3 | The displayed formals have no written annotation | Source syntax fact; annotation absence is distinct from an empty effect row |
| S1 | The selected structure is represented by the finite ordinary core graph; ordinary parameters generate `Value(A_f),Value(A_x)` | Conditional derivable source skeleton: typed-core §6 with admitted ordinary elaboration; no current production-acceptance claim |
| S2 | Name endpoints reuse `A_f,A_x`; the call generates a callee Function obligation, whole argument `Comp(empty,A_x)` and complete-call endpoints `E_c,A_c` | Conditional derivable source constraints: typed-core §§6,9; generated obligations are not typed certificates |
| U1 | An original logical binder/scope plan and one jointly scoped `xi=(nu,K,D)` for all retained operands | Unresolved supplied certificate; lexical nesting alone is not its proof |
| U2 | `PositionInventory(C,p_f,Phi_f)` yields original `beta,Slots(beta)` with position, annotation presence, scope and role-selected port inventory retained | Unresolved supplied certificate; no concrete identity/inventory rule is selected |
| U3 | Local constructor typing establishes the resolved name and captured operand at their admitted typed positions, including owner/receipt/consumer references and typed correspondence | Unresolved supplied certificate; lexical retention supplies no typed `Flow` or receiver relation |
| U4 | A local contract/protection interpretation relates the symbolic call constraints and the provisional seed to one inferred interface, preserving actual role/entry | Unresolved supplied certificate; exact seed/discharge and protection rules remain open |
| U5 | The emitted provider/admission clauses are active on the same whole tuple and original incidences, with local descriptor typing | Unresolved supplied certificate: source-contract §2.2 and constructor typing; explanatory links do not suffice |

`U1` must not be built by selecting a separate `nu,K,D` witness for each port.
`U2` must exhibit its position-to-contract mapping rather than assume a whole
`Reg` conclusion. `U3` must prove local operand typing from the source/kernel
premises; naming a capture edge is insufficient. `U4` must provide the exact
role/protection rules, not assume that the pending Function comparison works.
`U5` must identify the clauses and their interpretation, not assume
soundness of this new registration rule. All five certificates remain open.
Their decomposition makes the missing work visible; it supplies no proof
that the certificates exist or are mutually consistent.

The output distinguishes a proposal `J?` from a validated symbolic
association `J`. Both use a symbolic role-indexed contract family `Phi_f`
and relation root reference `R_f`; neither is a solved/public type.
`Phi_f`'s index describes internal inferred role alternatives. Actual callable
role and entry are separate operands interpreted at the original provider;
the provisional Handler seed cannot rewrite them.

## 2. First constructor: association with open obligations

The following rule is a **new research choice**, written in proof notation,
not a compiler representation, source type constructor or runtime object:

```text
L1–L3; S1–S2; all references are in the one resolved candidate C
---------------------------------------------------------------- PROPOSE
C |- J? = associate(
  fresh R_f, fresh symbolic role-indexed Phi_f,
  formal=b_f, use=u_f, call=c, capture=(l,b_f),
  constraints=CallObligation(A_f, Comp(empty,A_x), E_c,A_c),
  position/profile holes governed by PositionInventory(C,p_f,Phi_f),
  pending U1,U2,U3,U4,U5)
```

Freshness here allocates metatheoretic names for constrained presentation
references. It does not add existential source types, solve an endpoint or
certify a descriptor. `Gamma` retains `Value(A_f)` and `Value(A_x)` only.
The association is stored outside that ordinary interface premise, as a
proposed constrained relation over those endpoints.

One `R_f,Phi_f` is referenced by the formal, use and capture operands.
The proposal connects them because L2 resolves them to the same formal;
sharing the eventual inferred contract is the approved target. The new
choice is to realize that target by preallocating one symbolic association
and retaining unsolved obligations. It does not assert that every lexical
alias or generalized occurrence may reuse an unchanged instance; that
requires certified use/generalization and is outside this component.

The position/profile holes are not already certified `beta,Slots(beta)`.
Calling an opaque hole `beta` does not construct its original inventory.
No full-profile source-contract or transport theorem may consume `J?`.
Its legitimate consequence is the finite, explicitly shared constraint
proposal and its list of missing certificates.

## 3. Validation into a symbolic source association

A possible second rule is also a **new research choice**:

```text
J?; U1; U2; U3; U4; U5, checked on the same original operands
-------------------------------------------------------------- REGISTER
C; xi |- J(R_f,Phi_f,beta,Slots(beta),typed incidences,clauses)
```

`REGISTER` introduces the first certified provider/contract/profile
association. U2 supplies the position and inventory; U3 supplies typed
operands; the rule attaches them to the single symbolic contract/root.
The incoming certificates must not already assume that full association or
its soundness. If they do, this is merely a factorization of an assumed
decorated input and does not cross the source-formation cut.

The intended local provider clause is schematically

```text
FormalProvider(b_f,p; eta) and ContractObligations(p,Phi_f; xi)
```

`eta` denotes a lexical valuation in proof notation, distinct from `nu`.
The candidate interpretation of `FormalProvider` is `p=eta(b_f)`, refined
to an admitted callable provider by the independent local typing/contract
certificate. Equating the ordinary endpoint with a callable shape is not
that certificate. U5 must validate this clause against the original
provider/descriptor kernel; its semantic validity is not inferred from the
existence of the proposed root name.

For a returned closure instance `s`, the intended capture operand is
`eta_s(b_f)`, with `eta_s` the valuation it actually retained. L2 fixes the
same source binding across later calls; U3 must lift that fact to a typed
capture correspondence. A static `R_f` describes the symbolic formal
relationship, not a single provider shared by different outer invocations.
The candidate makes no provider equality between different `eta_s` values
and no claim that the outer receiver remains active after return.

U4 records unannotated `f`'s provisional protected Handler view as internal
inference state of this same `Phi_f`. It must retain full protection without
equating it to empty support. This note adds a pending
`NonHandlerFormal(C,b_f,u_f,c)` obligation, not a derivation of it from
`Value(A_x)` alone. The approved direction requires ordinary-value evidence
to discharge the seed, but the eligibility, aggregation and discharge rule
is not supplied here. A generic `Value => NonHandler/Pure` is inadmissible.

For this candidate U2/U4 retain annotation absence. Any annotated extension
requires a separately proved occurrence-to-original-port clause and scoped
permission/protection interpretation. In particular `[io]` would permit
removal of its specified contribution; it would neither require removal nor
authorize row subtraction of unrelated effects. This note constructs no
annotated variant and no projection to a printed public scheme.

The complete-call constraint retains the §9 `J_arg`/entry/body/consumer/
return dependence. It cannot substitute pure name lookup for `J_call`, infer
callee entry from the supplied value argument, or define call effects by
unconditional row union. Source-contract §§3.1–3.2 emission can use `J` only
after its decorated-input, local typing and clause obligations are met.
Complete initial/future admission is still separate (§3.3); `REGISTER`
does not manufacture a receipt, a live receiver or admitted future history.

## 4. Conditional derivation and outstanding proofs

Under L1–L3 and S1–S2, `PROPOSE` gives one root with the edges

```text
b_f -> (R_f,Phi_f) <- u_f/c
l's retained b_f operand -> (R_f,Phi_f)
```

These arrows are candidate association references, not typed `Flow`, runtime
authority or a solved equality of all endpoint observations. Under U1–U5,
`REGISTER` would link that root to the original `beta/Slots(beta)` and
typed provider operands. This is a conditional derivation **in the proposed
rules**, not evidence that approved source rules already derive U1–U5.

Conditional bookkeeping lemma: fix C, S1–S2, the original scope plan and
all position/typing/protection certificates. Assume `associate` allocates
one fresh root/family per this component and consistently references it;
assume the certificate outputs are fixed up to one legal joint renaming.
Then the proposed association graph is unique up to that renaming and does
not depend on pending comparison `Q`. Proof: its three incidences are fixed
by L2, its constraint operands by S2, and its profile/scope operands by the
fixed certificates; root names are the only allocation choice. Neither rule
has Q as an input. This proves conditional bookkeeping coherence, not
uniqueness/principality of solutions or Q-independence of an as-yet-unspecified
certificate producer.

The following obligations are not consequences of that lemma:

1. **Rule soundness:** derive U1–U5 from source/kernel rules without an
   incoming registration assumption; prove the formal-provider and capture
   clauses preserve complete entry/call behavior and active constrained-root
   membership. Preserve origin, guard, binder scope and operation witnesses.
2. **Principality:** show component formation and the role/protection rules
   neither lose legal views nor invent solutions; establish the required
   all-view quantifiers for the completed constrained interface. A unique
   allocated graph or constraint list is insufficient.
3. **Identity and lifecycle:** prove original position/annotation/scope
   retention through joint freshening, lawful graft/hiding and use-time
   instantiation (§3.4). No local-polymorphism or recursive-component rule
   is selected here; recursive origin/guard obligations cannot be erased.
4. **Source adequacy:** prove translation from the exact source interpretation
   to these registered clauses and back for the stated envelope, with local
   descriptor typing, exhaustive source emission and independent admission
   (§3.5). Literal source acceptance by current HIR remains unverified.
5. **B and production:** preserve normative literal B when an expected
   callback context is present, its boundary before body synthesis and one
   completed inequality; preserve supplied actual role/entry. Prove separate
   Option A/Option 2 production admission/membership and whole-domain
   containment, including production observations without source witnesses.
   No schedule optimization or source-tight production policy follows here.

## 5. Discriminators, coverage and stopping condition

The useful discriminator is whether the proposed `REGISTER` has local
certificate derivations whose first introduction is independent of `Reg`.
Supplying the full decorated association under another name fails that
discriminator. The current result makes this test explicit but does not pass
it: U1–U5 remain open.

Reasoned proof mutations, not executable tests: delete U2 and the conclusion
has no certified position/profile; replace U3 by L2 and typed capture is
unsupported; turn the provisional role seed into actual provider role and
actual callable identity is changed; allow per-port witnesses and joint xi
is lost; allow Q to choose a certificate and the dependency lemma's hypothesis
fails. These are rule-premise discriminators, not accepted-source runtime
counterexamples or alternative language meanings.

There is no executable oracle. Approved source meaning is independent of the
candidate constructor; the conditional core/contract consequences share
supplied typing/kernel assumptions. A checker executing `PROPOSE/REGISTER`
with assumed U1–U5 would establish only consistency of those supplied rules.
It would not prove their source validity. No seeds, ranges, random samples,
enumeration, implementation, tests, builds or formatting were used.

Coverage is this exact finite candidate and the named sections. Previous
reviewed attempts establish the open formation cut; their independent review
does not certify this new proposal. No whole-repository rule-absence search
is claimed. Stop here: a further toy graph would leave U1–U5 untouched.
Recommended next action is review of this candidate interface, concentrating
on whether U2's position/inventory constructor and U3's local operand typing
can be grounded without assuming the association they are meant to produce.

## Independent review

`compiler_referee` reviewed the frozen proposal against the declared source
formation, nested-block, typed-core and source-contract sections and found no
blocking, major or minor issue. The review confirms that `PROPOSE` carries
only symbolic references and pending obligations, U1–U5 remain unproved,
and the bookkeeping/Q-independence result is conditional on fixed certificate
outputs. The proposal does not derive registration, source validity,
principality, soundness or adequacy; those remain open.

## Dependencies, checks and resources

All semantic dependency bytes matched the pinned baseline before writing.
The governing sections and decisive prior-attempt passages were reread in
bounded captures after initial combined tool output was truncated. Navigation
reads: current task, laboratory startup seed and design index. Concurrent
HIR/solver edits were observed and excluded from inputs and writes.

Baseline whole-file SHA-256:

| Path | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/progress/2026-10-06-captured-provider-registration-constructive-attempt.md` | `faa91b04050437bccad0d57a0f19e5c0f42b8cf64df207896470a7f49eddc4ec` |
| `notes/progress/2026-10-06-captured-provider-registration-falsification.md` | `c64879a92c2f6b33a6fb771b9dd9395f47f6e6648d6edd1afd660c9b392435aa` |
| `notes/theory/inference-theorem-dependencies.md` | `83540b894df0f9c7d0b523f192be6fd46d85124009982f6588cad25cd16c65fd` |

Commands/checks: read-only `git rev-parse`, `git status`, `git show`; bounded
`cat`, `sed`, `rg`; sequential Python SHA-256/baseline-byte comparisons;
leased `apply_patch`; final dependency/lease/whitespace inspection.
No numerical wall-time/CPU/RAM cap was supplied; static work only, at most
three lightweight command calls overlapped. CPU time, peak RSS and total
wall time were not measured. Zero heavyweight processes, tests/builds,
children, Git mutations, question-board writes or shared-file edits.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-source-registration-candidate-route.md`.
- Baseline SHA: `3946e2592a27e5f1436da1114b7625870ffeed34`.
- Changed dependency hashes: none consumed; snapshot above.
- Review status: independently reviewed non-authoritative candidate; no gate closure.
- Checks already run: exact-section and premise classification; baseline/live
  equality and hashes; absent output before creation; final narrow scope,
  whitespace and dependency inspection. No tests/builds.
- Proposed one-line research-checkpoint commit message:
  `research: propose suspended source registration association`.
- Shared-record deltas intentionally left for primary/curator: link this
  candidate as an unreviewed constructive route; retain the missing U1–U5
  producer proofs and all registration, protection, principality, adequacy,
  production and lifecycle gates as open. No theorem edge or design status is
  promoted; no task/index/authority/question-board file was changed.
