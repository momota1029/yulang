# ORIGINAL_ASSOC P2: constructor input reduction

Status: compiler-referee-reviewed research-only premise-gap localization
Gate/method: ORIGINAL_ASSOC P2 / constructive dependency reduction
Baseline: `df1b80af6ad3c40cc08feea28acea0def65b30aa`, pinned by the primary
Write lease: this file only
Implementation authority: none

## Objective and result

Try to construct the original static `beta`/`Slots(beta)`, typed output
position `p0`, slot/owner and complete-contribution introduction from the
approved declarations, definitions and uses of exactly
`my apply f = { my step x = f x; step }`. Hold original `X`, source scopes,
providers and one `xi=(nu,K,D)` fixed. Formation must precede and be independent
of the pending comparison `Q`.

Result: a **bounded irreducible input gap for this constructive route**.
Granting complete Call descriptor typing removes P1 as the immediate stop,
but does not discharge the independently interpreted owner/view kernel input
of source-contracts §2.1. The available source constructors synthesize
interfaces and complete constructor images; they do not supply the original
kernel interpretation connecting those interfaces to static slot ownership
and a complete contribution. C-realization consumes that interpretation.
It cannot be used to construct its own input.

This is neither a nonderivability theorem about Yulang nor an admitted source
counterexample. It selects no denotation, slot count, coverage assembly or
licensing rule. ORIGINAL_ASSOC and its downstream gates remain open. The
precise blocker agrees with the retained candidate's P2 cut; this note makes
the constructor dependency explicit rather than claiming another closed gate.

## Baseline, authority and hypotheses

Governing reads: FVIEW §§1.1–5; source-contracts §§2.1, 3.2, 3.5, 6.1,
8–10; typed-core §§6/9; DAG ORIGINAL_ASSOC/ATTACH/LIC_FORWARD/LIC_INVERT;
and the reviewed original-Call kernel-contract candidate. The nested-block
addendum §§1–4 fixes the exact source interpretation. The directional
addendum §§1–4 records the current user decision. Draft typed-core and
source-contract clauses retain their stated conditional status.

| Class | Exact premise used |
| --- | --- |
| Established user decisions | Sequential local binding; final `step` returns the function value; body `f` resolves to the outer formal and `x` to the inner formal; later calls retain that same outer capture. One shared inferred source component and original scopes/constraints; actual callable roles/entries remain distinct from internal inferred views. |
| Established formation direction | `beta`/`Slots(beta)`, paths and owner/receiver relations must originate in source resolution/typed elaboration and survive transport. FVIEW §2 expressly leaves their exact generating judgments open. This requirement is not treated as an implemented introduction rule. |
| Established protection direction | Given `ProtectedVarAt(k,v,sigma,u)` and `SourceUpperUse(u,v,U,sigma)`, seed only the upper `outEff(U)`. Keep existing provider protection; do not back-propagate the new seed. This conclusion is a protection fact, not slot or contribution inhabitation. |
| Conditional source input Hlex | The original lexical/declaration interfaces and their typing premises are supplied to typed-core §6; source tags and capture references are preserved. Raw-source inference of arbitrary interfaces is not assumed. |
| Candidate assumption Hcall | Independently admitted operand/world assignments satisfy the complete local Call descriptor typing law, including returns, pending prefixes, compatible resumption extensions and future uses, at the original scopes and shared `xi`. Hcall does not consume association, attachment, licensing or `Q` success. It is granted only to isolate P2, not proved here. |
| Missing input Hkernel | Independently specified original owner/view-kernel contracts, including the meaning and typed introduction of original static slots, output positions and complete contributions and their joint incidence. No fresh replacement interpretation is supplied. |

The approved answer/receipt files were read as the primary's accepted decision
dependencies. No question bundle was edited or newly integrated. Their hashes
are recorded below; baseline byte equality remains the primary's integration
check because the packet forbids this worker's Git operations.

## Constructive reduction with P1 granted

Resolve binders `d_f,d_x,d_step` and body uses `u_f,u_x`. These names designate
source objects. They are not semantic slots or contributions. Relative to
Hlex and the §6 ordinary-parameter rules:

```text
Gamma(d_f) = Value(A_f)       Gamma(d_x) = Value(A_x)
n_f = result(name f)         n_x = result(name x)
n_fx = call(n_f,n_x)
I_fx = Computation(E_fx,A_fx)
```

The approved enclosing correspondence is:

```text
lambda(f,
  bind(step,
    result(lambda(x,n_fx)),
    result(name step)))
```

Returning this closure preserves the captured source root without invoking
the latent body. Application endpoints remain symbolic and constrained by the
complete Call relation. A Function-shaped constraint is a use demand; solving
it is not used to create ownership or receipt evidence.

Keep the complete Call equation distinct from receiver invocation:

```text
J_complete = J_f >>= ((actual_f,C) =>
    ExecuteCallable_X(actual_f,Delay(J_x),C))
```

The equation retains callee evaluation, inert argument, actual provider/entry,
receiver/receipt, body, designated consumer and pending suffixes. At this
source-base Name/Name cut, adequate lookup gives returning operands; that
simplification does not type all conservative production alternatives. Hcall
conditionally supplies complete descriptor typing independently of P2.

The following table is a dependency check of proposed constructor terms.
It introduces no new semantic judgments or source rules.

| Available constructed object | Proposed P2 use | Exact unmet obligation |
| --- | --- | --- |
| Resolved formal `d_f`, capture `u_f`, shared contract locator | Construct original `beta` and a member of `Slots(beta)` | Supply the original interpretation of this position/contract and its introduction into the existing inventory. A locator pair is not a demonstrated inhabitant of that original sort. FVIEW fixes provenance/persistence, not this constructor. |
| Symbolic `E_fx,A_fx` and upper `outEff(U)` occurrence | Construct independently typed original `p0` | Establish the original complete output view and its typed position correspondence. A value/effect endpoint or a protected upper occurrence does not supply that correspondence by identity. |
| Captured provider root and actual receiver links | Introduce original static slot ownership | Show how the original kernel relates this source ownership to its static slot. Actual receiver activation and lexical ownership cannot be substituted for that rule. |
| Hcall-typed `J_complete` | Introduce original complete contribution `c` | Interpret the original contribution sort and introduce an object of it from the complete constructor certificate. Descriptor typing of the relation image is not a coercion into the unspecified contribution sort. |
| All preceding objects at one `X/xi` | Introduce their original incidence | Apply the original joint introduction with original dependencies. Shared coordinates alone do not prove incident ownership; separately inhabited projections cannot be recombined by decree. |

Consequently the derivation reaches a typed Call interface under Hcall, not
an original slot/contribution witness. No equation `s=p0` or `c=J_complete`
is used. The original `beta,p0` are requirements of the output, not newly
chosen inputs quietly declared inhabited. No row union, fresh tuple or
per-call inventory supplies their interpretation.

## Why C-realization and allowance coverage cannot finish this route

Source-contracts §2.1 explicitly puts independently typed primitive and
owner/view-kernel contracts in its **input**. Section 3.5 then assumes §2,
local descriptor typing and the finite emission/transport certificate before
proving source-base correspondence. Its primitive induction case reuses the
same supplied local witness. It preserves that witness instead of producing
the missing interpretation from the Name or Call label.

The exact dependency reduction is:

```text
Hlex                         -> result/consumer skeleton
Hlex + Hcall                 -> conditionally descriptor-typed complete Call
Hkernel + local typing
  + emission/transport cert  -> C-realization correspondence
```

Using the third line to obtain Hkernel requires assuming the disputed input.
This is an input-cycle diagnosis, not a proof that an original constructor
cannot exist elsewhere. Generic conjunction, union, renaming, binding or
constructor-image clauses require their whole-tuple interpretations; they
provide no independently interpreted owner kernel merely by being named.

Section 6.1 does not repair the cycle. Its independent validity derivation
**retains** the whole non-coverage kernel and original binders. Its Call
clause constrains coverage of the callee and complete receiver allowances;
it does not introduce the retained kernel. Allowance coverage therefore
cannot initialize the missing static slot/owner/contribution interpretation.
Sections 8–10 preserve source applicability and unselected-rule boundaries.

Even if Hkernel's separately sorted objects were later supplied, P3 would
still have to establish the existing uniform complete-family witness target.
This note does not infer it from pointwise coverage. P4 licensing and its
exhaustive inverse remain separate, unexamined obligations.

## Independence, exclusions and next falsifier

No executable oracle or Frozen Oracle source was used. The reference consists
of the selected governing text, shared with the primary and other lanes.
Hlex and hypothetical Hcall are shared assumptions, not independent semantic
validation. There was no executable experiment, enumeration, random seed,
range, mutation run or semantic checker. A checker receiving Hkernel as its
transition rules would test consistency relative to that input and leave P2
untouched.

Failure conditions for a proposed completion: it uses `Q` success or solved
shape to introduce an object; replaces original slot/contribution sorts;
equates source locators/endpoints with semantic positions; chooses independent
`xi` per arm; drops callee/pending/future-use content; changes captured
provider identity; or obtains Hkernel from C-realization after assuming it.
Any such completion fails this constructive route's stated premise boundary.

Unverified: actual Hcall, full source/profile/row generation, P3 coverage
assembly, exhaustive P4 licensing, mixed/generalized/recursive components,
annotations beyond the selected decisions, arbitrary world/admission clauses,
production parser/HIR/compiler conformance, soundness and principality. The
bounded reads do not establish repository-wide absence of an introduction.
Initial large captures truncated; decisive source-contracts, typed-core and
DAG sections were subsequently read in narrow windows. No search shard or
computation timed out.

Recommended next action / next falsifier: supply one pinned original
owner/view-kernel introduction or an independently proved source-to-kernel
correspondence whose premises are dischargeable from this Hlex/Hcall source
cut, and whose conclusion constructs the original slot, typed output position
and complete contribution jointly at unchanged scopes/`xi`. Showing that rule
and discharging its premises falsifies this local stop. Another preservation
lemma or transition probe assuming Hkernel does not. Return any missing
semantic choice to the primary; do not reopen the approved source meaning.

## Checks, resources and frozen dependencies

Checks: bounded `cat`, `sed -n`, `rg`/`rg --files` source reads; Python
`hashlib.sha256` dependency capture and handoff recheck; note-local path,
whitespace and hash-table integrity checks. No Git commands, tests/builds,
formatters, children, compiler edits or scratch outputs. Only the leased note
was written. Up to five short read processes were batched once; all remaining
calculations were single short processes. No heavyweight process ran.

No numerical CPU/RAM/wall-time limit was supplied in the packet. Process CPU,
peak RSS and total wall time were not instrumented. There was no iterative
compute search and no incomplete range. Dependency hashes were captured
before writing and must be unchanged at handoff. The primary-pinned commit
was not independently resolved by this worker.

| Direct dependency | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `rules/question-board.md` | `8c617ceb978dfa26ce12f4f71ecc8ece22ffd8f1cf1982125b33142f645ae1c0` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/theory/successor-proof-obligations.md` | `18bfa4e5bb461616ca17a0c9a1492f75ff7fca2f6231a13b3d68e0a3335136dc` |
| `notes/progress/2026-10-08-original-call-kernel-contract-candidate.md` | `b401a3331ab96eb2668fd7d9bb7ec9488482c0550570f24ab3c29e071320246f` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| `questions/2026-10-05-nested-block-function-source-realization/approved-answer.md` | `04ee0dc089dc6ad19a184d31775a146c08b07f2f287099d2e5b54d7d1d5a643e` |
| `questions/2026-10-05-nested-block-function-source-realization/receipt.md` | `e5e59e176eb865a588b2843b18137571fe9c5b6f43bf1ca349bc60c9ad90f0ec` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-09-original-assoc-p2-constructor-attack.md`.
- Baseline SHA: `df1b80af6ad3c40cc08feea28acea0def65b30aa` (primary-pinned).
- Changed dependency hashes: none expected; handoff verifies the table above.
- Review status: bounded P2 input reduction; compiler-referee PASS on the
  semantic content at SHA-256
  `1a031d35e7ee8dcb898856eddf8ec08d58893b2d63137d6844504d707961ce24`;
  review does not establish semantic adoption or gate closure.
- Checks already run: governing-section reads, dependency SHA-256 capture;
  final dependency equality and note integrity checks reported at handoff.
  No tests, builds, executable semantic checks or Git operations.
- Proposed one-line research-checkpoint commit message:
  `research: localize original association P2 constructor input gap`.
- Shared-record deltas intentionally left for primary/curator: optionally
  record the C-realization/allowance retained-kernel input cycle under the
  existing P2 frontier. No new DAG edge, status promotion, task/index edit,
  question bundle change or authoritative rule is proposed.

Producer writes stop before artifact submission for frozen review.
