# c1 raw Application: rule inversion and transport obstruction

Date: 2026-10-13
Status: frozen independently reviewed research checkpoint; bounded documentary characterization
Reviewed-by: independent spec_auditor; PASS, no findings
Baseline: `beceb0bc91b35e84b4f62b353fc6c2abf18e0414`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file only
Method: independent rule inversion of the pinned constructors; no constructive proof delegation, compiler edits, tests, builds, probes or measurements
Requested role/model: researcher; no model override requested. Observed role contract: researcher instructions present. Effective runtime model/effort metadata is unavailable; configuration is not execution evidence.

## Objective and result

Test whether typed-core §6's generic Application row supplies the authentic c1 Call and native-to-source transport required by [the active-root construction frontier](../theory/2026-10-13-active-root-call-source-construction.md) §§1,3,5.

**Result:** the row supports a conditional result/consumer skeleton for c1. Its callee need not be a formal parameter. It does not supply c1's complete Application/check/reification origins or a legal whole-map action interpreting the native demand, extrusion pairs and qualified equalities. Promotion from that skeleton to complete source formation or g-frame transport lacks a rule premise. This is missing constructor evidence, not a language rejection or a source-qualified preservation counterexample. The parent A/B obligations remain OPEN.

## Exact authority and hypotheses

| Governing source | Exact scope used |
| --- | --- |
| [Inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md) §§1–5 | Preserve native generation, accumulation, propagation, levels, extrusion and generalization; proof convenience supplies no ordinary-source restriction. |
| [Charter](../design/2026-09-29-scc-intrusion-redesign-charter.md) §§13–21, with §24's narrow receiver-role supersession | Typed-path transport; inert whole argument; actual receiver entry; result forwarding; unannotated x/y/z have Value parameters. §24 preserves entry mechanics while withdrawing universal handler classification. |
| [LocalSelfRec](../design/2026-10-10-local-self-recursive-binding.md), Selected source behavior / Proposed source-to-solver seam / Required invariants | c1 refers to f's one active open monomorphic root, including from nested g. Adjacent bindings remain sequential; installation follows initializer formation. |
| [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md), header, §§2,6,9 | Draft finite derivation construction; §6 uses known lexical/declaration interfaces and existing complete invocation constraints. It does not establish arbitrary recursive inference. |
| [Call-input](../theory/2026-10-07-call-input-construction-proof.md) §§3–3.4,4 | Static binding certificates, Capture-Lambda, Data-Name and Code-Result; Code-Call consumes actual complete Application origins and original suffix ports. |
| [Source-Generalize selection](../design/2026-10-08-source-generalize-definition.md) §§2–3, selecting [construction](../theory/2026-10-08-source-generalize-definition-and-proof.md) §§2–5 | L1–L5 remain genuine local premises. Owning-rule records, original binder tree, publication component and complete N_g are inputs to the fixed walk and allocation. |
| [IF selection](../design/2026-10-08-call-source-interface-definition.md) §§2–4 and [construction](../theory/2026-10-08-call-source-interface-construction.md) §§3.1–3.2,5–6 | Registered declared telescopes, actual clause insertion and actual typed reference substitution; finite cycles need no unfolding. Original complete operator semantics and lawful whole-map actions remain inputs. |
| [Native recursive selection](../design/2026-10-08-native-recursive-interface-definition.md) §§1–2 | Exact simultaneous two-closure pair; explicitly does not adopt the wider Draft typed core or supply this nested recursive initializer's L4 introduction. |
| [Occurrence qualification](../design/2026-10-12-intrusion-value-type-association.md), Approved extrusion-event qualification / Definition-root origin / Qualification | Actual c1 extrusion has origin G, receiver F and all actual pairs; qualifies C=B,D=R. This fixes the operation, not equality preservation or source-coordinate transport. |
| [Copied-row ownership](../design/2026-10-12-value-reference-copied-row-ownership.md), Decision / Scope | Copying descriptions supplies no new Value-reference incidence. |

Shared assumptions are the fixed resolved source and accepted native history in the active-root note, plus these selected decisions at their actual scopes. Authentic complete Call formation, source classification of native operands and successful recursive introduction are conclusions sought, not assumptions granted. No Role_0 seed, imported formal-f contract, C description declaration, equality-placement convention or hypothetical K_g is assumed.

## Smallest diagnostic site in the unchanged source

```text
let rec f = lambda x.
  let g = lambda y. (lambda z. y) (f y)
  in {a = succ (g 0), b = g true}
in f
```

c1 is `App(Name(f),Name(y))`. c2 is the wrapper application whose whole argument is `Delay(code(c1))`. All original binders, Calls, record fields and checking boundaries remain. The diagnostic site is c1's rule application, not a minimized replacement program. No subtree is discarded because z ignores its rebound value: z has Value entry and forces c2's delayed argument before its body, conditional on actual execution reaching that entry. No termination or return premise is added.

### 1. What the generic Application row really constructs

Given authentic registration and lexical interfaces, `Gamma(f)=Value(A_f)` denotes the same active root o and `Gamma(y)=Value(B)` denotes the original y binding after its entry rebind. LocalSelfRec and Call-input's static Name/capture rules support those references. Charter §21 gives y its ordinary Value role; it does not give recursive f a formal-parameter role.

Typed-core §6 then has this conditional skeleton:

```text
Name f -> result(name f)
Name y -> result(name y)
Application c1 -> Computation(E_c1,A_c1)
                 reify(call(n_f,n_y))
Normalize -> designated consumption of that complete result interface
```

The row leaves E_c1,A_c1 constrained by the existing complete invocation relation, the whole argument contract and typed paths. Its own “Structural rules” and “Coherence” clauses explicitly retain those premises. It has no syntactic restriction to `apply`'s unannotated formal f, so that restriction would be an invalid falsification. Conversely, charter §21's pointer to the role construction removes only the ordinary parameter-role premise; it does not adopt raw recursive elaboration or independently form complete Call origins. Draft status alone also cannot invalidate the narrowly selected Call/IF constructors.

### 2. First unavailable formation application

Call-input §3.4 Code-Call requires, beyond the two child Code-Result certificates:

```text
actual Application/Gen-Call-0 origin(c1,F_c1,R_f),
actual whole-argument ReifyOrigin(c1,Name y,r_arg,Comp(empty,B),scope,incidences),
original complete result Comp(E_c1,A_c1) and result port,
emitted VIncl-origin(A_f,F_c1),
emitted WholeArgCompatible-origin(J_arg,CarrierContract(F_c1)),
original actual-provider receiver/entry/body/consumer/return suffix schema.
```

The generic row's result-role declaration is not an origin for those premises. Bare Gen-Call-0 is explicitly insufficient in the same section. Thus the concrete mismatch is **using a synthesis-row conclusion as the complete Application premise of Code-Call**. These are formation records, not solved membership, so demanding them does not require eager satisfiability at generation time.

The owning seam is c1's source Application/Call emission, including original parameter, receiver and result introductions. Static registered-root references are available; complete recursive semantic introduction still needs the original L4 instance separately. The exact two-closure theorem cannot supply that instance for this source by renaming its binders.

## Native tuple and g-frame transport attack

Grant the full c1 Application records hypothetically. A second obstruction survives. The accepted native history supplies

```text
o <: Function(B,R)
extrusion: (C,B,+,1), (D,R,-,1)
B <: C, D <: R, o <: Function(C,D)
qualified operation: C=B, D=R
```

It does not identify these scalar operands with the full dependent source clause's fields. In particular, a native Function result coordinate cannot be silently equated with a closure body/result port: Call-input §3.3–3.4 and typed-core §9 distinguish body, native delimiter, complete invocation and future-result fields.

The first missing **transport introduction/map** is the actual source interpretation of c1's native demand/extrusion occurrence: original incidence and telescope for o,B,R,C,D, the complete clause affected by C=B,D=R, and a lawful action on its dependent carrier, world, provider, receipt, result/future, witness and pending-suffix fields. C need not be Desc; its introduction/incidence can be another lawful source coordinate. Neither level 1 nor storage on o, SCC membership nor a row ID determines that incidence or telescope.

IF-Insert requires an actual independently typed clause at its original binders. IF-Use requires the original scoped substitution m on the declared interface. Its whole-map theorem assumes each primitive/root's original lawful whole-map action (IF §6). These rules retain an existing full interface/action; they cannot manufacture one from a scalar Function bound or extend C=B across admission-live fields without the owning law.

At p_g, Source-Generalize §5.1 additionally needs the actual validating component K_g, complete N_g/T_g and §3.3 records for the imported active f relation and that c1 clause. LocalSelfRec licenses the open reference; it does not emit these publication records. The external Mono/Established row refers to an installed contract. Here f is active and uninstalled; treating it as the rebound formal of `apply/step` would change the premise. Nor does an Internal tag by itself construct the actual publication component/relation.

Allocation §5.2 preserves each input clause and legally translates its supplied telescope. **If** authentic inputs classify c as shared and B as frame eligible and retain active c=B, independent uses retain c=B_0 and c=B_1. That conditional elimination is valid. The rule does not determine that classification, the equality's placement or timing from native freshening. Per-frame EventProof witnesses cannot replace the equality operands. The current rules therefore do not establish transport through the actual two g frames, even after hypothetically completing the static Call input.

## Falsifiers, coverage and next action

Evidence refuting this obstruction would be an exact c1 owning-rule instance supplying every Code-Call origin above, followed by an independently justified native-to-whole-clause map at the original binders. Its actual p_g registration must supply the complete dependency records and component relation; its legal frame action must commute with native freshening on the retained signed pairs and qualified equalities while preserving the complete tuple. An additional generic row, scalar quotient, successful native solve or supplied transition checker would leave the missing premise untouched.

This audit uses rule inversion, not a semantic oracle or executable model. It is independent of the parallel prover's derivation, which was neither read nor coauthored. Both methods necessarily share the selected source laws and native-history inputs. No tests, mutations, seeds or input ranges apply. No new source counterexample, impossibility result, soundness/principality theorem, compiler acceptance result, recursive termination result or all-path implementation claim is made.

Commands: bounded `cat`/`sed`/`rg` reads; read-only `git rev-parse`, branch/status and `git show`; Python SHA-256 and direct byte comparison for the 14 semantic dependencies below. All 14 matched the pinned baseline. Initial combined output truncated; decisive rule windows were reread narrowly. One guessed active-root derivation filename was absent and supplied no evidence. At most three short shell read processes ran concurrently; zero heavy processes, tests/builds/probes/measurement samples, children or Git mutations. Exact CPU/RSS and total wall-time were not measured.

**One decisive next action:** assign the c1 Application owner a bounded source-construction packet producing its authentic complete Call origin and native-to-whole-clause action, with original introduction telescopes and p_g dependency output. Stop at any missing local law; then apply existing IF and Generalize allocation. Keep dependent implementation and parent proof closure OPEN.

## Frozen dependency snapshot

All paths are relative to `notes/`; each matched baseline bytes.

| Path | SHA-256 |
| --- | --- |
| `theory/2026-10-13-active-root-call-source-construction.md` | `88b1ce77c5d113972a252abb876529d13cbe6a1500e2497b72c22c4577627fbb` |
| `design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `design/2026-10-10-local-self-recursive-binding.md` | `38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895` |
| `design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `theory/2026-10-07-call-input-construction-proof.md` | `f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6` |
| `design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| `theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| `design/2026-10-08-native-recursive-interface-definition.md` | `a9f833556a7e7c361c5b602c982de96b78663a77099999206bdb7bda6da67903` |
| `design/2026-10-12-intrusion-value-type-association.md` | `28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775` |
| `design/2026-10-12-value-reference-copied-row-ownership.md` | `7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd` |
| `design/2026-10-10-parent-copy-scc-intrusion.md` | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| `design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-13-c1-raw-application-owner-falsification.md`.
- Baseline SHA: `beceb0bc91b35e84b4f62b353fc6c2abf18e0414`.
- Changed dependency hashes: none among the 14 semantic dependencies checked; no dependency edits by this worker.
- Claim/review status: frozen unreviewed bounded rule inversion; no independent certification, theorem closure or implementation authority.
- Checks already run: exact governing-window reads, manual Code-Call/IF/Generalize inversion, read-only Git baseline/status, SHA-256 and pinned-byte equality. No tests or builds.
- Proposed commit message: `research: isolate c1 Application formation and whole-clause transport premises`.
- Shared-record deltas left for primary/curator: record that §6's conditional skeleton applies to recursive f without a formal seed; retain the authentic Call-origin, native whole-clause map and p_g component/dependency premises as OPEN. No shared task/index/theory/authority/question files changed.
