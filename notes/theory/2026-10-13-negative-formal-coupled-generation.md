# Negative formal: coupled generation and authentic call/output boundary

Date: 2026-10-13
Status: frozen research checkpoint; independent review pending; no parent closure
Claim class: bounded source-construction characterization and minimized obstruction
Y3 baseline: `c69d0b3629879294511fce4e8e20ceffc791ac53`
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this file only; leaf, no delegation or Git mutation

## 1. Frozen objective, authority, quantifiers and exclusions

Question: do the actual source owners construct an executable instance for a
composed-negative concrete formal, coupled to its authentic direct or aliased
call and owning output? Derive that instance, or identify the first absent
operation. No supplied attachment-to-call map or balanced PUSH/POP diagram is
a premise.

The indexed governing files are dated 2026-10-10, rather than the approximate
2026-10-12 names in the assignment: [annotation policy](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–4 and §6's withdrawal; [concrete annotation implementation](../design/2026-10-10-concrete-effect-annotation-implementation.md),
“Annotation checking and publication owner”; [attachment admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§§3–6, particularly set-wide identity §3.1 and the excluded negative-formal
enabling §6; [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. Contravariant concrete annotation permits function-local subtraction;
covariant annotation allows its concrete members. Symbolic tails remain
connected. The withdrawn `run_io` result selects no output. No automatic
subtraction at every unhandled output, handler semantics or admission rule is
invented.

The original H remains exactly the statement in [global hygiene](2026-10-11-oracle-global-effect-hygiene-proof.md)
§1: for every Oracle source P in the original successfully lowered domain,
every successfully lowered composed-negative concrete occurrence a, its
original lexical scope sigma and binders, every actual copy/instantiation u,
and every actual call/output route k involving that occurrence, authorized
subtraction removes only the contribution attached to that exact instance on
that route; an independent contribution at the same resolved family survives.
Symbolic tails and all current/future concrete checks remain connected; original
occurrence, attachment, scope, provider/call binder and correlated residual
lineage remain identified through actual copying/generalization, up to the
actual consistent fresh-use renaming. Incorrect lowers require authentic
checks/errors and safe nonpublication. Actual providers, tails and outputs
cannot be selected independently. No H quantifier or source restriction changes.

For the bounded discriminator fix f, formal cb, exact result-row occurrence a,
resolved nullary concrete member E, original scope sigma and direct call k to
cb in f's body. The historical spelling is
`my f(cb:(() -> [tick] ())) = cb ()`; it is used to name the already reviewed
Oracle spine, with no new parsing/execution claim. Provider code is absent.
For an aliased route, keep the additional resolved local binder d and actual
call k_d separate from cb and k; no type-row equivalence identifies them.

**Required generation premise G:** the negative formal constructor emits its
executable attachment instance, and the authentic consumer uses that same
instance, or its actual coupled freshening, in the appropriate call/output
operation. The residual consumer must retain exact tails, correlated parents
and independent constructor lineages. This packet establishes the current
Y3 non-generation boundary, and bounds the Oracle construction that can guide
G. It does not supply G by hypothesis.

Shared premises: inspected baseline bytes; successful HIR formation where
explicitly assumed; completed fallible constructor calls and arena freshness
without ID exhaustion. Exclusions: complete provider compatibility/Call,
runtime handling, parameterized effects, complete replay/termination, all-path
copying/extrusion/qualified intrusion/generalization preservation, soundness,
principality, negative admission and public/F5 cutover. Local exclusions do not
remove those cases from H.

## 2. Y3 non-generation follows at the source owners

The following is a bounded derivation about current implementation, not a
semantic source-rejection policy.

1. HIR `source_annotation.rs:349–374,399–480,505–558` preserves annotation
   owner, exact source position, Function structure, row position, resolved
   concrete members and symbolic variables. Thus the occurrence and member
   facts are known before inference; their presence does not emit subtraction.
2. `CandidateInference::solve` (`shadow_apply.rs:92–115`) calls source preflight
   before batch collection/session execution. The Lambda branch
   (`candidate_source.rs:97–99`) starts its formal at negative polarity.
   `preflight_formal:116–121` reverses Function arguments and preserves results.
   At every visited negative row, acceptance requires
   `concrete.is_empty() && variables.len() == 1`. A nonempty concrete result
   row fails, with or without a symbolic tail. Earlier unsupported checks may
   stop traversal first; universal non-acceptance does not imply every failing
   source reaches this particular test.
3. Even bypassing preflight would not supply G. `candidate_formal_annotation`
   (`candidate_effect.rs:1073–1111`) starts the paired construction at Negative,
   at the actual parameter Value's level. `candidate_formal_pair:1034–1052`
   rejects the same negative concrete row before returning the Function pair.
   The two Value edges and `formal_domains` insertion occur only after
   `pair?`; neither is reached successfully for this occurrence.
   `candidate_formal_effect_port:1054–1070` independently has only omitted,
   singleton symbolic, and composed-positive concrete branches.
4. The available source payload cannot repair this failure. `LocalWeight`
   (`candidate_context.rs:114–133`) has statically empty `left_word: [();0]`
   and `right_pops: [();0]`. `source_weight:2174–2195` retains owner, row
   position, member ordinals, polarity and scope, and constructs those empty
   words. `SourceUnitPush` is prepared only for positive nonempty sets.
   `materialize_unit_push:2200–2222` returns a detached payload and explicitly
   creates no live context, relation, bound, registration or recipe.
   Thus even this positive preparation is no negative formal executable pair.
5. `candidate_check_effect_operand:888–958` expands Support to members/tail;
   an allowed nominal member returns success; an unmatched member forwards
   unchanged to its actual symbolic tail or produces a conflict. This is an
   allowance check. It creates no attachment-local reduction or output POP.

Consequently, for any successfully formed LocalSource retaining the specified
composed-negative concrete formal, the current public candidate entry cannot
generate G. The direct and aliased bodies both stop before its successful
formal action. This is stronger than observing a failed balanced-weight
probe, but proves neither H false nor supported-language rejection legitimate.

## 3. Native direct and alias spines do not supply the missing exit

The actual downstream owners explain exactly what would still be absent after
a guard-only edit. For admitted schedules, `admit_candidate_fact`
(`shadow_apply.rs:1308–1447`) validates the registered application occurrence
and callee/argument/result/effect endpoints, allocates invocation Effect J at
the application's level, emits the actual four-port Function demand, and
forwards both J and callee evaluation Effect to application Effect B.
`admit_lambda_fact` (`lib.rs:11233–11369`) takes the retained formal domain,
joins B and inferred entry Effect into f's actual return Effect O, and
publishes the Function. It wraps neither actual body Value nor Effect with a
concrete-formal predicate.

At one fixed level, the conditional native constraint skeleton is

```text
A+ <: P; P <: A-; P <: demand_k
result_effect(A+) <: J; J <: B; B <: O
```

The Function result child preserves its actual context. Opposite-bound replay,
level-selected accumulation and extrusion determine physical transport; no
eager solving or freely chosen output witness is assumed. A+ and A- name the
paired interface that G still needs to construct for this source. The skeleton
for admitted forms proves structural incidence, not execution for the rejected
formal or attachment subtraction from O.

Aliases have authentic owners. `candidate_source.rs:369–408,641–680` emits
local use actions and the actual alias callee's Apply recipe. Installation
(`candidate_scheme.rs:1319–1344`) records LocalScheme `{id,root,boundary}`;
`route_candidate_local_run:1354–1398` checks the exact slot, local identity,
occurrence, destination Value and use level, captures its current graph, and
prepares a fresh use. `prepare_candidate_fresh_use:980–1069` has one canonical
row map, one per-use context origin, a bundle map, and a view map; older or
non-generic rows remain shared. `begin_candidate_fresh_bound:1221–1268`
restores each captured bound's actual orientation, context, bundle incidence
and fresh-use evidence.

Those operations copy/restore *existing* captured data. They are no producer
for a missing negative formal instance or predicate. In particular, merely
retaining an annotation set or transport origin cannot establish the call's
licensed lower fiber, output POP or concrete residual feedback/projection.
No whole-generalization preservation theorem is inferred from these maps.

The first absent Y3 owner operation is therefore at the negative paired formal
constructor. The additional absent **formal exit** operation belongs to the
actual call/Lambda output seam: construct the source-derived instance's
appropriate call predicate and apply it to that owning output. Existing G-free
Function port transport and inferred-entry evidence do not select it. Exact
alias and residual behavior must be established before that operation can be
specified as an implementation invariant; this note chooses no representation.

## 4. Oracle comparison: direct construction, guarded predicates, aliases

Oracle locators below are pinned Git objects, never the current Oracle worktree.
The reviewed [transfer audit](../progress/2026-10-12-oracle-effect-source-transfer-audit.md)
§§3–6 remains a bounded input. Narrow original-source inspection distinguishes
which parts of its direct construction can actually extend to aliases.

**Direct construction.** `annotation/constraints.rs:363–390,424–470,657–690`
constructs immediate result views `Stack+(q,PUSH_i(S))` and
`Stack-(q,FILTER(S))` and returns the predicate `POP_i.with_filter(S)`.
The one fresh i belongs to the concrete set S at this construction; row q may
be shared without sharing i. `lambda.rs:919–942` stores the exact returned
predicate on the actual introduced formal locals. `tail.rs:690–705,844–852`
requires the actual `Expr::Var`/resolved DefId and reads that local's predicate.
`make_app_with_origins:535–624` adds those same weights to the current frame
before constructing its demand and forwarding call Effect. Finally
`tail.rs:1058–1109` and `lambda.rs:1232–1237` wrap actual output Value and
Effect with the frame predicate. This is the real direct formal-exit
construction absent from Y3; it is not a proof of every check's completion.

**Immediate versus descendant.** The Function case returns only its immediate
`ret_eff.subtracts` (`constraints.rs:389`). Descendant Function graphs remain
in the ports but their predicates are not flattened into the outer binder's
direct predicate. Tuple output concatenation (`335–348`) is a separate branch.
Thus a structural induction assigning every descendant occurrence the same
outer direct-call POP fails at the actual constructor.

**Wildcard guard.** `callable_annotation_has_effect_wildcard`
(`lambda.rs:1509–1527`) recursively checks parameter, argument Effect, result
Effect, returned value and tuples. `lambda_annotation_predicate_constraints`
(`1581–1586`) suppresses the ordinary Function call predicate if any such
wildcard is present. Independently, the immediate wildcard row has its own
`parameter_function_boundary` branch (`constraints.rs:444–451`). A concrete
immediate result does not bypass a descendant wildcard. An enclosing f output
wildcard outside cb's annotation is a different scope. These guards describe
actual constructor behavior; wildcard occurrences remain inside H's domain.

**Aliased local lookup.** `block_local.rs:546–585` creates a plain local
binding's distinct DefId via `bind_let_local_with_def:1225–1263`, assigns its
body Value and generalizes that Value. The new LocalBinding's
`call_predicate_subtracts` is empty and its predicate frame is None. The
pinned lowering-tree search finds the only extension of this field in
`mark_lambda_param_call_predicate`; the local let owner does not copy cb's
field simply because its initializer refers to cb. Hence, for a completed
plain local binding d with no separate parameter-annotation marking, the
actual `Expr::Var(d)` call lookup returns d's empty local predicate.
`unannotated_local_callee_return_effect:740–758` also returns bare ports for
Def::Let, before its special unannotated Def::Arg mechanism. The direct
frame-extension route alone supplies no i for that alias call.

This is **not** a proof that the aliased source loses subtraction or violates H.
`instantiate_local_value` (`tail.rs:855–944`) either shares the local Value or
instantiates its scheme and constrains the instantiated predicate to that
Value, including genuine scheme-instantiation routes. Type-level retained
stacks may supply another path. `instantiate.rs:741–787` consistently renames
retained IDs and additionally wraps stack quantifiers with `u32::MAX` root
POPs. Establishing that path requires proving what generalization retains and
how this same occurrence/call/output observation reaches its real consumer.
No literal alias fixture was parsed, and no generalized observation is assumed.
This is a minimized source/operational bridge obligation, rather than a
source-qualified counterexample or a claim of universal alias non-generation.

The printed mini-language's missing exit, established in [negative formal
derivation](2026-10-12-negative-formal-source-proof.md) §2, remains separate:
its I-Lam/I-App rules forward the actual PUSH but emit no matching output POP.
Their lexical-bracketing assertion cannot replace a source rule. Oracle's
production direct-frame construction supplies such a rule for its stated
guarded domain; it does not fill the mini-language or aliased/generalized
bridge by itself.

## 5. Proved scope, obstruction and economy audit

Derived here: current Y3 negative concrete-formal non-generation on inspected
entry/paired owners; the admitted direct/alias structural consumer spines;
and the exact limitation of Oracle's local predicate route for plain let
aliases. These are bounded source characterizations, pending independent
review. No new universal theorem is claimed. No executable probe ran.

Still open: G's negative attachment constructor and authentic exit/residual
consumer, and the Oracle aliased/generalized observation bridge. They must
preserve original scope, actual provider, complete call incidence, every
applicable current/future lower and independent same-family contribution,
with correlated residual tails/parents and constructor lineages. A copied
row, support member, bundle or ID is not that coupled conclusion.

The previous production-singleton route and printed-rule route already reached
this same seam. This packet investigates the owning constructors and the
distinct alias consumer rather than another supplied transition algebra.
The economy audit classifies local safety and natural negative inference as
A/B; reconstructing occurrence/route evidence from equal rows after the owner
discarded it is D. HIR knows occurrence/members/scope; the paired owner knows
its interface and set identity; the call owner knows resolved binder and actual
demand; Lambda knows its true output. Retaining those facts could avoid D,
but cannot manufacture the missing semantic operation or its consumer proof.
No obligation reclassification, source restriction or parent status change is
a result of this audit.

One next action: the primary should assign the smallest source-owned coupled
negative constructor/exit invariant, including the actual alias observation
bridge, to its existing independent authority/review path before any dependent
admission implementation. A third balanced-weight proof would leave the named
premise unchanged. No additional semantic vote is identified for the selected
polarity policy; the exact missing source operation needs adjudication.

## 6. Checks, resources, runtime and commit packet

Static evidence only: `cat`, bounded `sed`/`rg`, read-only `git show` and Oracle
`git grep`, baseline-byte comparison and SHA-256 snapshot. All named live Y3
dependencies matched the pinned baseline. No tests, builds, executable models,
probes, Oracle invocation, measurements, Git mutations, delegation, source
edits or shared-record writes. Some initial large policy captures were
truncated; governing policies and decisive constructors were subsequently
read in bounded captures. At most one foreground lightweight source-read
command at a time after the initial independent policy reads. CPU/RSS and
wall-time were not instrumented; no heavy process or measurement sample ran.
Stop condition reached: concrete non-generation and authentic alias bridge
obstruction identified.

Requested model/effort: not exposed in the received packet; normal policy is
`gpt-6.1-sol` / `high`. Config registers prover and its role has no model/effort
pins. Observed effective runtime metadata: unknown. No Astra or hot-reload
claim. This leaf launched no jobs. Independent review is primary-owned.

Dependency snapshot follows. Final equality recheck and the note's whitespace
check are static document checks, not test/probe evidence.

| Y3 dependency | SHA-256; equals baseline |
| --- | --- |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a`; yes |
| `notes/design/2026-10-10-concrete-effect-annotation-implementation.md` | `3a3186723cd93edd2f767a7e4a481cb6dbed701fc749502e640071f65a4d89ae`; yes |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc`; yes |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389`; yes |
| `notes/progress/2026-10-12-oracle-effect-source-transfer-audit.md` | `e46cbe4f5df92f631a02b9204db6b976f4dc3f0976b95b888dcf2a3b791e0e90`; yes |
| `notes/theory/2026-10-12-negative-formal-source-proof.md` | `2db5d4763ddb7348cb3cb95acc42f492e3457d1773a149410171564c0a3f8081`; yes |
| `notes/theory/2026-10-11-oracle-global-effect-hygiene-proof.md` | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1`; yes |
| `crates/yu-hir/src/module/source_annotation.rs` | `a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb`; yes |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49`; yes |
| `crates/yu-solver/src/candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df`; yes |
| `crates/yu-solver/src/candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987`; yes |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1`; yes |
| `crates/yu-solver/src/shadow_apply.rs` | `cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411`; yes |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94`; yes |

| Pinned Oracle dependency | SHA-256 |
| --- | --- |
| `crates/infer/src/annotation/constraints.rs` | `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db` |
| `crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| `crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `crates/infer/src/lowering/expr/block_local.rs` | `661386fe559d8e207a9597962cfee3c11f05f21aa2888e22b2c0143825051898` |
| `crates/infer/src/instantiate.rs` | `876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c` |

Commit packet:

- Exact lease/change: `notes/theory/2026-10-13-negative-formal-coupled-generation.md`.
- Baseline: `c69d0b3629879294511fce4e8e20ceffc791ac53`; Oracle
  `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none observed; final table fixes inspected bytes.
- Claim/review: bounded constructive source characterization and obstruction;
  unreviewed research checkpoint, no certification/admission/parent closure.
- Checks: exact owners, pinned Oracle objects, baseline-byte/dependency check,
  leased-note whitespace check; zero builds/tests/probes.
- Proposed message: `research: pin negative formal generation and alias exit boundary`.
- Shared-record deltas for primary/curator: link this exact constructor result;
  distinguish Oracle direct-frame predicate from alias scheme transport;
  retain H, G, negative admission, complete Call, soundness/principality and
  F5 gates OPEN. No task/index/theory status record was edited.

Writes stop at handoff; the primary freezes this artifact for independent review.
