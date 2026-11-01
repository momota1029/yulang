# R196 source model attempt — frozen handoff r1

Sprint: `CANONICAL-SOURCE-INFERENCE-MODEL/R196`, contract r1, activated SHA-256
`fa26559ffc6d30bbf1b91db03ab7e8f401bfe335e9d8e48e891e57155ee44fcb`.
Baseline supplied by the primary: `yulang3` / `84f0ff11e`.
Worker: `/root/r196_canonical_model`, bounded leaf; no descendants.
Requested configured role/model/effort: `lean_prover`, Sol/high, per activation.
Observed model/effort: UNKNOWN. Actual tool execution is recorded below.
Outcome: **probe and exact source-correspondence obstruction**, not a complete
model, original theorem, counterexample, or semantic-underdetermination proof.
Independent review: pending primary assignment; author makes no acceptance claim.

## Original parent and application

`YulangClosure.SourceProblem.InferenceSoundness`, `Contracts.lean:128`:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

All original supported source, original scope `x`, same assignment `a`, and
one shared witness `e` remain required. No concrete `SourceProblem` is supplied.
The checked symbolic leaf equation below rewrites the existing `Build` of
an arbitrary unannotated original literal. It does **not** turn independent
Simple-sub solving into `OriginalSource.Satisfies` or construct the shared
source witness. Thus it removes no original parent premise.

Before/after: **5/5 dependency packages open; 0/4 original roots closed**.
The canonical model, forward soundness, reverse coverage, principality and
actual inference-step well-foundedness all remain open. No Rust bridge,
production authority or source-acceptance change follows.

## Source authority, available equations, and first missing bridge

Read actual sources, not just prior receipts:

- Authoritative top-level algorithm, `2026-10-11-yulang-inference-top-level-principles.md`
  §§1–5: generation/accumulation/propagation, levels, extrusion/intrusion,
  generalization. Birth-level correction: `2026-10-24-birth-level-scc-intrusion.md`
  §§2–6. Original source-scope/strategy claim: `2026-10-13-intrusion-source-preservation-proof.md`
  §§1–3; its local proof is not full source preservation.
- Selected source judgment: `2026-10-08-source-generalize-definition.md` §§2–3,
  selecting `2026-10-08-source-generalize-definition-and-proof.md` §§3–5.
  Its §3.1 Literal row requires the actual declaration and whole local typed
  relation. L1/L2/L4 explicitly retain independently fixed primitive, original
  constructor, world and annotation laws. §4 constructs symbolic rules; it
  supplies no independent structural solver for their local semantic atoms.
- `2026-10-02-source-result-synthesis-choice.md` §§1–2 selects result
  forwarding and syntax-directed parameter entry. Typed-core §6 gives
  `I_literal = Value(type of literal)` and
  `Normalize(Value(A),d) = result(d)`, preserving `Result = Comp(empty,A)`.
  The wider typed-core document remains Draft; its header is explicit.
- `2026-10-09-native-literal-call-checking-definition.md` §§1–3 selects
  the literal-0 id Call construction in its authentic registered Int frame.
  The selected construction, `2026-10-09-native-id-original-wholearg-construction.md`
  §§3–4, derives `Value(Int)`, `Comp(empty,Int)`, the exact source literal,
  original carrier/root, same event/provider, and original complete view.
  Its licensed non-source Return alternatives remain available. This is
  available authority and is **not** dismissed because Lean has parameters.
- Approved `original-literal-result-owner/q1/d1` selects
  `Original-ResultLiteral` for literal 1 in the Application_N Name/Int seam.
  The selected candidate §§2–4 explicitly retains independent `H_prim` and
  `H_return`: whole primitive/Return contract, all witnesses/alternatives,
  current world, provider/future indices, exact original occurrence/telescope.
  It constructs original Data/Result-port registration and leaves complete
  Return/action realization to its actual contracts. Approved
  `original-literal-call-emission/q1/d1` authorizes its bounded construction
  direction; it explicitly does not adopt emitted membership or solving.
- `2026-10-05-source-contracts-and-common-allowance.md` §§2,3.1–3.3 retains
  original whole-tuple primitive relations, Return/Request Bind equations,
  same current configuration, complete Call and independent admission. The
  `OriginalSourceInterpretation.Inputs`, `LiteralDeclaration`, `LiteralAtom`,
  `literalKernel` and `generated_literal_membership` definitions were inspected.
  `OriginalSourceChecking` retains genuine readout/registration premises.
- `docs/yulang-source-type-safety-ja.tex`, opening corrections and
  `sec:source`, and `docs/yulang-operational-type-safety-ja.tex`, value rules,
  give research source/core context. The source manuscript is explicitly
  unreviewed. The full-language semantics manuscripts are construction drafts.
  Their claims were not promoted to original source authority.

**First unavailable input in the inspected selected source chain:** the
complete original literal-declaration/readout equation relating independently
generated Simple-sub value/effect constraints to the original literal row,
for every original literal and arbitrary original scope/event. At the actual
Lean leaf the required concrete conclusion is:

```lean
OriginalSourceInterpretation.LiteralAtom inputs declarations environment.root
  (literalObligation context site literal)
```

It expands to that **same literal's** original declaration at
`environment.root.row site`, ground descriptor classification, and original
ground membership, with descriptor/value/root taken at `(site, finalRoot)`
and the same `environment.root.event`. The missing construction must supply
the original descriptor/value/root/event readout and exact value/effect
constraints, then derive those declaration/guard facts from an independent
solution. It may not assume this conclusion, admission, or a readout theorem.
The bounded adopted rules above supply only their stated original frames and
retain independent primitive/Return inputs; neither supplies this complete
all-literal equation.

This is a finite **input/correspondence gap**, not proof that literal semantics
does not exist, not a source counterexample, and not evidence that a new
semantic decision is necessary. A parameterized Lean record alone would not
justify that conclusion. Owner: primary/source-declaration registration lane;
next evidence is the exact existing original declaration/operator contract and
its constraint/readout equations, or its source-grounded construction. No
new semantic alternative was selected by this leaf.

The independent structural `SimpleSub.Constraint.Satisfied` is `Sub` after
substitution. `SimpleSub.Term.atom` carries opaque leaf identities.
`SimpleSubLatticeInference` decodes these structural terms and all four
Function ports; `SimpleSubGeneralizationSoundness` transports a supplied
structural store and valuation. Neither relates these opaque atoms to the
complete original literal row. `OriginalSource.Satisfies`, in contrast,
interprets `Formula.local` by `Local`, whose atom case is `Kernel.atom`.
Defining `p.solves` as this latter proposition and invoking reconstruction
would retain precisely the unavailable original local meanings in solving.
It would not discharge the independent source-to-inference model package.

## Full source inventory retained as obligations

These are the actual `OriginalSourceGeneration.sourceRules` obligations,
not new rules or claims that concrete instances exist. They show why the
literal is the first local constructor dependency; the rest remain required.

| Original expression | Retained local obligations / consumer |
| --- | --- |
| literal | actual `literalDeclaration`; optional written boundary |
| primitive | complete `primitiveDeclarationInstance` |
| name | resolved same binding, fetch once, whole published/family instance |
| app | descriptor formation, whole argument compatibility, complete Call certificate, source incidence, callable image; value/computation Checking; applicable singleton-role origin |
| refSet | invariant reference protocol, result, actual content boundary; ordered suffix |
| lambda | captured whole environment, closure formation; outer-annotation entry role; receipt; Value entry Force/Return/rebind or retained Computation entry; complete body consumer and actual return/pending suffix |
| tuple | original ordered operand roots and tuple formation |
| record | ordered field/spread formation, actual visible updates and suffixes |
| polyVariant | original tag, arity, ordered payload roots |
| select | retained actual member selection, qualified children, same whole instance |
| caseE | ordered pattern/guard attempts, branch join, actual boundaries and suffix |
| catchE | same rigid packet instance, residual coverage, latent preservation, original arm order, branch join, raw continuation and current-state suffix |
| block | source-ordered statements, actual binding contexts, final root |

All 11 patterns remain: wild; literal comparison; variable binding; tuple
arity; list length/prefix/rest/suffix; record presence/defaults/spread; variant
tag/payload; nominal invariant declaration and explicit type arguments; Ref
comparison; same-input as alias; ordered OR with original merge map/common
environment. All 3 statements remain: let registration and recursive joint
member/world introduction; expression discard with actual suffix; original
module linking. Container rules retain ordered execution, defaults-before-
binding, input joins, outside-arm guards, operation rigid binders, continuation
contracts, and annotation formation at the written target.

Lambda's actual binder order remains description → viewLogic → invocation →
receipt → Value-entry execution telescope when applicable → shared retained
formal → pattern/body with eventProof. Initializer scopes, one-shot evidence,
publicationFinalRoot, group publication and future instance/alias frames remain
distinct. No independent witness is chosen for each port or use.

Call/effects are not erased: the argument is the original inert whole code
interface; callee-returned value, carrier, actual entry, receiver/receipt,
body, designated result consumer, invocation return, pending observations,
future calls/resumption and both effect rows all remain. Structural Function
terms retain argument value, argument effect, result effect and result value,
with their common assignment and polarities `(-,-,+,+)`. Contextual Function
membership and checking still require the independently formed checked domain,
same-provider actual inlet, captures, guards and full observation relation.
Their original full source readouts have not been constructed here.

The later `branchJoin`/Union boundary remains open independently:
`original-typed-union-rule/q1` has no adopted selected-branch/result dependent
field equations. No result telescope, transport or alternative was invented.
No source form is marked unsupported or assigned False. Semantic coverage of
all forms remains **omitted**, openly, because there is no complete model.
The one symbolic theorem ranges over all eight original literal constructors:
unit, Bool, Int, Nat floatBits, String, List Nat bytes, path String and character
String. It performs no conversion/truncation and has no CoreSyntax dependency.

## Checked declaration and complete final audit

Changed artifact:
`notes/theory/lean/YulangClosure/CanonicalSourceInferenceModelR196.lean`
SHA-256 `69d551760efc1b40f9235e749c4d2edde3e439b2cb91655495bf1c22d7d55c7c`.
Delivered theorem count: **one symbolic generation equation**, no parent theorem.
Exact printed type and complete final axiom result:

```text
literal_generated_formula : ∀ (context : Context) (site : Site) (literal : Literal),
  Build context (Source.literal { site := site } literal) =
    ((Formula.local (Premise.atom (literalObligation context site literal))).and Formula.truth).and Formula.truth
'YulangClosure.CanonicalSourceInferenceModelR196.literal_generated_formula' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The fully qualified theorem is
`YulangClosure.CanonicalSourceInferenceModelR196.literal_generated_formula`.
It has no source-admission, typing, solver, or readout hypothesis. It proves
only the displayed existing formula equation. `literalObligation` is a data
definition, not a theorem or concrete declaration interpretation.

Actual environment commands, from `notes/theory/lean`:

```text
elan which lake
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake
warning: failed to query latest release, using existing version 'leanprover/lean4:v4.35.0'
exit 0

/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --version
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
exit 0

/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake env lean --version
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
exit 0
```

Exactly two targeted checks, both the same command:

```sh
timeout 120s /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake build +YulangClosure.CanonicalSourceInferenceModelR196
```

First: exit **1**, module compilation 4.6 seconds. Actual error:

```text
error: YulangClosure/CanonicalSourceInferenceModelR196.lean:57:93: unsolved goals
context : Context
site : Site
literal : Literal
```

The displayed goal still contained
`compile (YulangClosure.OriginalSource.annotated✝ { site := site } context
(RuleTree.rule Rule.lit site context [Premise.atom A] RuleForest.nil))`
on the left, versus `((Formula.local (Premise.atom A)).and Formula.truth).and
Formula.truth` on the right; `A` here abbreviates the full atom record printed
twice by Lean, exactly `literalObligation context site literal`. The failed
proof used `simp only [Build, sourceRules, compile, compilePremises,
compileForest, literalObligation]`. Lean warned that the three compile simp
arguments were unused. Its temporary error-recovery theorem audit was:

```text
'YulangClosure.CanonicalSourceInferenceModelR196.literal_generated_formula' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```

That failed attempt was not accepted or delivered. Repair: rewrite the
well-founded `sourceRules` equation first, then close the reducible private
annotation wrapper and formula compilation with `rfl`:
`simp only [Build, sourceRules]; rfl`. This addresses actual diagnostics,
not the independent semantic gap. Second check: exit **0**, module 903 ms,
`Build completed successfully (5 jobs)`, with the final complete axiom list
above and the printed unchanged `InferenceSoundness` definition.

The skill checker was not invoked: its line 208 creates a new
`TemporaryDirectory(prefix="yulang-lean-audit-")`, forbidden by this packet's
no-scratch-tree bound. The exact theorem `#check`, `#print axioms`, and parent
`#print` are embedded in the leased module and ran during both checks.
No third check, full/default build, test, installation, dependency update,
Core build, environment, target or scratch tree was created.

Source search over the changed module and its exact project dependency cone
`Contracts.lean`, `OriginalSourceGeneration.lean`, `OriginalSourceSyntax.lean`
for `sorry`, `admit`, top-level `axiom`, `skipKernelTC`, `native_decide` returned
no matches (rg exit 1). Final theorem's transitive axiom audit is the stronger
evidence; a search alone was not counted as a proof.

## Pins, generated outputs, and cessation

All nine contract-pinned Lean input hashes were rechecked and match:

```text
Contracts 2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e
OriginalSourceSyntax 3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1
OriginalSourceGeneration 126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef
OriginalSourceInterpretation feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef
OriginalSourceChecking a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6
SimpleSubLatticeInference c534c060dfde84f2817fbaa53222f430b59d9b6377cfacedabeca7b9b4b8ffa3
SimpleSubGeneralizationSoundness 3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246
InferenceConstruction 576d69266da62c0f75fa9748ff0f0691a9f0bc3aca5148be9d25cef82d2010f0
CoreSyntax c5a25cb7d935159b62f377b7fa88b3e92e4cdf429118d566e53f7859f6ea5375
```

Key semantic-source SHA-256:

```text
source-generalize-definition 46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38
source-generalize-definition-and-proof e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240
native-literal-call-checking-definition e65be7638ed616f5a88ce7d7bc5fffa06a07ee634df3649bd83cf0a60410d39b
native-id-original-wholearg-construction b8bdf720e50bcfab691f70c08fee8cb32fb2b34f3817099faba512378ebdcb24
original-literal-result-owner approved-answer d4240c3f9938db958eb1068df2a8f4a35cf4d23721da2eb6cec9f5f3b5bc1516
original-literal-call-emission approved-answer 77855c8526e1c105d40fac4dfc58455560fcc6135d280f2302e9809de717c4a8
original-literal-result-owner-extension-candidate 0c5c58022c6834651fedff6c14d8cdf96002831c0c2d25292843abbae64d3924
source-result-synthesis-choice 71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992
typed-computation-core-elaboration 0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e
source-contracts-and-common-allowance 1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186
```

Project pins, unchanged: toolchain SHA `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`;
lakefile SHA `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`;
manifest SHA `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.
No external packages. Direct checked imports: Contracts and OriginalSourceGeneration.

One cache owner, explicitly confirmed by primary. Generated existing-cache
outputs for this module only, under `notes/theory/lean/.lake/build/`:

```text
lib/lean/YulangClosure/CanonicalSourceInferenceModelR196.olean
  efc1f020df17be98feac6e125cdc8df58490be1483efaf47f5bf87a23f685b09
lib/lean/YulangClosure/CanonicalSourceInferenceModelR196.ilean
  992bf081f00a44f85d7e9d4b7684094b51e583db41ecd68d8d9d0eb2af1fa559
lib/lean/YulangClosure/CanonicalSourceInferenceModelR196.trace
  669b5e5b9fd1b355f22fd97eeb4f8e9127577272b8e967d4e50648a1ae254426
ir/YulangClosure/CanonicalSourceInferenceModelR196.c
  1eebaf20b2b735e6e6550e5e65e74395562cc3bc65b4527aef1f634ebaf9a77e
ir/YulangClosure/CanonicalSourceInferenceModelR196.setup.json
  70a6465b69e90c06bdf6d9de9f9cd7204890580890d51f42bf45b7f0c08fc4f4
```

Lake also created `.olean.hash`, `.ilean.hash`, and `.c.hash` beside those
files. No standalone scratch/log/audit path. Failure evidence is retained in
this handoff and actual tool transcript. No other worker's file, root import,
shared status/index, rules, configuration, toolchain, dependency or Git state
was written. No Rust owner was inspected to fill equations.

Resource envelope: 2400 active seconds maximum, two 120-second bounded
single-process checks, project `-j1 -M1024`; neither timed out. Per-check
observed compilation times are above. Exact aggregate agent active seconds,
peak RSS and effective model/effort are not exposed to this leaf; do not infer
them from token counts. Work stopped well inside the granted bound.

Worker state: **STOPPED; writes stopped after this r1 handoff**. No running
Lean process or descendant; cache ownership returns to primary on intake.
Only the two exact leased outputs were authored. Frozen artifact awaits
independent source-correspondence review and primary adjudication/integration.
Next source request: `R196-LITERAL-READOUT-1`, original parent above, primary
source-declaration owner, exact complete original declaration/constraint/readout
equation; falsifier is a solution whose original literal atom fails at the
same scope/assignment. Pending Union requires its existing separate owner.
