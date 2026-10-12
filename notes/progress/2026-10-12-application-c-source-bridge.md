# Application c: source constructor and checking evidence bridge

Date: 2026-10-12
Status: frozen research source audit; independently reviewed within the bounded claim; no theorem or acceptance claim
Primary baseline: `b4c46cf05bc62a53b61141605686be2177b82358`, `research/simple-sub-intrusion`
Producer: `/root/application_c_source_bridge`, complementary researcher lane
Exclusive lease: this file only; production implementation authority: none
Requested routing: standard researcher. Observed effective model/effort:
unknown; no runtime settings evidence was supplied or inferred from role files.

## 1. Objective, hypotheses and result class

Trace the innermost Application c, `f y`, in the unchanged fixture:

```yulang
my answer = {
  my f x = {
    my g y = { my drop z = y; drop (f y) };
    my first: int = g 0;
    g ()
  };
  f
}
```

This is a bounded source/artifact correspondence audit, not another
postfixedness proof. The owning constructive obligation remains
[`H_f subset Phi(S).V`](../theory/2026-10-12-nested-recursive-f-postfixedness-proof.md#1-frozen-statement-and-original-scope),
with its original domains, every actual provider decomposition, independently
admitted challenge, pending/complete development and compatible future.

Hypotheses for the static lowering derivation: the displayed text has an
ordinary recovery-free CST of the expected forms; the private LocalSource
route is enabled; identities/storage are available; the inspected dependencies
match the primary's pinned revision. Neither parsing nor baseline equality
was independently established here. All source locations below describe
conditional constructor behavior, not observed allocated runtime identities.

**Result:** this route retains lexical/source origins and generates native
polarized constraints. It supplies no authentic finite local complete-Function
comparison for c's original `A_f -> F_c`, and no original whole-carrier proof
of (D)/(P). That is an evidence gap on this named route, not a proof that a
finite source derivation is impossible, that the program is rejected, or that
the governing source semantics is inconsistent.

## 2. Exact governing sections and preserved meaning

- [Top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
  §§1,3–5 require native Simple-sub generation/propagation and proof-derived
  implementation; proof convenience supplies no new source restriction.
- [Source Generalize selection](../design/2026-10-08-source-generalize-definition.md)
  §§2–4 selects [its construction](../theory/2026-10-08-source-generalize-definition-and-proof.md)
  §§3.1–3.3: Name restricts the same binding certificate; Call uses the whole
  inert argument and actual entry/return; recursive installation requires
  simultaneous member/world evidence. L3/L4 remain actual local premises.
  §3.2(4)'s domain/observation inclusions are conclusions of finite local proof
  constructors, never an inclusion oracle leaf. §3.3 records are constructor
  outputs, never certificates inferred from identifiers.
- [Contextual Function definition](../design/2026-10-08-contextual-function-membership-definition.md)
  §§2–3 and [input realization](../theory/2026-10-08-call-semantic-input-realization.md)
  §§2,3.1–3.2,4.2–4.3,5 require one actual provider, independent challenge
  formation, same whole carrier/world and complete observations. Theorem F
  consumes a genuine whole comparison; it does not construct c's comparison.
- [Source scheduling](../design/2026-10-02-source-call-scheduling-choice.md)
  §§1–2(A) selects inert whole-argument reification. At c the whole argument
  is `Name y`; at the enclosing Call it is the whole computation `f y`.
  The bare Value formal z forces that computation before drop's y body.
- [Captured closure definition](../design/2026-10-08-captured-closure-constructor-definition.md)
  §§2–4 supplies complete Strict/entry and prefix meanings; its captured Step
  takes ordinary captured-f validity as input. [Native recursive interfaces](../design/2026-10-08-native-recursive-interface-definition.md)
  §§2–4 supplies only the selected pair case. Neither introduces this nested f.

The [nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–3 is explicitly confined to `my apply f = { my step x = f x; step }`.
It is not broad acceptance authority for this recursive fixture. The two
assigned research notes preserve the present candidate's source rule expansion
and leave its complete checking/introduction premises open.

## 3. Source-to-HIR construction, with lexical identities

Let Q be answer's DefinitionRootId. [Module lowering](../../crates/yu-hir/src/module.rs#L1410)
calls `local_source::form` only on its enabled private route. The carrier's
[data types](../../crates/yu-hir/src/module/local_source.rs#L97) retain
occurrence, SourceNodeKey, range, scope and child indices. These fields are
syntax/ownership evidence, not a semantic event/world certificate.

| Source occurrence | Owning constructor and retained fact |
| --- | --- |
| f/g/drop declarations | [block](../../crates/yu-hir/src/module/local_source.rs#L709) registers Local bindings and parameters, source identities and initializer slots before traversing RHSs. [Initializer/Publish](../../crates/yu-hir/src/module/local_source.rs#L329) temporarily installs each parameterized local's self identity, adds its formal Lambda, then restores/publishes its binding. |
| inner Name f | [IdentifierExpression](../../crates/yu-hir/src/module/local_source.rs#L640) resolves the latest lexical entry: the same enclosing Local f, still in its initializer. |
| argument Name y and drop body y | The same Name constructor resolves both to g's Parameter y; z is distinct and unused. |
| `f y` | [OperatorChain](../../crates/yu-hir/src/module/local_source.rs#L488) constructs Apply(callee=f Name, argument=y Name, source_form=tail kind), with distinct child occurrences. |
| `drop (f y)` | Apply retains drop Name and a [Group](../../crates/yu-hir/src/module/local_source.rs#L676) around c. It does not rewrite c's callee or argument binding. |
| first / final g uses / final f | Sequential Publish makes the appropriate g/f Local entry available. first's written annotation remains attached to its binding. |

Conditional ordinal layout follows registration order: f=`HirLocalId(Q,0)`,
g=`(Q,1)`, first=`(Q,2)`, drop=`(Q,3)`; x/y/z are Parameters `(Q,0/1/2)`.
The layout establishes which constructor creates an identity; numeric
ordinals establish no membership or local-check proof. The exact bytes have
not been parsed, so successful HIR reachability remains unverified.

## 4. What actual candidate construction supplies

[Candidate source collection](../../crates/yu-solver/src/candidate_source.rs#L180)
allocates endpoint recipes and formal registration/name records. A Parameter
Name uses its actual parameter recipe. Work traversal starts at level 1,
increments only for local initializers and retains open endpoints in
`active_initializers`. At c, f/g are active: f/x level 2, g/y/c level 3,
drop/z level 4. Both later g uses are after installation.

The [Local Name branch](../../crates/yu-solver/src/candidate_source.rs#L369)
therefore emits `Action::Link` from f's original initializer endpoint to the
callee Name row, rather than a fresh published use. [Link execution](../../crates/yu-solver/src/candidate_source.rs#L665)
admits a polarized value relation with occurrence provenance. This preserves
the native recursive endpoint association; it installs no actual hereditary
f/world certificate.

The [Apply branch](../../crates/yu-solver/src/candidate_source.rs#L394) retains
`CandidateRelation::Apply` and `ApplySourceInput` with owning Q, child indices,
level, endpoint recipes, checking occurrence and cause. Since f is a Local,
`formal_name=None`; y's formal registration is the argument's origin, not a
callee-formal introduction certificate for f.

[admit_candidate_fact](../../crates/yu-solver/src/shadow_apply.rs#L1308)
checks recipe incidence and allocates the native negative demand:

```text
callee+ <: Function(argument+, argument_effect+, invocation_effect-, result-)
callee_effect+ <: application_effect-
invocation_effect+ <: application_effect-
```

It retains NativeInterface terms and graph constraint provenance. These native
four ports are not a constructed original `F_c`, complete domain `D_F_c`,
observation family `P_F_c`, `xi`, whole argument `J_y`, or comparison proof.

The [Lambda recipe](../../crates/yu-solver/src/candidate_source.rs#L445) joins
parameter/body endpoint recipes. [admit_lambda_fact](../../crates/yu-solver/src/lib.rs#L11233)
constructs a positive Function and entry/body-to-invocation effect relations;
the entry edge additionally retains inferred-entry endpoints/provenance.
This supports native Value-entry effect generation, including unused x/z.
It is not original receipt/Force/rebind/body/invocation-return evidence or
identification of f's original complete `A_f` and actual entry `I_x`.

[CandidateSourceCall observation](../../crates/yu-solver/src/candidate_call.rs#L282)
validates authentic source/child occurrences, scopes, cause and native port
kinds/negative Function shape. It does not execute/check source laws.
[PendingCallConstruction](../../crates/yu-solver/src/candidate_call.rs#L217)
explicitly retains OriginalGenCall0, ArgumentReifyAndWholeCarrier, and
ReceiverDispatchAndCompleteResultFutureInterfaces as missing suppliers.
The formal-specific supplier trio is absent for this Local callee, which
does not remove its complete original source obligations.

## 5. Minimum missing evidence and exact prover handoff

The [f-y inventory](../theory/2026-10-12-fy-complete-call-construction.md#3-static-rule-instances-and-their-exact-missing-inputs)
specifies *conditional* originals: callee `A_f`, checked complete `F_c`,
Reify/Delay carrier `J_y`, VIncl and WholeArgCompatible origins. The inspected
native construction authenticates neither that entire original record nor
the truth of those checks. Origin retention alone would still be insufficient.

At the [postfixedness seam](../theory/2026-10-12-nested-recursive-f-postfixedness-proof.md#43-gs-delayed-whole-argument-and-the-first-recursive-checking-seam),
the needed finite proof must establish, at one original assignment/telescope:

```text
(D) d in D_F_c(e)       -> the same d in D_A_f(e)
(P) o in P_A_f[S](d)    -> the same decorated o in P_F_c[S](d)
```

First supply genuine identification/formation of `A_f/I_x`, `F_c` and `J_y`
with the authentic provider, reify license, capture/current world, receipt,
entry paths, complete ports and hard guards. Then supply c's finite checking
tree from Source Generalize §3.2(4): D transports the *same whole carrier*
to f's actual I_x, and P follows from the tree's constructors at the original
scopes. A `V*` pointwise inclusion cannot be applied to the provisional S
premise; identity/composition/congruence/recursive pairing require their
actual original children and nonpositive equality/domain proofs.

This handoff leaves the independent background embedding, complete f/g/drop
readouts, original guard/primitive/W/Z inputs and parent H_f proof open.
The raw no-finite-Return argument in the assigned note §5 supplies no
admission check: independently admitted/pending/zero-step cases remain.

Recommended next action: give the constructive owner this exact c-local
original interface/check tree obligation, beginning with D's same-carrier
map to I_x, then expand its genuine proof constructors to obtain P. More
native endpoint/storage checks would leave the same premise untouched.

## 6. Verification, independence and frozen dependencies

Commands: bounded `cat`, `sed -n`, `rg -n`, `wc -l`, `sha256sum`; source reads
and a hand constructor trace only. Some early combined captures truncated;
decisive source/checking and lowering sections were reread narrowly. No
tests, builds, parsing, solver/source execution, seeds/ranges, mutations,
performance measurements, child agents or Git commands. Zero heavy processes
and zero inference samples. CPU/RSS, peak process count and exact elapsed
time were not instrumented; no numerical compute budget was assigned.

Oracle independence: no executable oracle was used. Source meaning comes
from the selected definitions, implementation claims from constructor bodies;
their correspondence is precisely the open issue. The notes share the
original fixture and semantic definitions, so this is complementary source
evidence, not independent certification of their mathematical claims.
Failure conditions include CST recovery/unsupported structure, disabled route,
resource failure or dependency mismatch. Production F5/generalization,
runtime closure allocation/captures, source acceptance and other Call routes
were not exhaustively audited.

SHA-256 snapshot (no dependency changed by this producer):

```text
73810fef85c264e02a179b8630d4c392fdc0f5369123cb1a4cbe7cfecb2eccb2 notes/theory/2026-10-12-nested-recursive-f-postfixedness-proof.md
3bcc290f0fab01f08272d83c358f491df377da46f2022412c176184533d9f872 notes/theory/2026-10-12-fy-complete-call-construction.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389 notes/design/2026-10-11-yulang-inference-top-level-principles.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38 notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 notes/theory/2026-10-08-source-generalize-definition-and-proof.md
0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0 notes/design/2026-10-08-contextual-function-membership-definition.md
fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a notes/theory/2026-10-08-call-semantic-input-realization.md
6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd notes/design/2026-10-08-captured-closure-constructor-definition.md
a9f833556a7e7c361c5b602c982de96b78663a77099999206bdb7bda6da67903 notes/design/2026-10-08-native-recursive-interface-definition.md
181e95a9d87d90c265f28ad87e0176f10dd11c3c84bd308e1b802c571ae8d568 notes/design/2026-10-02-source-call-scheduling-choice.md
750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0 notes/design/2026-10-06-nested-block-function-source-realization-addendum.md
1084618662cf885991f83e3d41a901d0d429531bb742a1c0c2f91b8a998ec0ef notes/progress/2026-10-12-intrusion-admitted-two-use-witness.md
943dcab6440ffb70061f08641afa13fa8b36c5689a326d07288b9593e17ba8f5 crates/yu-hir/src/module.rs
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed crates/yu-hir/src/module/local_source.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49 crates/yu-solver/src/candidate_source.rs
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35 crates/yu-solver/src/candidate_call.rs
cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411 crates/yu-solver/src/shadow_apply.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94 crates/yu-solver/src/lib.rs
```

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-12-application-c-source-bridge.md`.
- Baseline SHA: `b4c46cf05bc62a53b61141605686be2177b82358`, primary-supplied;
  branch/revision equality must be revalidated by primary before integration.
- Changed dependency hashes: none by this producer; snapshot above.
- Claim/review: frozen bounded source bridge; fresh independent
  `compiler_referee` worker `/root/application_c_source_bridge_review` reported
  PASS with no blocking, major or minor finding. Effective review
  model/effort are unknown. Review was limited to cited constructor mapping and
  the missing D/P evidence; it did not establish baseline equality, exact-byte
  reachability, production routes, exhaustive source acceptance, H_f, L4 or
  complete Call. No theorem closure or implementation authority is claimed.
- Checks already run: static constructor/source-law reads and SHA-256 snapshot;
  no executable inference/checker verification. No Git operation performed.
- Proposed message: `research: map Application c lowering and missing whole-Function check`.
- Shared deltas intentionally left to primary/curator: record c's actual
  finite D/P comparison and A_f/I_x identification as missing construction
  evidence; retain H_f/L4/complete Call and production gates OPEN. No shared
  task/index/authority/question/configuration paths changed.

Writes stop at handoff; frozen report requires fresh review before promotion.
