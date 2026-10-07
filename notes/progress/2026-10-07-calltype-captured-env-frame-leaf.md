# CALL_TYPE: captured argument adequacy at the returned callee world

Date: 2026-10-07
Baseline: `8c214054b252f2dd0451f3fb5ba557e323e73def`
Status: bounded CI-ArgFrame refinement; no semantic rule adopted
Authority: none; CALL_TYPE remains CONDITIONAL-CLOSED
Review: spec-auditor PASS; compiler-referee major finding repaired and delta PASS

## Exact frame obligation

For the fixed source argument `result(name x)`, typed-core §6 supplies the
structural facts:

```text
Gamma(x) = Value(A_x)
J_x = Return(lookup_rho x)
Result(Value(A_x)) = Comp(empty,A_x)
```

Keeping `rho`, the resolved occurrence and the lexical lookup's provider
identity intact through callee execution proves static binding identity. It
does not prove that the provider's references, live contents, latent providers
or future callable obligations remain adequate in the callee's actual return
world `C1`.

Fix original `X`, `xi=(nu,K,D)`, binder/scope tree, `rho`, `r_x`, `A_x`, and the
caller's argument/callee incidences. The missing proof interface is:

```text
Gamma(x)=Value(A_x)
lookup_rho(x)=v_x at original root r_x
wa: one original jointly admitted CI-Operands witness at fixed (X,xi,scope)
e_x0: captured-binding/world adequacy at (C0,xi;wa), with call/provider inputs
t_f0: Typed_X(R_f,J_f,C0;wa)
d_f: actual admitted callee development J_f(C0) -> Return(actual_f,C1)
     retaining its state transitions, responses, resumptions and scopes
for each retained CalRet witness wf >= wa, including
          World_X(C1;wf) and CallableMem_X(U,actual_f,C1;wf)
-----------------------------------------------------------------
CapturedEnvFrame_x [required, not supplied]

exists compatible w1 >= wf.
  retained CalRet facts remain established
  AND the original x-binding has independently interpreted
      value/provider/captured-dependency adequacy at actual C1
  under unchanged X,xi,rho,r_x,A_x and original scopes.
```

This names the relevant projection of the existing joint environment/world
predicates. It does not define a weaker environment predicate by deleting
other conjuncts. The dependency support includes aliases, references and
latent providers required by `A_x`, not just direct lexical lookup.

With independently justified Name elimination and Return introduction at
`C1`, the frame can supply `Typed_X(Comp(empty,A_x),J_x,C1;w1)`. It still does
not supply the other CI-ArgFrame conjunct:

```text
ArgCompatible_X(R_arg,CarrierContract(U);w1)
```

That requires sound evidence for the original whole-carrier check against the
actual returned provider `U`, at a compatible extension preserving both the
CalRet and captured-argument facts. Separate existential extensions for
typing and compatibility do not automatically join; neither do they require
every possible extension pair to join.

## Source and rule boundary

The inspected sources provide no rule for `CapturedEnvFrame_x`:

- Source contracts §§3.3–3.5 keep current-state responses/future uses as
  independent inputs; §3.4 transports scoped coordinates and supplied
  evidence, and §3.5 assumes local typing. The §3.1 Theorem-C source envelope
  excludes mutable cells, so that conditional theorem cannot instantiate this
  frame for mutable state-changing worlds.
- Typed-core §6 emits the computation skeleton but does not establish its
  constraint interpretation. §8 transports an already supplied certificate
  covering the relevant executions/stores. §9 uses current state and retains
  supplied typed correspondences but proves no environment/store preservation.
- CALL_TYPE's CalRet supplies current-world and returned-callee membership;
  it does not supply adequacy of `x`'s captured dependency graph at `C1`.
- STATE_RW, STATE_RESUME and REF_WORLD retain replacement/restart,
  current-resumption and EnvStore/JointWF preservation as separate open work.
- Current Yulang3 application collection stores `ApplicationTypingRuleUnresolved`;
  it does not semantically collect the retained Apply operands. The HIR marker
  carries neither `C1` nor provider/world evidence.

A viable proof must preserve the actual callee development, including any
state replacement/restart, reference changes, latent dependencies, responses,
raw resumptions and activation expiry. It must not assume `C1=C0` or freeze a
mutable provider's C0 contents. This is a required proof interface, not a new
language rule or a compiler inference recipe.

## Disposition

| Gate / subcase | Before | After | Result |
|---|---|---|---|
| CALL_TYPE | CONDITIONAL-CLOSED | CONDITIONAL-CLOSED | Full composition remains conditional on uninstantiated local laws. |
| CI-ArgFrame, fixed Name/Name | OPEN within the conditional premise set | OPEN within the conditional premise set | Its typing conjunct requires `CapturedEnvFrame_x` at actual C1; actual-provider whole-carrier compatibility remains separate. |
| CI-ArgFrame, general Call | OPEN | OPEN | Receipt, phase, Bind, response/resume, future-provider and shared-witness requirements remain. |

The original retained `CalRet` witness, provider, `xi`, source scopes and
incidences remain fixed throughout. No actual source instance or semantic
predicate is proven here; no DAG node, edge or status changes.

## Checks and limits

Governing sources: canonical successor DAG `CALL_TYPE`, `SEM_JOINT`,
`STATE_RW`, `STATE_RESUME` and `REF_WORLD`; `notes/progress/2026-10-07-call-original-rule-round3.md`
§2.1; source contracts §§3.1, 3.3–3.5; typed-core §§6, 8–9; SCC intrusion
charter §17; and the current collection/marker paths in
`crates/yu-solver/src/lib.rs`, `crates/yu-hir/src/shadow.rs` and
`crates/yu-core/src/shadow_derivation.rs`.

Three complementary attacks were used: conditional frame
construction, witness-splitting falsification, and current producer-path
inspection. Their reports identify no source rule or producer that supplies
this frame. Independent compiler-referee and spec-auditor reviews found the
contract and claim scope conformant; a major shared-witness-index finding was
repaired and passed delta review. No code, tests, builds, Oracle inspection,
executable model, or Git mutation was used.
