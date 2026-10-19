# Executable method and role pilot — decision draft, revision 2

Date: 2026-10-19  
Status: Draft; no method or role semantics adopted  
Scope: one module-local, concrete receiver/member pilot; design only  
Authority: R78 rev2 `tasks/agent-loop/sprints/effect-hygiene-executable-method-role-20261019-r78-rev2.md`, SHA-256 `5a5cca3b708b0d79b56fc0d0b48c37f4226365d53f7159eb31c1b667881323b6`  
Reviewed-by: pending fresh compiler/source and spec/design delta review  
Approved-by: none

## Goal and boundary

The next useful surface is a source form that can eventually parse, resolve, type and run one method call using existing role and implementation declarations. This draft turns the old sketch into a decision package; it is not implementation authority. The receiving/selection certificate remains conditional and OPEN at raw source to `LocalSource`; it establishes neither native residual typing nor universal effect hygiene. Method dispatch, role laws, ordinary Call formation, source/native correspondence, evaluator correspondence, Simple-sub, A/B and production remain open.

The bounded pilot excludes imports, parent roles, generic heads, coercions, extensions across modules and overload ranking. It uses exact receiver type, role identity and member identity. The method spelling alone never chooses a role.

## Proposed declarations and unique success

```yu
role SecondInt {
    my second: int -> int -> int
}

impl int: SecondInt {
    my second self selected = selected
}

my answer = 1.second(2)
```

Proposed result: `answer` is integer `2`. The `impl` description is proposed to identify the role implemented. Its member body must be checked against the role signature. The call resolves the unique implementation for receiver type `int`, role `SecondInt`, member `second`, then elaborates to the ordinary curried call `second_member 1 2`. The selected callee is the source-qualified implementation-member identity, never the bare spelling `second`.

This interpretation of `ImplDescription`, role member signatures, role implementation identity and method lookup is new. Existing parser acceptance and R77's source joins prove syntax correspondence only; they do not establish these laws.

## Case matrix: proposed outcome versus executable availability

| Case | Draft source | Proposed language outcome | Current/provisional boundary |
|---|---|---|---|
| Unique method | The declarations above, then `my answer = 1.second(2)` | Resolve one `(int, SecondInt, second)` member and return `2`. | Not executable until declaration/member materialization, typing and runtime metadata paths exist. |
| Missing target | `my answer = 1.multiply(2)` with no `int` role implementation of `multiply` | Report unresolved method at the `FieldTail` occurrence; do not evaluate receiver or arguments. | A temporary playground may instead report unavailable source admission; that is not the language diagnostic. |
| Ambiguous roles | `role First { my second: int -> int -> int }`; `role Second { my second: int -> int -> int }`; implementations for both on `int`; `my answer = 1.second(2)` | Report ambiguity with both source-qualified candidates. Do not choose by declaration order or body shape. | Must remain unavailable until a resolver can preserve candidate identities and source ranges. |
| Callable field collision | `my invoke (box) = box.second(2)` where the independently typed `box` value has a callable field `second` | Existing field resolution wins and the expression is field projection followed by ordinary Call. It is not rewritten as role dispatch. | The example fixes the decision at the shared `FieldTail` boundary; a record construction/field owner is a separate dependency and is not claimed to run in the present playground. |
| Effectful receiver and argument | Under `act io: our observe: int -> int` and the unique `SecondInt` implementation: `my answer = io::observe(1).second(io::observe(2))` | Both expressions are constructed as inert computations. Because these two pilot formals have Value roles, the receiving activations force/rebind receiver then explicit argument once, left to right, before the body. The proposed observable request order is `observe(1)`, then `observe(2)`. | Must be checked against ordinary Call entry and handler traces after approval; no eager evaluation at method lookup or during candidate construction. |
| Computation formal retention | `role RunComp { my run: int -> [_] int -> int }`; `impl int: RunComp { my run self (action:[_] int) = 0 }`; `my answer = 1.run(io::observe(3))` | The explicit computation annotation fixes `action` as `Computation`; method entry retains its carrier and does not force it. Since the body ignores it, `observe(3)` is not requested. A body that explicitly consumes the carrier follows ordinary source computation-consumption rules. | §21 is the authority. This row does not invent a `force` form or infer the role from usage/effect support. |
| Outward method-body request | `act io: our tick: int -> int`; `role TickInt { my run: int -> () -> [io] int }`; `impl int: TickInt { my run self ignored = io::tick self }`; `my answer = 1.run(())` | The selected body issues `io::tick 1`. Without a handler it remains an outward request; a surrounding existing handler may select it. Method entry neither consumes nor drops it. | Requires validated declaration metadata and the same execution/handler path as ordinary functions. No runtime receipt is claimed here. |
| Malformed declaration | `impl int: { my second self selected = selected }` | Report the parser's malformed declaration diagnostic at the declaration. Do not construct a role or implementation identity. | Syntax diagnostics and executable-admission refusals must stay separate. |
| Unsupported but valid declaration | A syntactically valid generic or imported implementation outside this pilot | The language-level syntax is not rejected merely because this pilot does not implement it. A provisional playground refuses executable admission with an availability result naming the unsupported owner. | Admission refusal is not a user-facing language type error and must not be recorded as one. |
| Unvalidated declaration | A valid `impl int: SecondInt` whose `second` body fails signature checking | Report the actual signature/type error; do not admit the declaration or any member into executable metadata. | No partial `RuntimeProgram` publication. |

`[_]` is deliberately explicit: per charter §21, `x` and `x:A` are `Value(A)`, while `x:[_] A` is `Computation(E,A)`. Every call first constructs its whole argument computation inertly. Value parameters force and rebind once within their receiving activation before the body, even when unused; Computation parameters retain the carrier for explicit body consumption. Roles are fixed by the outer source annotation, never inferred from body use, empty effect support or a solved latent row. The method receiver is the first ordinary formal; the explicit arguments follow in source order. The rows above make no blanket eager-execution claim for computation formals.

The effect cases are hygiene checks as well as surface behavior: the chosen request must retain its selected handler and continuation behavior, and an outward request must remain outward. The frozen R78 proof is conditional on authentic source projection and does not prove those type-level or universal claims. No storage, fiber, or effect-row representation expansion is needed to decide this pilot.

## Source-to-execution owner path

Every step below is a required owner seam, not an assertion that the current tree already implements it.

1. **Parse and retain source.** Reuse `FieldTail`, `RoleDeclaration` and `ImplDeclaration`; preserve branded source occurrence, source range, and exact parser node. Current `visit_role_impl_nodes` explicitly implies no semantic identity or selection rule. Add grammar only if an example is shown not to parse, under a separate reviewed parser lease.
2. **Declaration identity and admission.** A declaration elaborator must create source-qualified `RoleId`, `ImplId` and member IDs joined to the exact parser nodes and module. Validate declaration shape before publishing any identity. Malformed syntax is a parser diagnostic; syntactically valid unsupported forms are provisional admission refusals; they must not be conflated.
3. **Role signature validation.** Elaborate each required member signature under the ordinary type and parameter-role rules. Validate every implementation member against its exact role member, receiver head and source occurrence. A mismatch produces a source diagnostic and excludes the whole implementation from executable admission.
4. **Member source root and environment.** Materialize each validated body as an executable source root with its lexical environment, parameter bindings and ordinary source identity. It must have a root and environment independent of the spelling `second`; capture resolution remains the ordinary source resolver's job.
5. **Field-first resolution.** At each `FieldTail`, resolve existing field projection first. Only if no field applies, collect role/impl candidates matching exact receiver type and member. Return `None`, `Unique(ImplId, MemberId)` or `Ambiguous(nonempty source-qualified candidates)` with occurrence provenance. Never select by name alone, declaration order, coercion, parent role, body shape or effects.
6. **Ordinary application elaboration.** For the unique result, produce the ordinary curried application whose callee link names the exact selected member identity; pass receiver first, then explicit arguments. Retain the original `FieldTail` and generated-node provenance so diagnostics and source/native correspondence can join both directions. This is a proposed construction and remains downstream of the open ordinary Call formation obligation; a successful candidate encoding alone cannot license its typing rule.
7. **CandidateInference preflight and admission.** `shadow_apply.rs` delegates source/placeholder preflight to `candidate_source.rs`. Today the playground's exception is narrowly registered `source_effect_declarations()` placeholders; this does not admit Role/Impl declarations or member bodies. A future candidate gate must accept only fully validated role/impl metadata, verify all source-owner joins before solving, and refuse unsupported or unvalidated items without publishing a partial result. This admission refusal is distinct from language diagnostics.
8. **RuntimeProgram metadata and execution.** `RuntimeProgram::from_hir` currently compiles ordinary binding/expression roots and skips only registered effect-declaration placeholders; other unsupported items return `MissingSource`. A future input must carry the validated declaration table and exact member roots. Runtime construction must preserve declaration-qualified callee identity and reject an unvalidated/missing target; the selected member body then runs through the ordinary Apply/handler machinery so requests and continuations use existing semantics.

The current owners establish the gap: HIR retains pending source nodes; solver candidate admission owns placeholder preflight; the runtime admits only ordinary roots plus registered effect placeholders. No one of these owners alone completes the path. The next implementation contract must lease these seams together or explicitly split them at a reviewed immutable interface.

## First executable milestone after semantic approval

A small, early-running milestone should compile one module-local `SecondInt` fixture through parse → source-owned declaration validation → unique selection → ordinary Apply → candidate admission → `RuntimeProgram` → result `2`. It should then add the missing/ambiguous/callable-field, §21 Value/Computation, receiver/argument request-order and outward-request cases as gates. The first milestone must run a focused syntax/HIR/solver/playground command set once those exact owners and expected outputs are reviewed. Until a later contract authorizes them, no tests, probes, builds or implementation are implied by this draft.

Before implementation, a fresh decision must settle declaration meaning, `ImplDescription`, candidate key and ambiguity, field precedence, diagnostic versus admission categories, evaluation and receiver order, signature checking, and generated-call typing/provenance. Independent review of this draft is not semantic approval. After that decision, issue a bounded end-to-end implementation contract with runnable first milestone, source/test owners, exact commands, expected outputs, proof obligations and rollback owner.
