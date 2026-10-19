# Executable method and role pilot — decision draft

Date: 2026-10-19  
Status: Draft; no method or role semantics adopted  
Scope: one concrete method call using existing FieldTail, role and impl syntax  
Authority: R78 contract `tasks/agent-loop/sprints/effect-hygiene-executable-method-role-20261019-r78.md`, SHA-256 `bf68454c19a7b4cfe5168355e0e5fb73beec069ad57dd53678258a66f26dfcab`  
Reviewed-by: pending fresh compiler/source and spec/design review  
Approved-by: none

## Why this is the next surface slice

The parser already retains `receiver.method` as a `FieldTail`, and parses standalone `role` and `impl` declarations. The R76/R77 work joins those nodes to their original parser positions; the proof is a source-correspondence result, not dispatch. The ordinary local source form has `Apply`, `Name`, `Lambda`, `Block`, `Catch`, literals and related forms, but no field selection, method call, role lookup or impl lookup. `RuntimeProgram` likewise compiles ordinary applications and handlers, not methods.

Relevant current forms:

```text
my answer = 1.second(2)

role SecondInt {
    my second: int -> int -> int
}

impl int: SecondInt {
    my second self selected = selected
}
```

The grammar can retain the declarations and postfix syntax. The example has no approved lowering or execution meaning. In particular, the optional `ImplDescription` is syntax whose semantics are outside `impl-shell.md`; treating it as the implemented role is a new decision.

## Proposed pilot rule

For one module-local, concrete pilot only, read the example as follows:

1. A `RoleDeclaration` names one required member signature. For this pilot, `SecondInt` requires `second : int -> int -> int`.
2. An `ImplDeclaration` with head `int` and description `SecondInt` supplies one implementation for that role. Its `second` binding must satisfy the role member signature. This draft gives the optional description that new meaning; current syntax authority does not.
3. At `1.second(2)`, evaluate the receiver once, then explicit arguments once from left to right. Select an implementation by the exact receiver type, role, and member spelling. Pass the receiver as the first ordinary function argument, then the written arguments. The elaborated computation is equivalent to `second 1 2`, represented by ordinary Apply nodes, with no new runtime opcode. The expected value is `2`.
4. Existing field access keeps precedence when the same receiver has a field named `second`; a call through that value remains ordinary field-then-Call behavior. Method lookup is the fallback only when field lookup finds no member. Otherwise, form candidates from module-visible role declarations and impls whose exact receiver type and role-member name match. The written method spelling does not select a role; zero candidates is unresolved and more than one is ambiguous. Diagnose both before evaluation. This pilot excludes imports, inheritance, generic heads, and coercions.
5. Do not search parent roles, coerce receiver types, use declaration order to break ties, or infer a method from a matching body shape in this pilot.

These choices aim to preserve a callable field's existing interpretation, make the implicit receiver visible in the ordinary call model, and reject ambiguous lookup deterministically. They remain proposals. They do not derive from parser acceptance or the current playground evaluator.

## Examples and falsifiers

Successful pilot: the declarations above make `1.second(2)` produce integer `2` after the complete path below is implemented and approved. It exercises receiver insertion and explicit argument passing without depending on an operator implementation.

An effect case uses a member whose body emits a declared operation:

```text
act io:
    our tick: int -> int
role TickInt {
    my run: int -> () -> [io] int
}
impl int: TickInt {
    my run self ignored = io::tick self
}
my request = 1.run(())
```

A method call that returns an unhandled `io::tick` request must preserve that request outside method execution, just as an ordinary function body does. A handler may then consume that request through the existing operation path. The effect case is a required implementation regression after approval; it is not evidence in this design draft.

Reject or diagnose each of these:

- missing `add` member for receiver type `int`;
- two applicable `AddInt` implementations for `int`;
- a field named `add` whose value is callable, which must retain field-then-Call precedence;
- an effectful receiver or argument, which must be evaluated exactly once in the stated order;
- a role signature mismatch in an impl body;
- an unhandled operation raised by the selected method body, which must remain outward.

The proposal is falsified if receiver and argument effects are duplicated or reordered, a callable field changes meaning, a wrong/ambiguous impl executes, the generated call changes ordinary argument order, or an outward operation disappears.

## Candidate source-to-execution path

1. **Parser:** reuse the established `FieldTail`, `RoleDeclaration` and `ImplDeclaration` grammar. Add only the missing grammar if the exact examples do not parse; parser changes need their own scoped reviewed gate.
2. **Source/HIR:** retain branded source occurrence and exact receiver/member ranges. R77 proves the receiver is constructor child zero and joins role/impl declarations to same-file parser nodes, conditionally on its source snapshot. Rev1's focused command failed only because a source slice expected `"b"` while the constructor range correctly included leading trivia (`" b"`). Error ownership also needs its reviewed rev2 repair before any implementation depends on that API. Rev2 is inactive; preserve this failure receipt.
3. **Resolution:** add a source-owned method/role/impl index and an explicit unique/none/ambiguous result. Keep the field-first decision visible in the produced evidence. A role body and an impl description cannot be treated as semantic entries until their new laws are adopted.
4. **Inference:** lower a successful lookup to the exact ordinary curried application with the receiver as first argument, retaining source ownership and normal constraints. The original ordinary Call formation obligation remains OPEN; the unadopted 2026-10-17 proposal is a gap locator, not authority.
5. **Provisional execution:** if the ordinary application reaches the existing inference-playground source form, execute its generated Apply nodes using the existing runtime. This demonstrates the bounded evaluator path only. It is not production execution or proof of full source typing/correspondence.
6. **Verification after approval:** add source tests for unique/missing/ambiguous lookup, field collision, single evaluation and order, signature mismatch and an outward operation. Then run focused verification on the HIR/inference/playground owners under a new contract.

## Approval boundary

Independent compiler/source and spec/design reviewers must first review this draft and its source-owner map. Their review does not adopt it. The user must approve the decisions on declaration meaning, impl description, lookup key, field precedence, ambiguity, evaluation order and role signature checking before any source or runtime behavior changes. An implementation contract must then lease the parser/HIR/inference/playground owner files and specify expected diagnostics, test cases and verification commands. The current R78 contract grants no such lease.

The proposed design does not close complete ordinary Call formation, method/role source correspondence, effect hygiene, Simple-sub, evaluator, A/B or production gates. Parent and A/B remain OPEN 0→0; R50 remains NOT_ADOPTED.
