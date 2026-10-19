# First role-qualified receiver call — decision draft

Date: 2026-10-19  
Status: Draft; syntax meaning and role laws are unadopted  
Sprint: `effect-hygiene-role-call-20261019-r79`, contract SHA-256 `0ad36f8f9efb6e9fab326cd7df35e553c6baa9b1dd721e277a8ac184c774e479`  
Baseline: `af3ccf2d63ba7f87e0359e183568db548ea53307`  
Reviewed-by: pending fresh independent compiler/source and spec/design review  
Approved-by: none

## Why qualify the first call by role

Two candidate surface forms are under consideration:

```yu
SecondInt::second 1 2
1.second(2)
```

The first form explicitly names the role and member and passes the receiver as the first ordinary argument. It can make one role-backed call runnable without first choosing a general rule for whether `x.member(...)` means field projection followed by Call or role dispatch. The second form is closer to method syntax, but its field/method precedence and collision domain need a real, source-valid example before that decision can be made. R78's attempt to claim collision readiness failed independent review; this proposal does not reuse or narrow that R78 claim. It leaves general dot-field collision OPEN.

The role-qualified notation may already be accepted by the parser as a path. That fact would establish only syntax; the role/member interpretation below remains a new choice. Both forms and all outcomes here are Draft. Neither parser acceptance nor an executable candidate establishes the ordinary source Call typing rule, source/native correspondence, or user approval.

## Candidate unique call

```yu
role SecondInt {
    my second: int -> int -> int
}

impl int: SecondInt {
    my second self selected = selected
}

my answer = SecondInt::second 1 2
```

Candidate result: `answer` is integer `2`. `SecondInt` identifies the required member set; the `impl int: SecondInt` supplies the implementation. The first explicit argument, `1`, is the receiver and the second, `2`, is the member's explicit argument. The selected callee is the exact source-owned `(ImplId, MemberId)` reached through a validated `(RoleId, receiver type)` relation. A spelling-only global `second` is not an executable identity.

Proposed call construction: elaborate the qualified target to the validated member and elaborate the receiver and remaining arguments through the ordinary curried application path, preserving the qualified source occurrence and provenance for every generated edge. This is a design hypothesis. It cannot be used as a substitute for the still-open ordinary Call formation and typing obligations.

## Exact case matrix

All errors below are proposed language diagnostics. A provisional playground refusal for otherwise valid source is a separate availability result, not a language error.

### Unique member

Use the complete source above. One implementation matches `(int, SecondInt, second)`, so the call returns `2` after implementation and user approval. The first runnable fixture should use this exact example.

### Missing member

```yu
role SecondInt {
    my second: int -> int -> int
}
impl int: SecondInt {
    my second self selected = selected
}
my answer = SecondInt::multiply 1 2
```

Proposed outcome: unresolved member `multiply` in `SecondInt`, anchored at the qualified member occurrence. Do not silently select `second`, search another role, or run a body.

### Missing implementation

```yu
role SecondInt {
    my second: int -> int -> int
}
my answer = SecondInt::second 1 2
```

Proposed outcome: role member exists but no implementation for receiver type `int`; diagnose at the receiver/qualified call with the role and receiver source ranges. This keeps member lookup separate from implementation lookup.

### Duplicate implementation for the same key

```yu
role SecondInt {
    my second: int -> int -> int
}
impl int: SecondInt {
    my second self selected = selected
}
impl int: SecondInt {
    my second self selected = self
}
my answer = SecondInt::second 1 2
```

Proposed outcome: duplicate/conflicting implementation for `(int, SecondInt)`; report both implementation occurrences and execute neither. Declaration order is not a tie-breaker. Whether this is diagnosed on the second declaration or at each use is a separate diagnostic-location choice for the user.

### Same-spelled member in two roles

```yu
role SecondInt {
    my choose: int -> int -> int
}
role ProductInt {
    my choose: int -> int -> int
}
impl int: SecondInt {
    my choose self selected = selected
}
impl int: ProductInt {
    my choose self selected = self
}
my second_answer = SecondInt::choose 1 2
my product_answer = ProductInt::choose 1 2
```

Proposed outcomes: the first call returns `2`, the second `1`. The role qualifier identifies the intended role; same member spelling across roles is not ambiguous here. The corresponding unqualified form `1.choose(2)` remains unresolved by this pilot until a field/method and role-selection law is chosen.

### Effectful receiver and argument; Value entry

```yu
act io:
    our observe: int -> int
role SecondInt {
    my second: int -> int -> int
}
impl int: SecondInt {
    my second self selected = selected
}
my answer = SecondInt::second (io::observe 1) (io::observe 2)
```

Proposed outcome: both operands are first constructed as inert computations. The receiver and explicit argument have Value roles under §21, so each is forced/rebound exactly once in its receiving activation before the body. The candidate observable order follows the nested ordinary application order: receiver request `observe(1)`, then explicit-argument request `observe(2)`, then body result `2`. A handler may observe and resume each request through the ordinary handler path. This order is a proposal to check against the actual ordinary Apply consumer and receiving rules; method lookup itself must not execute either operand.

### Explicit Computation formal remains retained

```yu
act io:
    our observe: int -> int
role RunComp {
    my run: int -> [_] int -> int
}
impl int: RunComp {
    my run self action = 0
}
my answer = RunComp::run 1 (io::observe 3)
```

Proposed outcome: `self` is Value; `action` is Computation because its outer annotation is explicit. Entry retains `action`'s carrier and does not request `observe(3)` because this body ignores it. If a body consumes it, that follows the existing source computation-consumption rule; this proposal adds no `force` syntax. The role cannot be inferred from use or solved effect support.

### Outward request from the selected member

```yu
act io:
    our tick: int -> int
role TickInt {
    my run: int -> () -> [io] int
}
impl int: TickInt {
    my run self ignored = io::tick self
}
my answer = TickInt::run 1 ()
```

Proposed outcome: the selected method body issues `io::tick 1`. Without an enclosing handler, the request remains outward; an existing handler may consume it. Qualification and member selection do not drop the request, consume its continuation, or transfer it to another handler. Existing R78 runtime evidence is conditional and does not prove method-body source projection or native hygiene for this example.

### Invalid and unsupported source

Malformed role/impl syntax receives its parser diagnostic and creates no declaration identity. A syntactically valid but unsupported declaration form is not rejected as invalid language syntax merely because the provisional playground cannot execute it. A failed role-signature/impl-body check is a source type diagnostic and prevents all-or-nothing executable admission. These are distinct from missing member and missing implementation diagnostics above.

## §21 entry and effect-hygiene boundary

The pinned charter §21 fixes source parameter roles by the outer annotation: `x` and ordinary `x:A` are Value; `x:[E] A`, including `x:[_] A`, is Computation. Every call constructs the whole argument computation inertly. Value formals force and rebind once in their receiving activation before the body, even if unused or effectful; explicit Computation formals retain the carrier for explicit body consumption. Body usage, an empty row, or a solved latent representation does not change the role. The candidate role signature uses the ordinary curried function stages and does not add special method evaluation.

The U/O/S proof lane is separately bounded to authenticating the source constructors for three existing effect fixtures and composing that with the conditional runtime trace. Its first obstruction leaves the general effect-hygiene gate OPEN. Neither the proof nor these draft examples closes native K/D, residual typing, arbitrary continuation resumption, or universal effect preservation. No storage/fiber detour follows from an open premise.

## Complete owner path and missing work

1. Preserve the exact qualified path/source occurrence and existing role/impl parser nodes. Parser acceptance supplies no semantics.
2. Elaborate source-owned `RoleId`, `ImplId` and member identities tied to exact module and parser occurrences. Reject malformed syntax before publication.
3. Validate role member signatures and every impl body against its role, receiver type and §21 formal roles. Failed validation is diagnostic and prevents declaration admission.
4. Materialize each validated member body as an executable source root with lexical environment, formal bindings, occurrence identities and captures resolved by ordinary source rules.
5. Resolve `Role::member` to one validated role/member, then select exactly one implementation for the receiver's source type. Missing/duplicate outcomes retain candidate source ranges. No name-only global and no declaration-order fallback.
6. Elaborate the selected member invocation to ordinary curried Apply edges with receiver first, then written arguments, preserving original qualified-source provenance in both directions. Ordinary Call formation remains a parent proof obligation; generated Apply alone is not a typing rule.
7. Extend `CandidateInference` admission at its source/placeholder preflight owner to accept only complete validated declaration metadata and member roots. Current effect-declaration placeholder registration does not admit roles, impls or member executable identities.
8. Carry the validated declaration table and exact `(ImplId, MemberId)` into `RuntimeProgram`; reject unvalidated/missing targets before publishing a partial program. Execute through existing Apply, receiving and handler paths so outward requests preserve their selected handler and continuation semantics.

The first implementation contract should lease these producer/admission/runtime seams together or freeze a reviewed interface across them. Its first command should compile and run only the unique `SecondInt::second 1 2` fixture and assert result `2`; subsequent authorized cases add missing/duplicate roles, §21 retention, request order and outward handling. The present contract authorizes none of those commands.

## Decisions for the user

1. Should the first role call explicitly qualify the role, using `Role::member receiver args`, so it can run before general dot-field collision rules are settled?
2. Should a duplicate implementation for one `(receiver type, role)` be a declaration error or a use-site ambiguity diagnostic?
3. Does the receiver remain the first ordinary Value/Computation formal stage, subject to §21 and ordinary curried Apply order?
4. Which missing-role/member and impl-body mismatch diagnostic locations are preferred?
5. Should general `receiver.member(args)` field precedence remain a later, separately reviewed design decision?

Independent reviews do not answer these user choices. The proposed vertical slice is useful only after those choices and any required specification updates are approved. No semantics, implementation or production path is adopted here.
