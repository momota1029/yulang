# First runnable role-qualified method call: decision draft

Date: 2026-10-19  
Status: Draft; syntax meaning and role-call laws are unadopted  
Sprint: `effect-hygiene-role-call-20261019-r80`, revision 2  
Contract SHA-256: `e7ff179d48156bf3aa897c4e8f186916936a6b0bbcea7bc0314cad3a7e7f110e`  
Baseline: `af3ccf2d63ba7f87e0359e183568db548ea53307`  
Reviewed-by: pending independent compiler/source and spec/design review  
Approved-by: none

## Proposed first runnable surface

The first method call uses an explicit role and member qualifier:

```yu
role SecondInt {
    my second: int -> int -> int
}

impl int: SecondInt {
    my second self selected = selected
}

my answer = SecondInt::second 1 2
```

The proposed result is `answer == 2`. `SecondInt` identifies the member set; `impl int: SecondInt` provides that member for an `int` receiver. `1` is the receiver and `2` is the ordinary explicit argument. The selected target is an exact source-owned `(ImplId, MemberId)` reached through validated role/member and receiver-type evidence. A bare global name `second` is not an executable identity.

This is a role-qualified method proposal, not an adopted rule. Parser acceptance of `SecondInt::second` as a path, if confirmed, would establish syntax only. It would not establish role lookup, receiver selection, ordinary Call typing or execution. General `1.second(2)` remains OPEN: this pilot chooses no field/method precedence or collision rule.

The first implementation slice should carry the selected member into the ordinary curried Call path. It must retain the original source occurrence and provenance on each generated edge, pass the receiver as the first ordinary argument, and preserve the existing argument construction and receiving behavior. It may not add a special method evaluator.

## Complete decision cases

Each outcome below is a Draft proposal. A playground's temporary inability to execute valid source is an availability result, not a language diagnostic.

### Unique member

Use the complete `SecondInt` program above. Exactly one validated implementation matches `(int, SecondInt, second)`; the first runnable result is `2`.

### Missing role

```yu
my answer = MissingInt::second 1 2
```

Proposed outcome: unresolved role `MissingInt`, anchored at the role qualifier. Do not search another role with a `second` member or fall back to a global value. This case is distinct from a role that exists but lacks `second`.

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

Proposed outcome: unresolved member `multiply` within `SecondInt`, anchored at that member occurrence. Do not select `second` or run a body.

### Missing implementation

```yu
role SecondInt {
    my second: int -> int -> int
}
my answer = SecondInt::second 1 2
```

Proposed outcome: `SecondInt.second` exists but no implementation matches receiver type `int`. Report the role/member and receiver source anchors. This is distinct from missing role and missing member.

### Duplicate implementation key

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

Proposed outcome: reject the duplicate `(int, SecondInt)` implementation at declaration validation, retain both source locations, and admit neither body. Declaration order is not a tie-breaker. The user must choose whether duplicate rejection is the adopted language rule.

### Same member spelling in two roles

```yu
role SecondInt {
    my choose: int -> int -> int
}
role FirstInt {
    my choose: int -> int -> int
}
impl int: SecondInt {
    my choose self selected = selected
}
impl int: FirstInt {
    my choose self selected = self
}
my second_answer = SecondInt::choose 1 2
my first_answer = FirstInt::choose 1 2
```

Proposed outcomes: `second_answer == 2`; `first_answer == 1`. The role qualifier selects the requested member set. This does not settle an unqualified `1.choose(2)` call.

## Entry roles and effect behavior

The governing source decision is charter §21: an unannotated `x` or ordinary `x:A` has `Value(A)` entry; `x:[E] A` and `x:[_] A` have `Computation(E,A)` entry. Calls build each whole argument computation inertly. Value entry forces and rebinds it once inside the receiving activation before the body, even when unused. Computation entry retains its carrier for explicit body consumption. Body use, a solved-empty row or latent representation does not choose a different role.

### Effectful receiver and argument: Value entry

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

Draft expected behavior: both arguments are first constructed inertly. Their two formals are Value formals under §21. Ordinary curried application supplies the receiver first, then the explicit argument; each is forced and rebound at its own receiving activation before that stage's body. The proposed observable order is `observe(1)`, then `observe(2)`, then result `2`. A method lookup itself runs neither operand. This order must be derived from and checked against the ordinary Apply consumer before adoption; this draft does not claim that proof.

### Explicit Computation entry

```yu
act io:
    our observe: int -> int
role RunComp {
    my run: int -> [_] int -> int
}
impl int: RunComp {
    my run self (action:[_] int) = 0
}
my answer = RunComp::run 1 (io::observe 3)
```

Draft expected behavior: `self` is Value; `action` is Computation because the executable binder itself carries the explicit outer annotation. Since the body ignores `action`, it does not request `observe(3)`. A role signature alone does not annotate or change an implementation binder. No signature-to-binder role inheritance is proposed.

### Outward request

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

Draft expected behavior: the member body issues `io::tick 1`. Without an enclosing handler, the request remains outward. Qualification and member selection do not consume the request, its continuation, or another receiver's permission. This source example is proposed; the reviewed R78 traces are conditional on their own exact `LocalSource` projections and do not prove this member-body path.

## Candidate effect-hygiene frontier

The accompanying proof artifact must report evidence, first missing premise and exact source owner separately for each frontier:

1. Direct matching-handler selection and arm priority.
2. Computation-carrier retention versus Value entry.
3. Wrong or sibling receiver permission.
4. Shallow unmatched outward requests.
5. One concrete continuation capture/transport/resumption path, including whether a protected sibling remains protected.
6. One static-to-runtime operation path through annotation, HIR/candidate evidence, native `K,D` or residual ownership, and execution.

R78 supplies conditional runtime evidence for direct selection, permissions, discard and outward request over its three exact fixtures. It does not supply authentic source projection, arbitrary continuation resumption, native `K,D` correspondence, residual typing or universal hygiene. R79 identifies the unpinned `parse_root` boundary and leaves all three source projections OPEN. The new proof must preserve those statuses unless it supplies the missing premise from an admitted source owner and obtains independent review.

The frontier map is not six completed proofs. The constructive core is the role-call-to-ordinary-Call simulation. Continuation/root-dispatch exploration together is capped at 300 seconds; exhaustive storage/fiber/capture inventories are out of scope. Any native or parser source outside the frozen manifest stays OPEN/uninspected until Luna adds an exact pin. Keep the original source domain and A/B quantifiers unchanged.

## Source-to-runtime ownership proposal

1. Preserve the exact role-qualified source occurrence and parser declaration occurrences; parsing alone adds no meaning.
2. Assign source-owned identities to role, impl and member occurrences. Validate the role member signature and impl body before publishing a candidate.
3. Preserve each validated member body as an executable source root with lexical environment, annotated formals, bindings and occurrence identities.
4. Resolve the qualified role/member and receiver type to one validated `(ImplId, MemberId)`. Missing and duplicate outcomes retain their source anchors. Name-only lookup and declaration-order fallback are forbidden by this proposal.
5. Elaborate the selected body into ordinary curried Call/Apply edges, receiver first, with source provenance retained on both sides. This proposal depends on the existing Call formation/typing obligations; generated Apply edges alone are not a typing rule.
6. Extend candidate admission only for complete validated declaration metadata and member roots. Existing effect-declaration placeholders do not by themselves admit roles, impls or executable member identities.
7. Carry validated metadata and the exact selected identity into `RuntimeProgram`; reject incomplete targets before publishing a partial program; execute through existing Apply, receiving and handler machinery.

These are proposed ownership seams, not a statement that any of them already works. The first implementation contract must pin every exact reached owner, test/fixture path and hash as a coherent vertical slice.

## Future-only first-run commands

The pinned package is `yu-playground`; its current CLI declares `--run DEFINITION [SOURCE.yu]`. After explicit adoption and a new Stage 2 contract, the proposed first focused test and CLI smoke command are:

```sh
cargo test -p yu-playground --test runtime_module_expressions role_qualified_member_call_returns_expected_integer
cargo run -p yu-playground -- --run answer tasks/agent-loop/fixtures/r80-role-call.yu
```

Neither the test nor fixture exists by virtue of this draft, and neither command is authorized or run in Stage 1.

## Decisions for the user after review

1. Adopt `Role::member receiver args` as the first runnable role-qualified method surface, leaving `receiver.member(args)` for a later collision decision?
2. Adopt the receiver as the first ordinary argument stage, preserving §21 Value/Computation entry and ordinary curried Call behavior?
3. Treat duplicate `(receiver type, role)` implementations as declaration-time errors, with both locations retained?
4. Use role/member/receiver source anchors as proposed for the three distinct missing-role, missing-member and missing-implementation diagnostics?

Independent review checks completeness and conformance; it does not make these choices for the user. No semantics, implementation or production path is adopted here.
