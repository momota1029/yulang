# R82 role-qualified call: adoption draft

Date: 2026-10-19  
Status: Draft; all new role-call rules remain unadopted  
Sprint: `effect-hygiene-role-call-20261019-r82`, revision 1  
Contract SHA-256: `a11cd61b71548ce144f60557c3c8b6fe32d3cce698b4dd58657fb6e33d85adce`  
Compatibility definition SHA-256: `1f6630f29ba79e72be87890445baadf7e6df5ba0091654c6095dca04fb56ec16`  
Baseline: `af3ccf2d63ba7f87e0359e183568db548ea53307`  
Reviewed-by: pending fresh compiler/source and spec/design review  
Approved-by: none

## Proposed first role-qualified method call

```yu
role SecondInt {
    my second: int -> int -> int
}
impl int: SecondInt {
    my second self selected = selected
}
my answer = SecondInt::second 1 2
```

Draft result: `answer == 2`. `SecondInt::second` identifies a role member; the
receiver's `int` type selects a validated implementation. Its exact source
identity and executable body must become an ordinary curried Call/Apply target,
with receiver as the first argument stage. The member body keeps its lexical
environment and original binder annotations. No special method evaluator or
signature-to-binder role inheritance is proposed.

This path does not choose `receiver.member(args)`, field/method precedence, or a
general dot lookup rule. The initial surface is explicitly role-qualified so
the first executable path can be built without deciding that separate lookup
question. Parser acceptance alone would establish syntax, not target
validation, ordinary Call typing or runtime execution.

## One shared compatibility rule

All examples, proof claims and outcomes in this document use the exact
three-way definition in `notes/design/2026-10-19-r82-role-call-compatibility.md`
(SHA-256 recorded above). In summary, this pilot supports a monomorphic
module-local role/member with an `int` Value receiver, one or more parameters
from the fixed set `int`/`() ` Value or explicitly annotated `[_] int`
Computation, and an `int` result. Compatibility yields exactly:

- **Compatible:** supported arity, endpoints, result and roles agree. This
  allows ordinary checking to continue; it does not itself create an
  executable method.
- **Incompatible:** both sides are supported, but arity, endpoint or role
  differs. Reject this implementation before executable member admission.
- **Unsupported:** either side uses an excluded form. Do not admit it through
  the provisional pilot and do not claim the general language rejects it.

An executable binder's own outer annotation fixes its Value or Computation
role under charter §21. The signature never supplies that annotation. A
conversion requires an explicitly selected adapter with separately defined
behavior; this pilot inserts no adapter. The shared definition is the sole
authority for the R82 examples and proof—this summary does not add cases.

## Complete supported and discriminating cases

### Compatible pure call

```yu
role SecondInt { my second: int -> int -> int }
impl int: SecondInt { my second self selected = selected }
my answer = SecondInt::second 1 2
```

Both executable binders are unannotated Value binders with ordinary `int`
endpoints. The compatibility result is Compatible; after ordinary inference,
call generation and admission succeed, the proposed result is `2`.

### Compatible Computation parameter

```yu
act io:
    our observe: int -> int
role RunComp { my run: int -> [_] int -> int }
impl int: RunComp { my run self (action:[_] int) = 0 }
my answer = RunComp::run 1 (io::observe 3)
```

The role slot and executable binder both explicitly declare Computation entry.
Under §21 the `action` carrier is retained; because this body ignores it,
`observe(3)` is not requested and the proposed result is `0`.

### Supported Value/Computation mismatch

```yu
role RunComp { my run: int -> [_] int -> int }
impl int: RunComp { my run self action = 0 }
```

Classification: Incompatible. The signature slot is Computation while the
unannotated executable binder is Value under §21. Reject this implementation
before executable admission. The binder must not inherit a signature
annotation. The symmetric pair—a Value signature and explicit `action:[_]`
binder—is also Incompatible.

### Supported arity and endpoint mismatches

```yu
role OneArg { my run: int -> int -> int }
impl int: OneArg { my run self first second = 0 }
```

Both declarations use supported Value/int slots, but their arities differ, so
the classification is Incompatible and the implementation does not enter the
executable member set.

```yu
role UnitArg { my run: int -> () -> int }
impl int: UnitArg { my run self (value:int) = 0 }
```

Both endpoints are within the supported set, but `()` and `int` differ. The
classification is Incompatible. No cast or implicit adapter follows.

### Unsupported form

```yu
role BoolArg { my run: int -> bool -> int }
impl int: BoolArg { my run self (value:bool) = 0 }
```

Classification: Unsupported because the Boolean parameter is outside this
pilot. This does not assert that the source is generally ill-typed or rejected;
the provisional role-call path simply cannot publish a target from it.

## Resolution outcomes

Each outcome below is a Draft category. It does not alter current diagnostics
or authorize a fixture expectation change.

Missing role:

```yu
my answer = MissingInt::second 1 2
```

Proposed category: `MissingRole`, anchored at `MissingInt`. Do not search other
roles or global values.

Missing member:

```yu
role SecondInt { my second: int -> int -> int }
impl int: SecondInt { my second self selected = selected }
my answer = SecondInt::multiply 1 2
```

Proposed category: `MissingMember` within `SecondInt`; do not execute a body.

Missing implementation:

```yu
role SecondInt { my second: int -> int -> int }
my answer = SecondInt::second 1 2
```

Proposed category: `MissingImplementation` for the `int` receiver. This is
distinct from missing role and missing member.

Duplicate implementation key:

```yu
role SecondInt { my second: int -> int -> int }
impl int: SecondInt { my second self selected = selected }
impl int: SecondInt { my second self selected = self }
my answer = SecondInt::second 1 2
```

Proposed category: reject the duplicate key before member admission and retain
both declaration locations; declaration order is not a tie-break.

Same member spelling in two roles:

```yu
role SecondInt { my choose: int -> int -> int }
role FirstInt  { my choose: int -> int -> int }
impl int: SecondInt { my choose self selected = selected }
impl int: FirstInt  { my choose self selected = self }
my a = SecondInt::choose 1 2
my b = FirstInt::choose 1 2
```

Proposed results are `2` and `1`. The role qualifier keeps the member
identities distinct. This does not make `1.choose(2)` unambiguous.

General dot method calls and callable-field collisions stay OPEN and outside
this pilot. There is no dot syntax precedence proposal in this document.

## Effect request prefix and bounded hygiene evidence

The ordinary effect outcome follows charter §21 and the pinned ordinary
Apply/runtime consumers. In this complete candidate:

```yu
act io:
    our observe: int -> int
role SecondInt { my second: int -> int -> int }
impl int: SecondInt { my second self selected = selected }
my answer = SecondInt::second (io::observe 1) (io::observe 2)
```

Both argument computations are built inertly. The receiver is the first
ordinary application stage and its `self` binder is Value. Without a handler,
`observe(1)` escapes before the first Value entry returns. The saved suffix
retains the pending receiver entry and later application. The second formal has
not entered; `observe(2)` and result `2` do not follow. A resumed later trace
requires an explicit supported handler and proof of its exact suffix; none is
claimed here. Do not change existing unhandled-request expectations.

The six broad effect frontiers remain tracked at their existing evidence depth:

| Frontier | Bounded evidence/status |
|---|---|
| ordered matching handler | ordinary-consumer and exact R78 fixture evidence; complete source-generated membership remains OPEN |
| Value/Computation entry | §21 role rule and consumer path; role-call materialization must preserve original annotations |
| wrong/sibling permission | exact positive permission is the licensing fact; authentic protected-sibling source proof remains OPEN |
| shallow unmatched request | conditional outward request; native residual typing remains OPEN |
| continuation | one bounded capture/binder/resumption route; full template and protected-sibling preservation remain OPEN |
| static → native/runtime | conditional source/candidate/runtime path; native operation/formal and K,D/residual owners remain OPEN |

This map is not six proofs or universal effect-hygiene closure. No exhaustive
storage/fiber inventory is included. R80/R81 constructor hypotheses P1–P4
remain OPEN; the full source-to-HIR projection remains OPEN even though R81
removed the prior dispatcher inspection boundary. Parent A/B and all original
quantifiers remain unchanged.

## Source-to-runtime plan and adoption gate

The future vertical slice must carry validated declaration identities and the
member's source body/environment/binder annotations into an exact selected
`(ImplId,MemberId)`, elaborate it to ordinary receiver-first Call/Apply,
preserve original occurrence/provenance, admit only the complete validated
metadata/root, and execute through existing RuntimeProgram/Apply/receiving
consumers. Current code does not yet establish this chain. The conditional
proof is not evidence that the producer exists.

After independent compiler/source and spec/design review, ask the user to adopt
the exact bounded compatibility definition and role-qualified call package.
Only an explicit adoption authorizes a separate implementation contract. That
contract must pin exact constructors/consumers and focused command paths, bind
P1–P4 to producer facts, and retain the request-prefix theorem's limits. No
test, command, source edit, or production behavior is authorized by this draft.
