# R83 role-qualified method call and effect hygiene: adoption draft

Date: 2026-10-19  
Status: Draft; new role-call rules remain unadopted  
Sprint: `effect-hygiene-role-call-20261019-r83`, revision 1  
Contract SHA-256: `68fdfda6599d3b894482d4ef447e2940802c64ef97573a602b63abf003ff648b`  
Shared compatibility definition SHA-256: `bdf814ad1cab0bd07976b9e14079c534fe811547515a015aa8ff65d637f62af3`  
Baseline: `af3ccf2d63ba7f87e0359e183568db548ea53307`  
Reviewed-by: pending fresh compiler/source and spec/design review  
Approved-by: none

## Proposed first runnable call

```yu
role SecondInt {
    my second: int -> int -> int
}
impl int: SecondInt {
    my second self selected = selected
}
my answer = SecondInt::second 1 2
```

The proposed result is `2`. `SecondInt::second` names a role member; the
receiver's `int` type selects its implementation. A future implementation
must retain the exact source-owned selected member, body root, lexical
environment and original binder annotations, then form an ordinary
receiver-first curried Call/Apply path. It must execute through existing
receiving and runtime consumers, without a special method evaluator.

This pilot chooses the explicit `Role::member receiver args` route. It does
not decide `receiver.member(args)`, dot dispatch, field/method precedence, or
callable-field collisions. That narrower first surface is intended to reach a
real run early while keeping the separate lookup rule OPEN.

Parser acceptance alone establishes syntax only. Current code does not yet
establish validation, selected-member materialization, candidate admission or
RuntimeProgram execution. The pure call's result remains a future observable,
not evidence supplied by this proposal.

## One compatibility judgment for every example and proof

All outcomes below are governed by
`notes/design/2026-10-19-r83-role-call-compatibility.md` at the hash above.
It defines independent `SigEligible` and `ImplEligible` predicates; neither
compares arity against the other. After both pass, the three-way classifier is:

| Result | Exact condition | Proposed pilot consequence |
|---|---|---|
| **Compatible** | Counts, supported endpoint evidence, result and §21 role vectors all agree | Continue through ordinary type/effect checks and separate source/admission gates |
| **Incompatible** | Both declarations are eligible but arity, supported endpoint or entry role differs | Reject this implementation before executable member admission |
| **Unsupported** | Either declaration form is outside the pilot, or ordinary endpoint evidence is outside/unavailable | Do not admit it through this provisional pilot; do not claim the language generally rejects it |

An extra or missing binder of an otherwise supported form is Incompatible. A
Boolean endpoint, closed row, or Computation receiver is Unsupported. The
implementation binder's own outer source annotation fixes Value/Computation
entry under charter §21. The signature never rewrites or annotates a binder.
No implicit adapter or permission-as-effect-cap interpretation is introduced.

### Compatible Value call

```yu
role SecondInt { my second: int -> int -> int }
impl int: SecondInt { my second self selected = selected }
my answer = SecondInt::second 1 2
```

Classification is Compatible when ordinary inference establishes the
implementation's endpoint evidence. Both binders are Value under §21; after
ordinary Call and admission succeed, the proposed result is `2`.

### Compatible Computation argument

```yu
act io:
    our observe: int -> int
role RunComp { my run: int -> [_] int -> int }
impl int: RunComp { my run self (action:[_] int) = 0 }
my answer = RunComp::run 1 (io::observe 3)
```

Classification is Compatible when ordinary inference establishes the ground
endpoints. Both signature and executable formal explicitly use Computation
entry. Under §21 the argument carrier is retained; this body ignores it, so
the proposed result is `0` without an `observe(3)` request from `action`.

### Incompatible entry role

```yu
role RunComp { my run: int -> [_] int -> int }
impl int: RunComp { my run self action = 0 }
```

Classification is Incompatible: the signature slot is Computation but the
unannotated executable formal is Value under §21. Reject this implementation
before executable admission. The symmetric pair—a Value signature slot and an
explicit `action:[_] int` binder—is Incompatible too.

### Incompatible supported arity and endpoint

```yu
role OneArg { my run: int -> int -> int }
impl int: OneArg { my run self (first:int) (extra:int) = 0 }
```

Both declarations independently use supported forms; the implementation has
one extra supported binder. Classification is Incompatible. `ImplEligible`
does not compare that count to the signature.

```yu
role UnitArg { my run: int -> () -> int }
impl int: UnitArg { my run self (value:int) = 0 }
```

Both endpoints lie in the pilot set, but they differ. Ordinary evidence yields
Incompatible, with both annotation/signature anchors retained.

### Unsupported form

```yu
role BoolArg { my run: int -> bool -> int }
impl int: BoolArg { my run self (value:bool) = 0 }
```

Classification is Unsupported because `bool` is outside the pilot. It does
not say that full-language inference rejects this program.

## Lookup cases and outcomes

These labels and diagnostic anchors are proposed categories only. They do not
authorize any existing diagnostic or expected-output change.

Missing role:

```yu
my answer = MissingInt::second 1 2
```

Proposed `MissingRole`, anchored at `MissingInt`; do not search a different
role or global value.

Missing member:

```yu
role SecondInt { my second: int -> int -> int }
impl int: SecondInt { my second self selected = selected }
my answer = SecondInt::multiply 1 2
```

Proposed `MissingMember` within `SecondInt`; do not execute a body.

Missing implementation:

```yu
role SecondInt { my second: int -> int -> int }
my answer = SecondInt::second 1 2
```

Proposed `MissingImplementation` for the `int` receiver; this differs from
missing role and missing member.

Duplicate implementation key:

```yu
role SecondInt { my second: int -> int -> int }
impl int: SecondInt { my second self selected = selected }
impl int: SecondInt { my second self selected = self }
my answer = SecondInt::second 1 2
```

Proposed declaration-time duplicate rejection before member admission, with
both source locations retained. Declaration order is not a tie-break.

Same member spelling in two roles:

```yu
role SecondInt { my choose: int -> int -> int }
role FirstInt  { my choose: int -> int -> int }
impl int: SecondInt { my choose self selected = selected }
impl int: FirstInt  { my choose self selected = self }
my a = SecondInt::choose 1 2
my b = FirstInt::choose 1 2
```

Proposed results are `2` and `1`. The explicit role qualifier distinguishes
the member identities. This leaves `1.choose(2)` OPEN.

## Correct outward-request prefix

The governing entry rule is charter §21. Calls construct the whole argument
computation inertly. Value entry forces and rebinds once in that receiving
activation before body execution; Computation entry retains the carrier.
Neither body use nor an empty solved effect row changes the role.

```yu
act io:
    our observe: int -> int
role SecondInt { my second: int -> int -> int }
impl int: SecondInt { my second self selected = selected }
my answer = SecondInt::second (io::observe 1) (io::observe 2)
```

Both arguments are constructed inertly. The receiver is the first ordinary
application stage and `self` is a Value formal. With no matching handler,
`observe(1)` escapes before that entry returns; the suspended suffix retains
the pending receiver entry and later application. The second formal has not
entered, so neither `observe(2)` nor result `2` follows. A later trace requires
a response and exact continuation evidence. No handler-completion trace is
claimed here, and existing unhandled-request expectations remain intact.

## Effect-hygiene range and proof limits

The effect goal remains broad and evidence-led. It covers six frontiers without
pretending to prove all six or reopening storage/fiber inventories:

| Frontier | R83 evidence boundary |
|---|---|
| ordered matching handler | inspected ordinary consumer and exact R78 fixture evidence; complete authentic source selection remains OPEN |
| Value/Computation entry | §21 and ordinary receiver consumers; role-call materialization must preserve source annotations |
| wrong/sibling permission | exact positive permission is the licensing fact; protected sibling source proof remains OPEN |
| shallow unmatched outward request | conditional fixture/runtime evidence; native residual typing remains OPEN |
| continuation | one bounded capture/binder/resumption path; full template and protected-sibling preservation remain OPEN |
| static → native/runtime | conditional source/candidate/runtime path; native operation/formal and K,D/residual owners remain OPEN |

The R81 proof supplies a conditional ordinary-Apply prefix simulation, not
current role-producer facts. P1–P4 (selected identity, executable body/root,
ordinary graph and complete admission) remain OPEN. The previous root-dispatch
inspection boundary was removed; complete literal-to-HIR projection remains
OPEN. No inference, native K,D/residual, continuation or original A/B theorem
closes from these fixtures or the classifier.

## Future source path and exact adoption offer

The first executable slice must establish, in order: source-owned role/impl/
member identities; signature and implementation validation using the shared
three-way rule; materialized member body/root, environment and original
annotations; unique receiver-type selection; ordinary receiver-first Call;
candidate admission of complete validated metadata; RuntimeProgram execution
through existing Apply/receiving consumers. Current code does not yet establish
that chain. A later implementation contract must pin each reached source owner
and exact focused command before running anything.

After fresh independent compiler/source and spec/design review, the user can
adopt or reject this exact package:

1. Use `Role::member receiver args` for the first role-qualified method call,
   with receiver as the first ordinary Call stage; leave dot dispatch and
   field collision OPEN.
2. Adopt the exact `SigEligible`, `ImplEligible` and three-way classifier in
   the cited compatibility definition, including Incompatible arity mismatch
   and Unsupported out-of-envelope forms.
3. Keep executable formal roles fixed by §21 and require exact role agreement;
   do not inherit annotations or insert adapters.
4. Use the listed distinct missing-role/member/implementation and duplicate
   declaration outcomes for the pilot.
5. Preserve the exact unhandled request prefix and the stated effect-hygiene
   limits.

No user approval, source edit, test run or production semantics follows from
this draft. A later explicit adoption and a separate implementation contract
are required before the first demonstration can run.
