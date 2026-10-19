# R81 role-qualified call and effect hygiene: adoption draft

Date: 2026-10-19  
Status: Draft; all new syntax, validation and diagnostic choices below remain unadopted  
Sprint: `effect-hygiene-role-call-20261019-r81`, revision 1  
Contract SHA-256: `57989ca9d6f7b54d2bffa37fb5399f9d0bcaf16ea5193109d7bb7c7547914c16`  
Baseline: `af3ccf2d63ba7f87e0359e183568db548ea53307`  
Reviewed-by: pending fresh compiler/source and spec/design review  
Approved-by: none

## First runnable surface

```yu
role SecondInt {
    my second: int -> int -> int
}
impl int: SecondInt {
    my second self selected = selected
}
my answer = SecondInt::second 1 2
```

The proposed result is `2`. The role qualifier selects a member declaration;
the receiver type selects one validated implementation. The selected executable
callee must retain source-owned `(ImplId, MemberId)`, its body root, lexical
environment and original binder annotations, then enter the existing curried
Call/Apply path with receiver first. There is no special method evaluator.
General `1.second(2)` and field/method precedence remain OPEN.

The path is not runnable in the current producer/admission chain. Existing
`Role::member` syntax, if accepted by parsing, gives syntax evidence only.
Validation, body materialization, selected identity, CandidateInference
admission, RuntimeProgram representation and execution require a later
implementation contract. This draft authorizes none of them.

## Bounded role/binder compatibility proposal

Charter §21 fixes an executable formal's role from its own outer source
annotation: an unannotated or ordinary `x:A` formal is `Value(A)`; an explicit
`x:[E] A` or `x:[_] A` formal is `Computation(E,A)`. A role signature cannot
rewrite that role. For this first pilot, propose the following validation
judgment over a single member, in source order:

| Slot | Role-signature requirement | Implementation-formal requirement | Draft outcome |
|---|---|---|---|
| receiver | first input is ground `int`, entered as Value | first formal has ground `int` and is Value under §21 | accept |
| ordinary parameter | ground `int` or `()` and Value | same ground type and Value under §21 | accept |
| retained parameter | explicit `[_] int` and Computation | same ground type and explicit `[_]` outer annotation, hence Computation under §21 | accept |
| role mismatch | signature slot says Value but body formal is Computation, or converse | executable role remains the body's §21 role | reject the declaration before member admission |
| other shape | polymorphic, unresolved, unsupported effect expression, arity mismatch, or type mismatch | no implicit coercion or inferred adapter | keep outside this pilot; do not report it as a general language error |

The proposed judgment checks exact arity, slot roles and the listed ground
types; it does not compare permissions with closed effect caps. `[_]` retains
its existing symbolic source meaning. Duplicate `(receiver type, role)` impl
keys are proposed declaration errors retaining both locations. Every outcome
in this table is a new Draft choice, not an existing compiler fact. The user
must adopt or replace it before implementation.

### Compatibility cases

Computation formal with matching signature:

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

Draft outcome: the declaration satisfies the bounded signature/binder rule;
`self` is Value and `action` is Computation because of the executable binder's
own annotation. The body ignores the retained action, so it does not request
`observe(3)` and returns `0`.

Role mismatch:

```yu
role RunComp {
    my run: int -> [_] int -> int
}
impl int: RunComp {
    my run self action = 0
}
```

Draft outcome: reject this declaration before executable admission. The
unannotated `action` is Value under §21; the signature does not supply an
annotation or adapter. A corresponding Value signature with an explicitly
Computation implementation formal fails symmetrically. No implicit adapter is
selected.

## Lookup and diagnostic cases

All outcomes are proposals, not adopted diagnostics.

Missing role:

```yu
my answer = MissingInt::second 1 2
```

Proposed outcome: unresolved `MissingInt` at the qualifier; do not search
another role or a global `second`.

Missing member:

```yu
role SecondInt { my second: int -> int -> int }
impl int: SecondInt { my second self selected = selected }
my answer = SecondInt::multiply 1 2
```

Proposed outcome: unresolved `multiply` within `SecondInt`; do not execute a
body.

Missing implementation:

```yu
role SecondInt { my second: int -> int -> int }
my answer = SecondInt::second 1 2
```

Proposed outcome: member exists but no implementation matches the `int`
receiver; report the member and receiver source anchors.

Duplicate implementation:

```yu
role SecondInt { my second: int -> int -> int }
impl int: SecondInt { my second self selected = selected }
impl int: SecondInt { my second self selected = self }
my answer = SecondInt::second 1 2
```

The proposal rejects the duplicate declaration key before any use is
published.

Same member spelling in two roles:

```yu
role SecondInt { my choose: int -> int -> int }
role FirstInt  { my choose: int -> int -> int }
impl int: SecondInt { my choose self selected = selected }
impl int: FirstInt  { my choose self selected = self }
my second_answer = SecondInt::choose 1 2
my first_answer = FirstInt::choose 1 2
```

Proposed outputs are `2` and `1`. This does not settle `1.choose(2)`.

Same-name callable field and role member:

```yu
struct Box { second: int -> int }
role BoxRole { my second: Box -> int -> int }
impl Box: BoxRole { my second self selected = selected }
my apply_field box: Box = box.second(2)
my apply_method box: Box = BoxRole::second box 2
```

This is a concrete competing declaration pair and use site. The proposed
surface keeps `BoxRole::second box 2` as the explicit method route and leaves
`box.second(2)` as field projection followed by ordinary Call in this pilot;
no dot method desugaring or field/method precedence is claimed. If the desired
future syntax makes the dot form dispatch to the role member, that needs an
explicit selection rule and the exact same-source collision remains OPEN until
adopted. These are Draft examples; this document does not claim parser or
runtime support.

## §21 effects and exact outward prefix

The controlling rule is charter §21. Every call constructs its whole argument
computation inertly. Value entry forces and rebinds the argument once inside
that formal's receiving activation before its body, even if unused.
Computation entry retains the carrier for explicit body consumption. Entry is
fixed by the executable formal's outer annotation, not by body use, solved row
emptiness or a role signature. No entry force recursively demands a latent
result.

The pure `SecondInt::second 1 2` case may complete with `2`. For effectful
arguments:

```yu
act io:
    our observe: int -> int
role SecondInt { my second: int -> int -> int }
impl int: SecondInt { my second self selected = selected }
my answer = SecondInt::second (io::observe 1) (io::observe 2)
```

Both argument expressions are constructed inertly. The receiver is the first
ordinary application stage and has Value entry. If `io::observe 1` is
unhandled, that first request propagates outward with the remaining receiver
activation and later curried application suspended. Execution has not reached
the second formal's entry; it therefore has not issued `observe(2)` and has not
produced `answer == 2`. If a future supported handler resumes the first request,
the resumed suffix must be derived from the pinned ordinary consumers before
claiming any later trace. This corrects R80's counterexample without changing
existing expected output.

`Observe(1)`, `Observe(2)`, then `2` is not promised here. A complete explicit
handler version may be added only if its source and exact resumption outcome
are pinned and proved. Method lookup and selection must not execute either
operand.

## Effect-hygiene evidence range

The goal is broad evidence with explicit depth boundaries, not six claimed
proofs. R78's reviewed runtime work supplies conditional evidence only for its
exact fixtures; R80 supplies a conditional occurrence-indexed simulation only
under `Hsel`, `Hroot`, `Hann`, `Hgraph`, and `Hadmit`. Those hypotheses are not
current producer facts. R80 does not establish actual role source projection,
native operation/residual typing, or universal hygiene.

| Frontier | R81 bounded claim | Evidence status and remaining owner |
|---|---|---|
| ordered matching handler | ordinary consumer chooses the first eligible matching arm in its ordered set | consumer-level evidence; source-generated selection membership remains conditional on complete `LocalSource` projection |
| Value/Computation entry | §21 roles force/rebind or retain at the ordinary receiving boundary | consumer behavior inspectable; role-call producer annotations/compatibility remain to be bound |
| wrong or sibling permission | exact positive permission licenses the request; absence alone does not claim protection | R78 fixture-conditional; protected-sibling source construction remains OPEN |
| shallow unmatched request | unmatched request exits the handler with its suffix outward | R78 fixture-conditional; native residual path remains OPEN |
| continuation | one capture/binder/resumption path transports the same concrete continuation and suffix | one bounded path only; continuation-template owner and protected-sibling proof remain OPEN if unpinned |
| static → native/runtime | one operation path links source, candidate evidence and actual execution | R78/R80 conditional; native operation/formal and K,D/residual consumer owners remain OPEN if unpinned |

The map states current evidence and falsifiers; it is not a hygiene theorem.
Do not inventory storage/fiber representations. For every uninspected owner,
record its exact symbol and leave it OPEN until a separately pinned authority
permits inspection.

## Proposed source-to-runtime path

1. Retain parser source occurrences for role, impl, member and the qualified
   call; parsing alone supplies no lookup semantics.
2. Give role, impl and member declarations stable source-owned identities.
3. Validate the bounded signature/binder judgment before publishing any
   executable member root; retain lexical environment and binder annotations.
4. Resolve the role/member qualifier and receiver type to exactly one validated
   `(ImplId, MemberId)`; preserve exact origin on each generated Call/Apply
   stage, with receiver first.
5. Extend candidate preflight/admission for complete validated declarations
   and member roots. A registered effect-declaration placeholder is not
   sufficient to admit a role or executable member.
6. Retain validated metadata and selected identity in RuntimeProgram, then
   execute through ordinary Apply, receiving and handler consumers.

This path names future owner seams; it claims none are implemented. The first
post-adoption verification should run one focused source fixture yielding `2`
through the package's existing CLI/test entrypoint after a successor Stage 2
contract pins exact owners and commands. Stage 1 runs no checks.

The current pinned package is `yu-playground`; the proposed future smoke route
is `cargo run -p yu-playground -- --run answer <fixture.yu>`. A focused test
name and fixture path must be selected and pinned in Stage 2 when the actual
test owner is leased. This command is planning evidence only and is not
authorized or run here.

## Adoption questions

1. Adopt `Role::member receiver args` as the first role-qualified method form,
   with receiver as the first ordinary Call stage, while leaving general dot
   lookup open?
2. Adopt the bounded role/binder compatibility judgment and its declaration
   rejection boundary, or choose a different exact rule before implementation?
3. Adopt duplicate implementation-key rejection and the proposed distinct
   missing-role/member/implementation anchors?
4. Accept the §21 outward-prefix outcome: an unanswered receiver request stops
   before later argument entry and final result?

Independent reviews test this package and its proof, but do not make these
language choices. No syntax meaning, runtime behavior, code or production gate
is adopted by this draft.
