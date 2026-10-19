# R84 role-qualified call and effect-hygiene adoption offer

Date: 2026-10-19  
Status: Draft; proposed semantics remain unadopted  
Sprint: `effect-hygiene-runnable-role-slice-20261019-r84`, revision 1  
Contract SHA-256:
`fd6de85efe1926696f3a45894aa1e3a8a612b31d257bb71b339cc7c79d7c2f48`  
Normative judgment: `notes/design/2026-10-19-r84-role-call-judgment.md`  
Normative judgment SHA-256:
`f3c604dd7a131bbba606d38ff5b19f37c01ef1b26386a5f90ae39e8de60478c1`  
Approved by: none

## 1. Proposed first executable surface

```yu
role SecondInt {
    my second: int -> int -> int
}
impl int: SecondInt {
    my second self selected = selected
}
my answer = SecondInt::second 1 2
```

The proposed result is `2`. `SecondInt::second` identifies a member under an
explicit role qualifier. The `int` receiver selects the implementation. The
implementation must lower this to ordinary receiver-first curried Call/Apply,
then execute through the existing candidate and runtime path. The full
source-to-runtime owner map and its open producers are in the R84 readiness
artifact; it is planning evidence, not current support.

This chooses `Role::member receiver args` as the first method surface. It leaves
`receiver.member(args)`, dot lookup, field/method precedence and callable-field
collisions OPEN. Those rules are not needed for this first call.

## 2. Proposed shared declaration judgment

All declaration outcomes use the normative procedure in the judgment artifact
at the hash above. In short, `SigEligible` and `ImplEligible` inspect each
declaration independently; neither compares arity. After those checks, the
procedure examines every receiver/formal endpoint on both complete
declarations, including unmatched extra binders. Any outside or unknown
endpoint yields `Unsupported` before arity, type or role mismatches are
compared.

| Declaration pair | Proposed outcome | Reason |
|---|---|---|
| `int -> int -> int`; `self, selected:int` | Compatible | all-supported vectors agree |
| `int -> int -> int`; `self, selected:int, extra:int` | Incompatible | supported arity mismatch |
| `int -> int -> int`; `self, selected:int, extra:bool` | Unsupported | outside endpoint dominates arity mismatch |
| `int -> int -> int`; `self, selected:()` | Incompatible | both endpoint types are supported; they differ |
| `int -> [_] int -> int`; `self, action:[_] int` | Compatible | explicit Computation role and endpoint agree |
| Computation signature; unannotated or ordinary-value `action` | Incompatible | §21 makes the executable formal Value |
| Value signature; `action:[_] int` | Incompatible | §21 makes the executable formal Computation |
| Computation signature; `action:[_] bool` | Unsupported | outside endpoint dominates role mismatch |
| either complete endpoint inventory has unknown type | Unsupported | evidence is insufficient for this pilot |
| signature has bool receiver/result or closed-row slot | Unsupported | signature is outside the pilot |

`Unsupported` means “not covered by this pilot,” not “invalid in Yulang.”
`Incompatible` applies only after all inventoried endpoints are known and
inside the pilot. `Compatible` permits ordinary body/result/effect checks; it
does not establish those checks or materialize an executable method.

## 3. Proposed binder and request behavior

The outer source annotation of each executable formal controls its entry under
charter §21: an unannotated/ordinary value formal is Value, and an explicit
`[_]` formal is Computation. A signature does not annotate or rewrite that
formal. This proposal adds no implicit adapters.

```yu
act io:
    our observe: int -> int
role SecondInt { my second: int -> int -> int }
impl int: SecondInt { my second self selected = selected }
my answer = SecondInt::second (io::observe 1) (io::observe 2)
```

Both argument computations are initially inert. The first receiver application
uses a Value formal, so `observe(1)` is forced before entry returns. With no
matching handler, that request escapes with the later application suspended.
`observe(2)` and result `2` do not follow. A handler/resumption trace needs a
separately evidenced context; this offer does not invent one or alter existing
unhandled-request expectations.

## 4. Proposed lookup outcomes

These are pilot behavior proposals, not authority to alter current diagnostics
or expected outputs:

- unknown qualifier `MissingRole::second` → `MissingRole` at the qualifier;
- known role with absent `multiply` → `MissingMember` within that role;
- known member with no implementation for the `int` receiver →
  `MissingImplementation` for that receiver;
- repeated `(int, SecondInt)` implementation key → declaration-time duplicate
  error retaining both source locations;
- `SecondInt::choose` and `FirstInt::choose` select distinct role members.

The implementation contract must establish authentic source identities and
anchors before any such result is treated as existing behavior.

## 5. Effect-hygiene range and evidence limits

This work covers effect hygiene across six known fronts without claiming six
new proofs or returning to indefinite storage/fiber inventory:

| Frontier | Current evidence boundary | Next falsifier or owner obligation |
|---|---|---|
| ordered handler match/priority | ordinary consumer and bounded R78 fixture evidence; authentic source selection remains open | source witness with overlapping handlers and the selected exact clause |
| §21 Value/Computation entry | ordinary receiver consumers inspected; role-call preservation is conditional on source binders | end-to-end check that the retained executable binder annotation reaches the receiver entry consumer |
| wrong/sibling permission | the exact positive permission is the license; sibling non-protection remains open | source/native pair where one permission excludes the operation and a sibling preserves the request |
| shallow unmatched outward request | R81 conditional prefix proof preserves `observe(1)` and its suspended suffix under P1–P4 | bind P1–P4 to authentic selected-member producers without changing the prefix |
| continuation capture/resumption | one binder/resumption route is evidenced; complete template and protected-sibling preservation remain open | trace the exact captured continuation through one response and one unrelated sibling request |
| static-to-native/runtime | source action and ordinary runtime consumers are known; selected-member admission and native residual correspondence remain open | build one selected-member path through generation, admission and runtime, then compare its residual |

The readiness artifact pins the source-path lane's owner map and records which
rows it can substantiate. These are separate obligations; a role-call proof or
successful runner does not establish general effect hygiene, permission
preservation, continuation safety or native correspondence. Parent/A-B remain
OPEN 0→0, and R50 remains NOT_ADOPTED.

## 6. Exact adoption decision

After fresh independent compiler and specification review, the user can adopt
or reject this package as a unit:

1. Use `Role::member receiver args` for the first role-qualified method call,
   with receiver as the first ordinary Call stage; leave dot lookup and field
   collision OPEN.
2. Adopt the exact supported pilot envelope and ordered classifier in the
   cited judgment, including `Unsupported` for any outside/unknown endpoint
   before mismatch checks.
3. Keep executable formal roles fixed by §21; require exact role agreement and
   insert no implicit adapters or signature-derived annotations.
4. Use the distinct role/member/implementation lookup outcomes and
   duplicate-key rule as proposed for this pilot.
5. Preserve the exact unanswered Value request prefix and keep the six effect
   frontiers as open, evidence-led obligations with their stated falsifiers.
6. If adopted, make the next sprint the vertical runnable implementation of
   the listed source form, with exact source owners and future verification
   commands pinned before execution.

This draft does not authorize code, tests, diagnostics, fixtures,
expected-output changes, production semantics or closure of the parent proof.
