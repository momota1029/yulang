# R279 — evidence for declaration-local Yulang2 `where` syntax

Status: checkpointed implementation evidence; provisional and unreviewed.

## Parent application

R149 requires unchanged Types/Console examples and authentic source-backed role
prerequisites. R278 removed dotted Pattern targets from the exact pinned fmt
source's parser recovery, reducing 50 diagnostics to 36. A fresh invocation of
the rebuilt playground identified the complete partition as:

| Kind | Structural owner | Count |
| --- | --- | ---: |
| `ErrorGroup` | `Root` | 21 |
| `ErrorGroup` | `OperatorChain` | 7 |
| `Missing` | `CaseArm` | 7 |
| `Missing` | `StringEscape` | 1 |

The previous R278 note/test summary omitted the last category from its subtotal;
R279 corrects the record and pins all four groups in the test.

## Pinned source requirements

The exact pinned 40-module bundle contains 47 source lines beginning with
`where`. In fmt, constraints precede the body of generic function definitions
and `impl` bodies. Subjects include `'a`, `'b`, `'ok`, `'err`; role types include
`Display`, `Debug`, `LowerHex`, `UpperHex`, and an applied `Fold 'item`. R149's
Types sample depends on the tuple `Display` prerequisites being retained and
later discharged independently. Console `say` similarly depends on `Display`.

These counts are source census evidence, not a semantic proof. The implemented
`WhereClause` prefix parser preserves exact occurrences and declaration
ownership before ordinary body parsing. On the exact pinned fmt source, the
census is now 32: 1 root `ErrorGroup`, 15 `OperatorChain` `ErrorGroup`s, 15
missing `CaseArm`s, and 1 missing `StringEscape`. The root count fell from 21
to 1; continuing through the formerly swallowed case bodies exposed nested
diagnostics, so the total fell by four. Focused tests cover applied role
constraints, ordered repeated prerequisites, malformed frontiers, and the
nested-block boundary. HIR/solver transport, remaining expression syntax, R149
role selection, and source/native obligations stay OPEN.

## Current step and falsifier

R279 adds a declaration-owned CST prefix for valid binding and implementation
bodies and keeps ordinary statement parsing after it. Tests show source-order
preservation, exact target `fmt` syntax positions and bounded recovery. A test
pass does not establish HIR transport, prerequisite solving, principal public
types or output.
