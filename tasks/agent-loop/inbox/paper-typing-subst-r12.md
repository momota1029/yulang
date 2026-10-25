# R12 handoff — resume through typed continuation values

Status: `SUCCESS_CHECKED_R12_SLICE`; full paper theorem remains `OPEN`.
Sprint contract `FULL-PAPER-TYPE-SUBSTITUTION-20261025/r12`, SHA-256
`77ebe126a6239aa51daba89a4b997e2f9d7b34a5240952a354788622c5f429fd`.
Baseline `11230acfb`; authority `docs/yulang-operational-type-safety-ja.tex:403-405,458-465,953-977`.
Primary `/root` was the only writer and checker; runtime exposes no UUID
(`UNKNOWN_CURRENT_SESSION_ID`). No child or reviewer was admitted. Eight
historical/foreign reservations stay quarantined. Writes stop after this frozen
handoff and state integration. Independent review remains `NOT_RUN`.

## Result and source correspondence

The paper's handler arm binds `k : Kont(Q,A)` (§types, lines 403-405), and its
resume rule accepts that continuation plus a `Q` response and returns `A`
(lines 458-465). `PaperComputationTyped.resume` now expresses this directly:
its continuation premise is `PaperValueTyped ... K (.kont Q A)`. The canonical
`PaperContinuationTyped` body judgment remains in the value introduction rule
and in request typing. Request's unique declaration and same-instance payload /
response premises were not changed.

`PaperComputationTyped.typeTransport` uses the value IH for the revised resume
premise. The six-family mutual theorem still transports arbitrary
`σ : Nat → Ty`, including both `Kont` indices, the type environment, shared
graph environment, declaration table, values, and computation.

The concrete witness `resumeVariableBoolInt` proves
`resume(variable 0, true) : Int` with `Γ = [Kont(Bool,Int)]`, for any declaration
table. `resumeVariableWrongResponseImpossible` proves the same expression
cannot receive result type `Bool`; the indexed resume rule keeps response and
normal result distinct. Its axiom audit contains only `propext`.

This closes the identified judgment mismatch only for the partial extrinsic
relation. It does not add handler typing, term substitution, owner
alpha-renaming or runtime semantics. Omitted paper forms and all original
inference/executor/A-B, source/native, Rust, and independent-review gates remain
OPEN.

## Checked declarations and verification

The focused pinned build passed for `YulangClosure.PaperExecutionSyntax` and
`YulangClosure.PaperExecutionTypingSubstitution`. The audit's `#check` output
prints the exact revised resume constructor, both Bool/Int witnesses, the
six-family `PaperValueTyped.subst_explicit`, and the five transport projections:
`ValuesTyped.typeTransport`, `ValuesAllTyped.typeTransport`,
`RecordPayloadsTyped.typeTransport`, `PaperContinuationTyped.typeTransport`,
and `PaperComputationTyped.typeTransport`.

All audited transport declarations and `resumeVariableWrongResponseImpossible`
have complete axiom output limited to `[propext, Quot.sound]`, except
`resumeVariableBoolInt`, which has no axioms. No `sorryAx`, `_f`, failed
declaration dependency, or project axiom appeared.

Toolchain: Lean 4.35.0; Lake `5.0.0-src+eb6cafb`; `-j1 -M1024`. R12 spent
3/6 serial Lean/Lake invocations and approximately 11.5 checker seconds of 90:

1. `lake build +YulangClosure.PaperExecutionTypingSubstitution` — syntax
   dependency built (9.1 s); typing module failed at the attempted `variable`
   case label in the negative example (`variable` is a parser keyword).
2. Focused build after replacing named inversion with `cases`/`simp_all` — exit
   0 (about 0.9 s).
3. `lake env lean -j1 -M1024 .lake/R12Audit.lean` — exit 0 (about 0.3 s).

The syntax dependency reports unused binder-name linter warnings in existing
mapping/resolution code. They do not affect the successful build or audited
proof dependencies. `git diff --check` passed. No tests, Rust build, default
build, or production source changes were made.

## Artifact hashes

- `PaperExecutionSyntax.lean`: `0d5da86660c4daa4bd8afb6651957a43ee6dc1d18dab774b107a5ba612844616`
- `PaperExecutionTypingSubstitution.lean`: `1f78031b5dc4ca493f2fbb47ff6a38297552bb22af3139b61d2662b32c3c067e`
- `PaperTypeSubstitution.lean` (read-only): `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`
- `PaperTypeFormation.lean` (read-only): `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`
- `DeclSubst.lean` (read-only): `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`
- R11 handoff: `3101c2c70e7b73da63c026457b9a52f9d9eb2b48b074c745540db64fd33e0db1`
