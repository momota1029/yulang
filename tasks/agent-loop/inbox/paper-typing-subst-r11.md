# R11 handoff — continuation, request, and resume transport

Status: `SUCCESS_CHECKED_R11_SLICE`; full paper theorem remains `OPEN`.
Sprint: `FULL-PAPER-TYPE-SUBSTITUTION-20261025/r11`, contract SHA-256
`7304ca40845df0c3adbd439f4ed3670dfb8593bd51857a616e79adc04083706e`.
Baseline: `46ff3a262`; authority: `docs/yulang-operational-type-safety-ja.tex:345-359,458-465,953-977`.
Role/session: primary `/root`; current runtime exposes no session UUID
(`UNKNOWN_CURRENT_SESSION_ID`). No child was admitted; the eight historical or
foreign reservations remain quarantined. Writes stopped after this handoff and
state integration. Independent review: `NOT_RUN`.

## Result and source map

`PaperTypeSubstitution.Ty` now contains `kont response result`; both `mapVars`
and arbitrary simultaneous `subst` recurse through its two indices. The
identity, renaming compatibility, and composition proofs include this case.
`Formed.kont` requires both response and result types formed, and `formed_mapVars`
and `formed_subst` transport it.

The paper rule at §types (lines 345-359) says a continuation body is typed under
`Q :: Γ` with result `A`, while its type is `Kont(Q,A)`. The represented
`PaperContinuationTyped D Xi Γ K Q A` uses the existing `GraphEnvironment` as
shared `Xi`; the continuation constructor types the body at `Q :: Γ` with result
`A`. Owner binders remain names and do not bind graph/resource identities.

Paper request typing uses a uniquely resolved declaration for the operation
identity and one equality identifying the operation instance with that
declaration instantiated by the provided type arguments. The payload is typed
at that instance's payload type; the continuation has that same instance's
response type and the request returns the continuation's normal result type.
This matches the source distinction between response `Q` and normal result `B`
(§types, lines 354-359). `resume` requires the continuation and response value
at `Q`, and returns `A` (§types, lines 458-465). The six-family mutual recursor
transports these forms under arbitrary `σ : Nat → Ty`, preserving the shared
mapped graph environment. Request transport reuses R10's unique-resolution
preservation and operation-instantiation/substitution commutation.

The new judgments still form a deliberately partial extrinsic relation. Its
represented value/computation forms are variable, graph reference, literal,
tuple, sequence, record, delay, value/computation lambdas, union injections,
intersection, top view/view, continuation, ret, let, force, call, field, lookup,
perform, request, resume, and fail. Variant/nominal values, handler arms and
attempts, graphs, primitives, templates, patterns, other paper constructors,
term substitution, owner alpha-renaming, and runtime transitions remain
omitted. This packet proves no step preservation, inference/executor safety,
source/native correspondence, Rust bridge, or original A/B parent theorem.

## Checked declarations

`YulangClosure.PaperTypes.PaperValueTyped.subst_explicit` is the six-family
mutual transport theorem. Its public projections are:

- `ValuesTyped.typeTransport`
- `ValuesAllTyped.typeTransport`
- `RecordPayloadsTyped.typeTransport`
- `PaperContinuationTyped.typeTransport`
- `PaperComputationTyped.typeTransport`

All preserve arbitrary `σ`, map the declaration table, graph environment,
type environment, and syntax, and substitute result types. The additional
support audited was `subst_id`, `subst_mapVars`, `mapVars_subst`, `subst_comp`,
`formed_mapVars`, `formed_subst`,
`OperationDeclarationResolved.typeTransport`, and
`operation_declaration_instantiation_subst`.

The exact `#check` output in `.lake/R11Audit.lean` confirms that
`PaperComputationTyped.request` has premises for exact declaration resolution,
type-argument arity, instance equality, payload typing at the instantiated
payload type, and continuation typing at the same instance response type; its
conclusion is the continuation's normal result type. `resume` concludes the
continuation's normal result type from a response at the continuation response
type.

## Verification receipt

Pinned toolchain: Lean 4.35.0; resolved Lake reported
`Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)`. Lake config supplies
`-j1 -M1024`. All checker calls were serial. R11 used 7/8 allowed Lean/Lake
invocations and approximately 24 checker seconds (under 120 seconds). The
receipt includes the exact failed attempts:

1. `lake build +YulangClosure.PaperExecutionSyntax` — exit 0; built the new
   type algebra, formation, and syntax dependencies (about 20.7 seconds).
2. Focused typing-module build — failed at the continuation value handler's
   `change`; `mapPaperValue` did not reduce definitionally to the mapped
   continuation body.
3. Focused typing-module build — failed because the continuation wrapper was
   indexed by an arbitrary value rather than the continuation constructor.
   The wrapper was narrowed to `.continuation owners binder body`.
4. An attempted focused build passed `-j1 -M1024` as Lake short options and
   exited with `unknown short option '-j'`; no Lean process ran.
5. Focused typing-module build — after replacing `change` with an explicit
   `simpa [mapPaperValue]` IH, exposed the outer value/type goal still needed
   `simpa [mapPaperValue, subst]`.
6. `lake build +YulangClosure.PaperExecutionTypingSubstitution` — exit 0,
   0.68 seconds.
7. `lake env lean -j1 -M1024 .lake/R11Audit.lean` — exit 0, 0.3 seconds.

Audit output printed all required types. Every audited theorem's complete
`#print axioms` output was exactly `[propext, Quot.sound]`; no `sorryAx`, `_f`,
failed declaration dependency, or project axiom was reported. Syntax emitted
unused-binder linter warnings in pre-existing resolution helper proof patterns;
these do not affect the successful build or proof dependencies. `git diff
--check` passed. No tests, Rust build, or production source changes were made.

## Artifact hashes

Input hashes at sprint issue are recorded in the R11 contract. Final modified
artifact hashes:

- `PaperTypeSubstitution.lean`: `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`
- `PaperTypeFormation.lean`: `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`
- `PaperExecutionSyntax.lean`: `22c2e19811d4c6a21c5b7f58d0b4c86d832031e44d53a786307453d1b8c4fba7`
- `PaperExecutionTypingSubstitution.lean`: `6893510f5b419f1d9c47bbfd26f73dbf95ccefb688ca8e74253029d2b033bbf4`
- `DeclSubst.lean` (read-only): `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`

R9/R10 independent reviews remain `NOT_RUN`. This checked partial slice does
not close the full paper typing theorem or any source/native or compiler parent.
