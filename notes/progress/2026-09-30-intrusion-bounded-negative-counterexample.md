# Intrusion bounded-negative erasure counterexample

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Classification: conditional denotational counterexample; no Yulang semantics selected

## Claim

Under a subtype preorder with `Top ≰ Int` and Function subtyping

```text
Arr(A, R) ≤ Arr(A', R') iff A' ≤ A and R ≤ R'
```

a negative-only local argument `x` constrained by `x ≤ Int` cannot in general
be replaced by `Top` while preserving the candidate principal relation. The
constrained relation is `↑{Arr(A,R) | A≤Int}`. `Arr(Top,R)` belongs to
`↑{Arr(Top,R)}` by reflexivity. It cannot belong to the constrained relation:
membership would require some `A≤Int` with `Arr(A,R)≤Arr(Top,R)`, hence
`Top≤A≤Int`, contradicting `Top ≰ Int`.

This counterexample shows that the unconstrained negative-argument lemma cannot
be generalized by polarity alone. It is not an Oracle observation and does not
establish that the Oracle accepts or emits this exact selected graph.

## Frozen Oracle characterization

A temporary Rust source-path test against frozen Oracle `a58eefc3` used:

```text
my expect(x: int): int = 1
pub k x = expect x
```

The lowering completed without diagnostics. In `k`'s first compact view, the
Function argument includes `Int` and `TypeVar(16)`; that variable has an upper
bound record. At the saved `GeneralizedCompactRoot`, the argument contains
`Int` and no variable, and the public scheme is `int -> int`. This is
consistent with the frozen Oracle compactor expanding negative variables
through upper bounds before one-polarity elimination, but this source graph is
not proven identical to the abstract counterexample above.

Probe command:

```text
cargo test -p infer scratch_oracle_saved_bounded_negative_projection -- --nocapture
```

One focused test passed, including an assertion that lowering produced no
diagnostics. Its temporary instrumentation and test lived only in
`/tmp/yulang-intrusion-bounded-arg-probe` and were removed after capture. The
frozen Oracle worktree was not modified. The proof must still compare the
candidate's selected-obligation relation with this ordered Oracle projection;
deleting a bounded variable directly is not a valid shortcut.

Independent `compiler_referee` review verified the counterexample under the
stated preorder and Function rule. Independent `spec_auditor` review confirmed
that its scope is conditional and it makes no Oracle-semantic decision. Neither
review establishes the source graph or the general root-projection theorem.

## Restricted correspondence result

A conditional path theorem is now recorded in the abstract semantics draft.
It covers a pure acyclic structural root `Arr(x, R)` with one negative
occurrence of `x`, a successful projection query whose sole effective input is
one direct concrete upper atom `U`, eligible one-polarity elimination, and
later passes that leave `U` and `R` unchanged. If the candidate separately
stipulates `{A | A ≤ U}` as the nonempty admissible assignment set with greatest
element `U`, both paths produce the same root denotation, `↑{Arr(U,R)}`.

This statement was reviewed conditionally by a `compiler_referee` and
`spec_auditor`. A subsequent semantic review confirmed the interval lemma below
and required further precision for the Oracle-path premise. The draft now
requires a successful per-root projection/restart, a non-bipolar occurrence
census with no other relevant occurrence, the actual level/non-generic
elimination checks, and evidence that the complete retained argument after
merging the self variable and projection input denotes exactly `U`; all later
passes must preserve that argument and `R`. The exact assignment fiber
`{A | A ≤ U}` remains a separate denotational premise. The `expect`/`k` probe
is only an observed `U = Int` path consistent with these conditions. The
structural root `Arr(x,R)` is not claimed to be the complete compact graph:
Oracle's `compact_var_side` merges the source-variable occurrence with its
projected bound before elimination. This is one restricted interpreted-root
correspondence, not diagnostics, later-member state, incoming-use simulation,
Gate C closure, or Oracle equivalence for the source graph family.

The draft now also records a reviewed interval extension of the pointwise
extremal lemma. In a fixed fiber where the admissible assignments are exactly
the nonempty interval cut out by finite lower and upper bounds, the meet of the
uppers is the greatest admissible assignment; compatible lower bounds do not
change the projected root. This still assumes the exact selected fiber and
does not derive it from Oracle evidence or cover shared-variable dependencies.

The selected-edge corollary now derives that exact fiber for a restricted
already-selected graph: after fixing anchors and every other local vertex, all
edges mentioning `x` must be fixed-endpoint inequalities into or out of `x`,
and every other obligation must be independent of `x`. Its nonempty fiber then
has the upper-endpoint meet as maximum, so a negative-only `Arr(x,R)` projects
fiberwise to that meet. A compiler referee found no blocking/major issue and
requested two premise clarifications, now applied: omitted obligations must be
syntactically x-free, and finite meets include the empty meet `Top`. The result
does not establish Oracle evidence selection or global principal-view
representability.

The Oracle's collector/finalizer path for the conditional sole-`U` case is now
audited against frozen `a58eefc3` Rust source and independently reviewed by a
`compiler_referee`. In negative SchemeProjection, the scoped view exposes its
generalized upper records; the collector folds them with negative merge,
compacts a direct concrete constructor, then merges the original `x`
occurrence. The one-polarity pass removes `x` only when the boundary,
non-generic, and root/recursive-bound/role polarity checks allow it. Negative
Function argument finalization preserves the singleton concrete `U`. The
review found no issue in this derivation for the stipulated sole-`U` fragment.
This explains the Oracle side of that conditional path; it still assumes the
query view contains exactly the stipulated record and later passes retain the
result. The source program's creation of that view and saved-root stability
remain the general bridge to prove.

The concrete `expect`/`k` source construction is now traced through the frozen
Oracle Rust lowering and constraint path. The annotated `int` parameter goes
through `connect_parameter_computation_detailed` to `connect_value_detailed`,
which inserts both `Int <: expect_param` and `expect_param <: Int`. Application
lowering inserts `expect_value <: Arr(k_arg, result)`, and Function
decomposition derives the contravariant argument obligation
`expect_param_inst <: k_arg`. Instantiation clones the finalized scheme and
routes its predicate through the direct-lower or subtype insertion path. Given
the finalized scheme's annotated argument relation, these constraints derive
`k_arg <: Int`. A compiler-referee review accepted this as a conditional
source derivation and emphasized that the scheme premise must be backed by the
actual probe. Together with that probe, this closes the source-construction
bridge for this one `U = Int` fixture. It does not establish the selected
scoped query record solely from source code, prove the result for a family of
schemes, or show that restarts and post-loop passes preserve the result in
other fixtures.

Source locators in frozen Oracle `a58eefc3`: `lowering/expr/lambda.rs:674,
1244-1280`; `annotation/constraints.rs:124-136,251-281,771-793`;
`lowering/expr/tail.rs:94-124,535-566,630-646`;
`constraints/machine/propagate.rs:213-244`; and
`analysis/session/instantiate.rs:385-519`.

Source locators in the frozen checkout: `compact/collect/mod.rs:166-183,
746-782,816-846,952-976,1132-1155`,
`constraints/structural_kernel/access/legacy_read_view.rs:225-235`,
`compact/analysis/mod.rs:41-58,506-513`,
`compact/analysis/occurrence/substitution.rs:109-130`,
`compact/finalize.rs:136-176,415-425,802-825`, and
`compact/collect/type_nodes.rs:104-119,175-190`.

An attempted scratch Rust source-path probe for a nested captured polymorphic
function application, `pub outer(f: 'a -> 'b) = my inner x = f x; inner`, did
not complete. In an isolated detached worktree at frozen Oracle `a58eefc3`,
`cargo test -p infer scratch_intrusion_anchor_argument_application --
--nocapture` remained inside `prepare_cold` for over 90 seconds at nearly one
CPU core and was interrupted; a second run with `timeout 20s` also timed out
before leaving `prepare_cold`. No diagnostic or type result was observed. The
temporary test and worktree were removed, and no frozen Oracle files changed.
This is not evidence about the source program's type or language acceptance;
do not use it as a fixture or repeat it without a bounded execution plan.

## Next action

Extend the source-to-view proof beyond this single `expect`/`k` instance, with
particular attention to how a successful per-root query selects upper records
and how restart/post-loop transitions preserve the saved projection. Then
extend the graph class to anchored or shared endpoints. The general denotation,
ordered root simulation, use simulation, and implementation gates remain
open.
