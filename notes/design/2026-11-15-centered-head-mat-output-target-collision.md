# Output targets lose their clause identity

Status: Draft proof record. Date: 2026-11-15. Scope: astra2-centered-28,
the unchanged total-materialization successor boundary and its V6 Local.

## Result and stop condition

`GeneralNominalCenteredHeadMatCompletionCollision.stable_selected_counterexample`
constructs a checked, constructor-covered, ground-point Initial state of
`GeneralNominalCenteredHeadMatStepBoundary.boundary roles`. Its zero-step
trace establishes actual reachability. The state is stable for the real
successor Step and has V6 Local selected with two children, but neither child
is generated and no installation is enabled.

The pre-state is inhabited, the positive chosen-head baseline holds, chosen
class effects have a model, and choice compatibility holds. Materialization
is complete (`unknown = false`). The obstruction is the allocation of two
incompatible output equations to the same target.

This meets the requested stable-counterexample stop condition. The three
completion premises cannot all be discharged for this boundary:

- `GeneralNominalCenteredHeadMatCompletionCollisionPackets.not_packetAssembly`
  refutes `GeneralNominalCenteredHeadMatCompletionAssembly.PacketAssembly roles`.
- `GeneralNominalCenteredHeadMatCompletionCollision.not_selectedCompletion`
  refutes the frozen `GeneralNominalCenteredHeadMatStepCompletion.SelectedCompletion roles`.
- `GeneralNominalCenteredHeadMatCompletionCollision.not_generatedSelectedChildren`
  refutes the frozen V6-selection-aware `GeneratedSelectedChildren roles`.
- `GeneralNominalCenteredHeadMatCompletionCollision.not_prior_generatedChildren`
  also refutes `B4SkeletonV5.GeneratedChildren (B4TargetV6.prior G)` for this G.

These are closed negative theorems, with no new hypothesis. They refute the
requested production bridges for the current representation; they do not by
themselves refute `B4TargetV6.Statement` or Yulang's intended semantics.
General `HeadBaseline` and `ChoiceFromCommon` remain open, although both
relevant conclusions hold for this particular fixture. Full V6 composition
is therefore not assembled. The preceding twelve laws remain untouched.
Exhaustive multi-tag/open-tail K2 projection work stops here as requested.

## The source contract and the allocation mismatch

The source has a unary parent role P and two distinct zero-argument output
roles R and S, each declaring `out`. Its schematic Yulang shape is:

```yulang
impl P int:
    where R(out = int), S(out = :tick int)
```

The Lean fixture uses declaration ID 37, clause IDs 42 and 44, and output
equation ID 43 in each clause. The first equation is `out = int`; the second
is `out = :tick int` (tag 0). These numbers are internal source identity data,
not Yulang syntax. The registry contains the parent declaration. No child
implementation or resolved-child premise is needed to generate its demands.
R and S are distinct roles, so their output requests must not be equated by
same-input demand merging.

`GeneralDeclarations.Declaration.Identified` checks:

- uniqueness of clause IDs;
- uniqueness of the parent's associated equation IDs and names;
- uniqueness of output-binder names;
- uniqueness of output equation IDs **inside each clause**.

It does not require output equation IDs to be unique across different
clauses. The fixture satisfies the entire `DeclarationChecked` judgment,
including scope, constructor coverage, strict Paterson descent and universal
capture stability. It also satisfies `InitialSource`, point roots, ground
labels, and the successor's actual Coverage requirement. No omitted
well-formedness assumption has been supplied by a caller.

In contrast, `GeneralNominalAllocation.declarationKeys` and
`GeneralNominalAllocation.allocation.outputs` allocate a child output by

```text
source(seed, (invocation, declaration, 5, equation.id, 0))
```

Both omit the clause ID. `same_target` proves equality of the targets for the
two distinct clauses. `schema_exact` computes the actual total-materialized
schema as

```text
t = int
t = :tick int
```

`int_not_variant` proves these meanings are not equivalent in the general
carrier. Consequently `no_packet_model` rules out every model of the actual
packet, despite `effect_model` exhibiting a model of the current journal and
the chosen class effects. The latter see the parent's class output requests,
which are empty; prospective child equations live in the emitted packet.
This is the exact missing implication in PacketAssembly.

The governing spec §6.3 says 「関連型は、新しい型変数と等式で表す」 and
「同じ入力の需要はまとめる」; its merge condition explicitly requires
「同じ role の需要が二つあり」. Accidental equality between outputs of
R and S does not implement that rule. The later head-only/output decisions
in user turns 15 and 22 are also preserved by the fixture: candidate matching
uses only the parent int head, and no refresh or unsettled-output cache is used.

This is an **implementation/source-contract gap**, not a language-semantics
question. If elaboration assigns globally distinct equation IDs, that property
is not part of the present checked/source boundary, so the theorem's current
quantifiers still include the fixture. No compiler-to-source producer is
claimed by this counterexample.

## Stability and non-vacuity

`frame_plan` shows that every current Frame for the selected root is exactly
the fixture plan. Thus `no_install` excludes every root installation, not only
one arbitrarily chosen effect.

The initial journal has no edges, packets or aliases, and its only registered
site is the root. `generated_only_root` excludes every other focus. All listed
source heads are known, so neither refresh constructor can run. The source is
point-closed, ruling out improving reobservation. The point-root initial
journal has exactly the raw source models, so equality feedback cannot add a
new raw equality. Enqueue finds the registered root; a merge would join that
site with itself, whose alias already exists. `stable` checks all of these
constructors, and `halted` excludes every successor Step.

The witness is therefore not a snapshot awaiting an administrative action.
`children_length` proves that selection emits two children; `child_ne_root`
uses their distinct non-parent roles, and `child_not_generated` excludes both.
The positive source and effect models prevent a vacuous inconsistency argument.

## Minimal repair boundary

One representation repair is to retain both clause and equation identity in
purpose-5 allocation, using the available pair of owner/position fields:

```text
source(seed, (invocation, declaration, 5, clause.id, equation.id))
```

Both reservation keys and `allocation.outputs` must change together, followed
by all child output producers/consumers and their identity lemmas. Purpose-2
shared output-binder identities need not change: intentional use of the same
binder is a different case. The alternative is an additive source/checked
contract requiring globally unique child output equation IDs within each
declaration, backed by its elaboration producer. That would restrict the
present theorem domain and requires an explicit integration choice.

No repair or stronger predicate is installed in this turn. Step, Local,
Initial, refresh, V5 and V6 definitions remain unchanged. The collision alone
does not justify inventing another pending or rejection rule.

## Exact evidence interface for dot

The existing stronger reusable node obligation for the successor is

```lean
B4SkeletonV5.EvidenceNode
  (B4TargetV6.prior (GeneralNominalCenteredHeadMatStepBoundary.boundary roles))
```

Writing `G := GeneralNominalCenteredHeadMatStepBoundary.boundary roles`, its
exact expanded type is:

```lean
∀ registry, G.Checked registry →
  ∀ state root, B4TargetV6.Reachable G registry root state →
  ∀ model, G.Models state model →
  ∀ demand key children dictionaries,
    (demand = root ∨ G.Generated registry state root demand) →
    G.Stable registry state demand →
    (∀ child, child ∈ children → G.Stable registry state child) →
    B4TargetV6.SafeKnown G registry state demand →
    B4TargetV6.Unique G registry state demand key children →
    CommonRoleOutermostResolver.All₂
      (fun child dictionary => G.Evidence registry state model child dictionary)
      children dictionaries →
    G.Evidence registry state model demand
      (CommonRoleOutermostResolver.Dictionary.node key dictionaries)
```

This prior-field type has no OutputConflict premise; it is sufficient for a
V6-specific composition which additionally knows the selected node has no
conflict. There is no existing `B4SkeletonV6` record in this checkout. No
EvidenceNode derivation or replacement definition is added here.

## Validation

The `yulang-proofs` skill was used. This checkout supplies no configured or
callable prover role; the primary constructed the bounded counterexample,
with separate read-only source audit and independent proof review. Exact
commands and final results follow. The independent proof reviewer checked
all four modules and found no defect, including the full Stable argument
and the unchanged source domain.

All commands below ran from `lean/`; each exited **0**:

```sh
lake build --wfail Yulang.GeneralNominalCenteredHeadMatCompletionCollisionSource Yulang.GeneralNominalCenteredHeadMatCompletionCollisionLocal Yulang.GeneralNominalCenteredHeadMatCompletionCollisionPackets Yulang.GeneralNominalCenteredHeadMatCompletionCollision
lake build --wfail Yulang
lake build --wfail
lake env lean Audit/GeneralNominalCenteredHeadMatCompletionCollision.lean
```

The [new audit](../../lean/Audit/GeneralNominalCenteredHeadMatCompletionCollision.lean)
lists all **56 public theorems**, with no missing or duplicate entries.
Dependencies are limited to `propext`, `Classical.choice`, and `Quot.sound`;
one theorem has no dependencies. The independent reviewer also ran each of
the four modules directly with `lake env lean`; all exited **0**.

From the repository root, `git diff --check` exited **0**. The source-scope
check confirmed that existing-file edits only append four root imports and
the design-index entry. Every new module is imported, and the new proof
modules contain no disallowed proof construct. Branch and HEAD remain
`astra2/centered` and `f83402ee5685378ef7ff514e9281eff73aa810d7`.
