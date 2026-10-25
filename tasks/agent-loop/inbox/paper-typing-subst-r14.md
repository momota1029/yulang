# R14 handoff — universal introduction dependency probe

Status: `STOPPED_BUDGET_LIMIT`; the requested R14 constructor and transport
were not added. Full paper typing remains `OPEN`. Contract
`FULL-PAPER-TYPE-SUBSTITUTION-20261025/r14` has SHA-256
`742444e019b87526fed8fa7fcf2d335191381c086a0e82938b0e4dc9c2afc04c`.
Admission baseline was `06fc932be71b3125f7455ef4ef0f08ace6b100e1`; the
contract/current-state admission record was committed as `a79997741`.

## Source goal and result

The source rule is value-only `Λα.v : ∀α.A` with
`α ∉ fv(D, Γ)`, at `docs/yulang-operational-type-safety-ja.tex:203-207,237`;
the preservation proof calls out shifting declarations and the whole shared
environment together at `:953-977`.

The R14 dependency is a binder-depth-generalized substitution/shift law for
every mapped declaration field, including executable template bodies. R14 did
not add a `typeAbstraction` typing constructor, did not re-index the six
judgments, and did not change syntax or the R13 typing module. No forall
freshness or introduction claim is proved by this handoff.

The candidate module
`notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean` contains
constructive type-substitution and environment/graph-environment shift laws.
Its final frozen SHA-256 is recorded with the sprint state. Those declarations
were individually elaborated without local diagnostics in failed module
checks, but the final module build and per-theorem axiom audit were not obtained;
they are therefore **not reported as checked artifacts**.

## Exact blocker evidence

The attempted declaration-table equation was

```text
mapDeclarationTable (liftSub σ) (mapDeclarationTable shift D)
  = mapDeclarationTable shift (mapDeclarationTable σ D)
```

After unfolding the real map, Lean left obligations for nested
`liftSubN` substitution composition in operation, nominal, and primitive
entries, and a `TemplateBody` equality whose `body` field is recursively mapped
`Computation` syntax. That syntax mapping itself crosses values, computations,
patterns, constructor branches, guarded branches, both arm forms, handlers,
and mappers. R14 did not close these obligations.

The attempted syntax proof used `induction value/computation/pattern`; Lean
rejected each because those types are mutually inductive. `Value.rec` was
inspected and exposes 24 simultaneous motives, including list, option, and
product helper motives. The attempted handler simplification also left the
`List.attach.map` equations for value and operation arms, and mapper equations
for `OperationInstance.subst`. No concrete mathematical counterexample was
found; these are unresolved proof-construction obligations, not a refutation
of the mapping law.

## Resource and verification receipt

Pinned project Lean 4.35.0 and Lake `5.0.0-src+eb6cafb`; commands used
`-j1 -M1024` and only one Lean process at a time. R14's limit was 12 serial
Lean/Lake invocations. The invocation count reached **13/12** because a wrong-
working-directory cleanup attempt launched one extra failed Lean command.
This is recorded as a budget overrun; no further Lean/Lake process was started.
Checker time stayed far below 180 seconds (each process returned in under one
second), but cumulative time was not instrumented precisely.

Material failures retained:

1. Initial shift/environment helper builds exposed and repaired a shift
   composition goal; one intermediate helper build passed.
2. The declaration-table `simp` attempt left the exact real-field obligations
   above.
3. The depth-generalized raw syntax attempt failed at the unsupported ordinary
   `induction` tactic for the mutually inductive family. Remaining diagnostics
   included list `attach.map` and `OperationInstance.subst` commutation goals.
4. A recursor inspection succeeded for `Value.rec`; its 24 motives establish
   the required mutual proof surface but do not themselves prove it.
5. Final focused build and exact axiom audits were omitted after the call limit.

No tests, default-target build, Rust build, or production edit. No reviewer or
child was admitted. Independent reviews R9-R13 remain `NOT_RUN`; eight
historical/foreign reservations remain quarantined. Parent inference/executor,
source/native, original A/B, and full-paper typing obligations remain `OPEN`.

## Next proof packet

Construct and check the depth-generalized shift/substitution theorem over the
full mutually inductive syntax family using its generated simultaneous
recursor (all constructors, nested attached lists/options/products, type
abstraction, and rigid operation-arm binders). Apply it to template-body and
declaration-table mapping before changing typing judgments. The successful
environment and graph shift lemmas are candidate inputs, not accepted until a
fresh focused build and complete axiom audit succeed.

Writes stopped for R14. No theorem closure or independent review is claimed.
