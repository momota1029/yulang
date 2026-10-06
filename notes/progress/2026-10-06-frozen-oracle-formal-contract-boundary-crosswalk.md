# Frozen Oracle formal-keyed contract boundary crosswalk

Date: 2026-10-06
Status: frozen, independently compiler-referee-reviewed research-only historical characterization; two minor locator/scope findings closed
Yulang3 baseline: `11e884131de3193b6bc33e894a996f7fe5a06b5d`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`, `/tmp/yulang2-oracle-rebuild`
Exclusive lease: this note only
Semantic and implementation authority: none

## Question and result

Locate a historical mechanism nearest the current missing source producer:
how an annotation attached to a formal survives lowering and reaches a later
function boundary. This is a bounded static producer/consumer trace, not a
claim that the historical mechanism supplies current original profiles.

The frozen implementation has a concrete chain:

```text
formal annotation
  -> ArgEffectContract markers
  -> Poly Arena map keyed by formal DefId
  -> compiled-runtime import remaps that DefId
  -> specialization reads the same formal-keyed contract
  -> function-boundary hygiene wrapper
```

This is more persistent than ephemeral frame subtraction: it carries a
formal-keyed annotation contract across lowering and import to a consumer.
It still does not register the current complete original `beta/Slots(beta)`,
typed incidences, owner/receiver/receipt maps, or a joint `(nu,K,D)` relation.
The specialization consumer runs at a typed function boundary; it does not
produce a Q-independent contract for an unknown ordinary formal at `f x`.

## Historical chain

All paths below are relative to the frozen Oracle tree.

1. `crates/infer/src/lowering/expr/lambda.rs:1300–1434` creates an
   `ArgEffectContract` from a Function annotation by recursively collecting
   effect-family markers with a family path, nesting depth, and preservation
   mode. The extraction traverses the lowered annotation structure; it does
   not retain a source annotation occurrence ID or full typed position path.
2. At `crates/infer/src/lowering/expr/lambda.rs:870–920`, the lambda lowering associates the resulting
   contract with the resolved parameter `DefId` in
   `poly::expr::Arena::arg_effect_contracts`. The Arena declares this as
   `FxHashMap<DefId, ArgEffectContract>` (`crates/poly/src/expr.rs:81`). This is a
   durable source-definition key inside that arena, distinct from a transient
   constraint origin.
3. `crates/infer/src/compiled_runtime.rs:1766–1803` imports all or selected
   contracts alongside definitions. The import path maps the old `DefId` to
   the imported definition ID and clones the contract. This preserves the
   formal association through that particular compiled-runtime import route;
   it does not freshen or prove a semantic relation over type/profile fibers.
4. Specialization has multiple consumers. The expression-boundary helper at
   `crates/specialize/src/lib_support/specializer.rs:300–365` handles Lambda
   expressions and looks up the contract through that lambda parameter's
   `DefId`; instance boundaries use `def_argument_effect_contract` at
   `:409–418`. More directly, application lowering in the specializer at
   `:180–201` calls `callee_argument_effect_contract` for the callee spine.
   That helper at `:750–768` handles a resolved `Var` by following its target
   definition and selecting the indexed lambda parameter contract; it also
   handles a literal Lambda spine. The contract is then passed to
   `wrap_boundary_with_argument_contract` for the argument boundary. This is
   a concrete historical **post-inference application-boundary consumer** of
   a definition-keyed annotation contract.
5. The inference application producer remains a distinct route:
   `crates/infer/src/lowering/expr/tail.rs:535–563` creates the call Function
   demand from callee/argument/result endpoints. The contract consumer above
   runs in specialization and does not itself form the unknown formal's
   original source relation or establish Q-independent admission.

## Correspondence and limits

| Historical structure | Useful structural analogue | Missing current bridge |
|---|---|---|
| `DefId -> ArgEffectContract` | Keep annotation metadata tied to the exact formal across later phases | Current annotation occurrence identity, `beta/Slots(beta)`, and complete profile interpretation |
| Imported `DefId` remapping with cloned contract | Preserve a formal association across a known import map | Original-scope transport of all typed incidences and the same joint `xi=(nu,K,D)` |
| Specialization argument-boundary consumer for resolved callee definitions | Retrieve a formal-keyed contract by callee-spine index and apply it at an argument boundary | It consumes a previously built contract after inference; it does not prove original profile completeness or independent admission |
| Separate application Function-demand producer | Calls can add constraints on shared endpoints | Proof that ordinary source uses introduce exactly the permitted original positions and complete contribution footprint |

The historical mechanism therefore identifies a concrete design shape worth
comparing: **definition-keyed annotation contract storage plus explicit
identity remapping and a resolved-callee/indexed argument-boundary consumer**. Its marker language is
lossy relative to current requirements: the prior annotation archaeology
records that family/depth markers can conflate parameter and result branches
and deduplicate equal markers. No conclusion is drawn that the old compiler's
behavior is correct or that its boundary wrapper has current semantics.

This does not close current original-introduction completeness, independent
admission, typed capture/receipt transport, source adequacy, principality,
soundness, or production conformance. Frozen Oracle semantics remain
non-authoritative.

## Coverage and checks

The frozen worktree resolved to the pinned commit. This pass used bounded
`rg` and source-window reads in the annotation producer, Poly Arena,
compiled-runtime import, specialization consumer, and application producer.
No Oracle executable, build, test, mutation, or performance sample ran. This
note has not yet received independent review. Other import/export routes,
serialized cache behavior, and runtime/provider evidence were not audited.
