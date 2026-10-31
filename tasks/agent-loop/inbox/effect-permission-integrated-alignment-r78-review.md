# R78 independent review

Reviewer: `/root/r78_review` (`compiler_referee`), independent and read-only.

**Verdict: REJECT R78 integration; ACCEPT the bounded Lean slice. One blocking finding.**

## Blocking finding — no typed definition identity bridge

- `candidate_receiver.rs:505`: `InventorySourceAlignment.target` has type `&DefinitionOrderId`.
- `candidate_receiver.rs:4512`: matching `LocalSourceResolution::ModuleDef(target)` binds `&yu_hir::DefId`.
- `candidate_receiver.rs:4519`: that HIR `DefId` is assigned directly into the solver `DefinitionOrderId` field.
- Definitions are in `yu-hir/src/module/local_source.rs:443`, `yu-hir/src/module.rs:1093`, and `yu-solver/src/lib.rs:496`.

These are distinct nominal types. `DefId` contains module, spelling, and same-name ordinal; `DefinitionOrderId` contains collection-artifact identity and admitted-binding ordinal. There is no applicable coercion or cross-type equality implementation. With `shadow-apply-candidate` enabled, this initializer cannot type-check. This conclusion follows from the source types; no compiler was run.

The same missing bridge already occurs in R77 at `candidate_receiver.rs:2429`, where the resolved HIR definition is compared directly with `DefinitionUse::target()`. The bounded R77 Lean acceptance therefore does not establish executable Rust correspondence. This violates R78's exact target-definition join and the authoritative implementation-correspondence requirement.

Minimum closure: translate the resolved HIR definition through an authenticated HIR-binding/root-to-collected-definition bridge, validating the collection artifact, exact root/binding, and uniqueness. Use the translated solver identity in both R77 selection and R78's retained alignment. Changing the field type to `DefId` only moves the missing bridge to comparisons with `DefinitionUse::target()`.

Collection creates a temporary `definition_by_hir_id` map at `lib.rs:1059`, inserts binding identities at `:1078`, and resolves pending targets near `:1400`; the map is discarded. Retained HIR bindings and root/definition indexes contain data that may support a future exact bridge, but the submitted path does not use a checked one. `candidate_value_graph::Graph.modules` separately retains root-to-`DefId` data; it does not make the nominal types interchangeable.

## Consumer trace

The coordinate separation itself is present in the candidate:

- Capture keeps every retained call, including calls without module-Name alignment, in enumeration order; it retains the call index and original input pointer.
- Apply checks authenticate expression occurrence, checking occurrence, owner, operands, and cause.
- Selected-call matching uses the callee Name occurrence, intended target, and receiving owner; multiple matches reject.
- Root view reuses the stored alignment and checks Apply coordinates separately from Name/use coordinates.
- Existing slot-0/slot-2 facts, permissions, formals, recipes, relations, ancestry, root checks, and failure checks remain after the new checks. No solver-state mutation was found.

Relevant receiver tests and call collection were inspected but not executed. No additional compiler-correctness finding was established.

## Lean evidence

I independently reconstructed both historical audit inputs in memory and decoded both retained base64 outputs.

| Evidence | Bytes | SHA-256 |
|---|---:|---|
| Audit 1 stdin | 57,409 | `fe4816df474cf33882c161966d54c24303e34f75e5fb7a4e30212b0d9dffcfb3` |
| Audit 1 stdout | 23,812 | `1a6fc002799a0c3b33424f15038a25643eafc93b4092b68094e5497984272285` |
| Audit 2 stdin | 57,790 | `0c61742191ea55c18c68ef6ef4e30e1c34cf48bb24275ca310481629602ed0c7` |
| Audit 2 stdout | 19,841 | `306d1c05ebb3bcddbae50f5338b2ce59d4157f5ab17182e87d6a8fedada60f51` |

Audit 1 exited 1 with 19 errors and recovery `sorryAx`; it supplies no accepted proof evidence. Final audit 2 exited 0 with nine complete theorem types, no errors, and no `sorryAx`. Every theorem reports exactly `propext` and `Quot.sound`; no `Classical.choice` or project axiom appears.

The audited declarations establish the two coordinate equations from R77 `Alignment`; root-coordinate success from `Captured`; exact indexed/unique call and use joins; unchanged same-use plan, R66 owner-selection, and parameter-recipe conclusions; and finite successful/rejected joins. Consumer success is a conclusion rather than an assumed field. `construction_certifies` remains conditional on computed `capture` returning `some`; its `none` branch proves `True`.

The mathematical model uses a common `Key` for targets. It does not supply the Rust `DefId` → `DefinitionOrderId` bridge, Rust pointer identity, branded HIR ownership, genuine R66 incidence/root, or whole-language A/B closure.

All 14 final source/slice hashes, all 17 baseline input pins, and the pinned Lean executable hash matched. Frozen candidate artifacts matched the workspace:

- Rust receiver: `5e99035a94e1d3f618e03e932e59933fb3d5eb9f501455779bcb52e65e7c7a3a`
- Lean module: `bfe304c33e6018910739d58d37c2122a4a475fac57e00091e1a700a965510029`
- Proof handoff: `2a271605d7ec6942fec80f2288a6da615f013167616321140806894ce3d13dd5`

**STOPPED / WRITES STOPPED.** No files were changed by the reviewer; no author contact, build, test, Lean invocation, generated artifact, environment, or Git write occurred. Luna persisted this report.
