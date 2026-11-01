# R136 nested formal permission constructor proof

Status: CONSTRUCTED AND KERNEL-CHECKED; independent review pending.
Producer: `/root/r136_lean_proof`. Exact two-file lease only; no descendants.
Source baseline: `abbe733b952138b5d576c30936692dd262f3e92f`.
Contract SHA-256: `99138f4ed08a48ab010b51b2e3f2cc17d2f5e1c228af20bd8fddbef40d12734b`.

## Original claim and application

Original parent `YulangClosure.SourceProblem.InferenceSoundness`,
`Contracts.lean:128–130`, retains its full quantification:
`∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a`.
This is a proposition definition, not a proved concrete source instance.
Original effect hygiene H is the unchanged statement in
`notes/theory/2026-10-11-oracle-global-effect-hygiene-proof.md` §1:
every successfully lowered original source program, negative occurrence,
lexical scope/binders, actual copy/use and actual call/output route; exact-instance
subtraction preserves independent same-family contributions, retains symbolic
tails/current and future checks, and transports actual correlated identity.
That manuscript is a frozen research derivation, not semantic authority.
The authoritative selected polarity policy is
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–4;
its §6 withdraws the old callback expected result. No expected result is used.

Application to the parent: `constructor_inventory` replaces an assumed
structural permission-inventory equality for this modeled constructor with a
proved recursive equality, and `inventory_membership`/`record_identity` identify
the exact negative source port and complete retained record. Inventory sequence
equality preserves order and duplicates. This is usable once actual HIR/source
construction is decoded to this tree. It supplies none of the original
`sourceJudgment`/`sameScoped` or hygiene H conclusions by itself.

First remaining premise/owner: the source-correspondence lane must authenticate
actual HIR IDs, source annotation shape and successful native construction as
this tree/Context/Row traversal, including resource/identity failure behavior.
Then the arrival/capture/export/copy/consumer lanes must prove actual retained
port arrival, use correlation, tail constraints, checking and Catch subtraction.
`OriginalEffectHygiene` supplies its existing original publication/replay/expiry
results, not these missing premises. Both whole parent gates remain OPEN.

## Source map and represented domain

All Rust reads used immutable baseline blobs. Source owners:

- `candidate_source.rs:701–707,709–717`: polarity-sensitive nested row
  preflight, argument flip, result preservation; nonempty tuples and no
  immediate effect annotations on tuple children.
- `candidate_source.rs:1323–1341,2472–2475`: separate `FormalEntry` versus
  `FormalAnnotation` actions and dispatch.
- `candidate_effect.rs:1607–1609,1614–1748`: paired value constructor;
  argument-value recursion, result-value recursion, argument-effect emission,
  result-effect emission in that order; tuple element order/path.
- `candidate_effect.rs:1763–1835,1897–1976`: separate outer entry construction
  and successful formal-annotation integration (line ranges from fixed packet;
  owners read directly across relevant surrounding definitions).
- `shadow_apply.rs:2609–2640,2680–2711`: nonempty path interpretation and
  nested permission export still require authentic capture/arrival.
- Correct HIR path: `crates/yu-hir/src/module/source_annotation.rs:630–687`.
  `parse_row` pushes concrete and symbolic operands into separate sequences,
  allowing at most one symbolic tail; it does not forbid concrete-plus-tail.

`Value` is the permission-inventory projection: leaves abstract scalar,
variable and hole value behavior; Function has two value children and their
optional effect rows; tuples contain value children with no immediate effects.
`Elements` preserves every tuple index and permits arbitrary finite arity;
`supported` rejects the empty tuple. Function argument polarity flips; results
and tuple children retain polarity. Paths append exact steps. `Row` separately
stores row position, concrete member sequence and symbolic variable sequence.
`Context` and `Metadata` reuse the existing `FormalPermissionSourceOrigin` /
`FormalPermissionCaptureConstruction` definitions. Nat encodings require real
source-ID authentication; no injectivity is assumed or established here.

`ports` inventories all ports independently of grants. `inventory` follows the
native append order directly; `inventory_exact` proves it equals `flatMap emit`
over all ports. `emit_exact` proves precisely that a negative, nonempty concrete,
zero-symbolic row emits its one exact record. No conclusion appears in an input
record field or a theorem hypothesis. `construct` computes support rejection;
its theorem quantifies arbitrary trees/outputs and characterizes success.

`mixed_row_boundary` rejects concrete-plus-single-tail at a negative nested
port while accepting the same row at positive variance. `EntryPermission` and
`constructEntry` are a separate outer-entry inventory projection;
`entry_mixed_retained` retains concrete members there even with one symbolic
tail. The actual entry equality linking the symbolic tail is NOT modeled or
claimed. Registration/formal identity checks also remain a source-owner premise.
No outer entry permission is inserted into the nested structural inventory.

Omitted: native value/effect allocation and memo behavior, constraints, HIR
formation authentication, resource failure/rollback, equality/generalization,
copy/use correlation, tail connectivity, arrivals, capture completion, consumer
execution, handlers, subtraction, complete source language/typing interpretation.
No accepted source feature or original parent quantifier is removed: these are
explicit boundaries of this auxiliary constructor projection only.

## Toolchain and execution receipt

Read the pinned project `lean-toolchain`, `lakefile.toml`,
`lake-manifest.json` and README original-effect-hygiene/toolchain sections.
No external packages. Read-only `elan which lake` resolved:
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Actual outputs, both exit 0:

```text
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

Working directory: `notes/theory/lean`. Commands used resolved native Lake:

```text
lake --version
lake env lean --version
lake build +YulangClosure.FormalPermissionConstructorR136
lake env lean -j1 -M1024 YulangClosure/FormalPermissionConstructorR136.lean
lake build +YulangClosure.FormalPermissionConstructorR136
```

Each proof command used `LEAN_NUM_THREADS=1` and one inherited CPU affinity;
Python monitored the complete process group's RSS through `/proc` every 0.1s
and would kill the process group at 1,073,741,824 bytes or the command deadline.
No resource limit triggered. Build deadlines were 120s then 90s; direct check
90s, with actual cumulative verification elapsed 24.528s (<120s total).

| Attempt | Actual result | Elapsed | Peak sampled group RSS |
| --- | --- | --- | --- |
| Initial named build | Lean/Lake exit 1 | 21.920s | 1,029,435,392 bytes |
| Repaired direct Lean + every type/axiom print | exit 0 | 1.304s | 900,231,168 bytes |
| Final named build, 13 jobs | exit 0 | 1.304s | 914,169,856 bytes |

Material failure preserved: importing OriginalEffectHygiene exposed an existing
`YulangClosure.Step` name which shadowed the opened capture `Step`. Initial
errors at lines 42/47/50 etc said `List Step` received a machine-step relation
instead of a Type; elaborator recovery generated `sorryAx` in the failed run.
The repair introduces explicit alias `PortStep :=
FormalPermissionCaptureConstruction.Step` and uses `List PortStep`. No written
`sorry`/`admit` was used. Both final checks accept all eight theorems with no
`sorryAx`. One pre-existing unused-simp warning remains in
`FormalPermissionSourceOrigin.lean:172`; the new module has no warnings.

The skill helper was not invoked because it creates a temporary audit source,
forbidden by this packet. Primary explicitly accepted in-file `#check` and
`#print axioms`, so every delivered theorem has both commands in the leased
module. Normal Lake-generated `.lake/build` artifacts were the only generated
writes; no scratch source, new environment/cache setup, dependency installation,
network, root import, toolchain/config changes or full/default build occurred.

## Complete theorem types and axiom audits

These are theorem declarations, not propositions/axiom declarations.
The source contains the complete proof terms and reproduces all printed types
and audits. Full names/types below retain all binders and premises.

```lean
theorem YulangClosure.FormalPermissionConstructorR136.inventory_exact (c : Context) (value : Value) (p : Bool) (path : List PortStep) :
      inventory c value p path = (ports value p path).flatMap (emit c)
```

Actual transitive `#print axioms` result: `[propext]`.

```lean
theorem YulangClosure.FormalPermissionConstructorR136.element_inventory_exact (c : Context) (es : Elements) (p : Bool)
      (path : List PortStep) (i : Nat) :
      elementInventory c es p path i = (elementPorts es p path i).flatMap (emit c)
```

Actual transitive `#print axioms` result: `[propext]`.

```lean
theorem YulangClosure.FormalPermissionConstructorR136.emit_exact (c : Context) (port : LocatedPort) (permission : Permission) :
    permission ∈ emit c port ↔ ∃ row, port.row = some row ∧
      port.positive = false ∧ row.concrete ≠ [] ∧ row.variables = [] ∧
      permission = record c port.path row
```

Actual transitive `#print axioms` result: `[propext, Quot.sound]`.

```lean
theorem YulangClosure.FormalPermissionConstructorR136.inventory_membership (c : Context) (value : Value) (p : Bool)
    (path : List PortStep) (permission : Permission) :
    permission ∈ inventory c value p path ↔
      ∃ port ∈ ports value p path, ∃ row, port.row = some row ∧
        port.positive = false ∧ row.concrete ≠ [] ∧ row.variables = [] ∧
        permission = record c port.path row
```

Actual transitive `#print axioms` result: `[propext, Quot.sound]`.

```lean
theorem YulangClosure.FormalPermissionConstructorR136.constructor_inventory (c : Context) (value : Value) (p : Bool)
    (output : List Permission) :
    construct c value p = some output ↔
      supported value p = true ∧ output = (ports value p []).flatMap (emit c)
```

Actual transitive `#print axioms` result: `[propext, Quot.sound]`.

```lean
theorem YulangClosure.FormalPermissionConstructorR136.record_identity (c : Context) (path : List PortStep) (row : Row) :
    (record c path row).metadata.parameter = c.parameter ∧
    (record c path row).metadata.occurrence = c.occurrence ∧
    (record c path row).metadata.owner = c.owner ∧
    (record c path row).metadata.scope = c.scope ∧
    (record c path row).path = path ∧
    (record c path row).metadata.sourceRow = row.position ∧
    (record c path row).metadata.concrete = row.concrete
```

Actual transitive `#print axioms` result: `[]`.

```lean
theorem YulangClosure.FormalPermissionConstructorR136.mixed_row_boundary (position atom tail : Nat) (rest : List Nat) :
    rowAllowed false (some ⟨position, atom :: rest, [tail]⟩) = false ∧
    rowAllowed true (some ⟨position, atom :: rest, [tail]⟩) = true
```

Actual transitive `#print axioms` result: `[propext, Classical.choice, Quot.sound]`.

```lean
theorem YulangClosure.FormalPermissionConstructorR136.entry_mixed_retained (c : Context) (registration formal annotationPosition entry
    position atom tail : Nat) (rest : List Nat) :
    constructEntry c registration formal annotationPosition entry
      ⟨position, atom :: rest, [tail]⟩ =
      some [⟨registration, formal, c.metadata position (atom :: rest), annotationPosition, entry⟩]
```

Actual transitive `#print axioms` result: `[propext, Quot.sound]`.

No project axioms, `sorryAx`, native-evaluation assumptions or checker bypasses
occur in any delivered theorem's printed transitive audit. Source scan of the
12-module local import cone found no code occurrences of `sorry`, `admit`,
`axiom`, `skipKernelTC` or `native_decide`; the sole textual match was the word
“admit” in a comment at `FormalPermissionLiveCapture.lean:13`.

## Frozen artifacts and dependency hashes

New theorem file: 10356 bytes, SHA-256 `3289bccd2b85dd4576adb1c4a870e635985b60e2e87c459d9174c4a0477eab4f`.

Local Lean import cone at verification:

```text
2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e notes/theory/lean/YulangClosure/Contracts.lean
181d5075e2fa3ed5f4adfe4029b368461638b6ac6f62341ec165e6e3980ee13c notes/theory/lean/YulangClosure/FormalPermissionCaptureConstruction.lean
3289bccd2b85dd4576adb1c4a870e635985b60e2e87c459d9174c4a0477eab4f notes/theory/lean/YulangClosure/FormalPermissionConstructorR136.lean
0e1bd4f2ae95e798561e014595e66ec9b6d9b342dbd2b15d0d5c9d346838c53e notes/theory/lean/YulangClosure/FormalPermissionLiveCapture.lean
db37f9d83e450a450d689b9eed46311108e635eb846d268b7a3a567dcee624fd notes/theory/lean/YulangClosure/FormalPermissionSourceOrigin.lean
39aa5cefa078dd423e54f0d9790f9a48e136326742e01f65149f317c907be957 notes/theory/lean/YulangClosure/NativeClosureEnvironment.lean
926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f notes/theory/lean/YulangClosure/OriginalEffectHygiene.lean
126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean
3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1 notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean
02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861 notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean
8d370ee57e486ae48607d1bab493ae5135f28bf8a5a7ff1b0ef240fc0247e424 notes/theory/lean/YulangClosure/SourceFunctionMembership.lean
6019fd9d57cde50183e016bd0c72de2c6eee72009065d85119fb0348dbcf0168 notes/theory/lean/YulangClosure/SourceIdentityWorld.lean
```

Committed Rust dependencies:

```text
bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49 crates/yu-solver/src/candidate_source.rs
102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01 crates/yu-solver/src/candidate_effect.rs
2fa42a5570e660babab5da6361e0d71e0c022b234a21f7e01b78eafbfc65f278 crates/yu-solver/src/shadow_apply.rs
409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f crates/yu-hir/src/module/source_annotation.rs
```

STOPPED_WRITING. Only the two leased artifacts and ordinary verifier-generated
project outputs were written. No Rust edits/diffs, tests, Git mutations,
independent-review claim, production claim or parent closure claim.
