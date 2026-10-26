# Independent review: paper term substitution algebra

Disposition: **CLEAN for the module's stated algebraic and represented-typing
scope**. No BLOCKING, major, or minor findings. No source repair requested.

Reviewer: `/root/paper_allocation_execution`, fresh non-author review of this
target under the generic compiler-referee/proof-review fallback. The reviewer
authored the separate allocation bridge, which this module does not import;
the reviewer did not construct or edit this substitution algebra.

## Frozen inputs

| Artifact | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/PaperTermSubstitutionAlgebra.lean` | `b35a14e1872cec5284a68cb38e9ea6fd0c9dc23cbd6d8017c82a550ec60a379d` |
| `/workspace/scratch/f98087c7ac1a/term-algebra-audit.log` | `87c14204604cc51c97c864ef012fbe89539ad73785b8d656498114606b9faa0d` |
| `/workspace/scratch/f98087c7ac1a/term-algebra-build.log` | `65e5aab98907fcac0598d37a7473f516a539955f8b6145b93f26c24faf792ac8` |
| `/workspace/scratch/f98087c7ac1a/TermAlgebraAudit.lean` | `25141c06edb812901dc5dc04fb751532630bf54aef0ff917a4e4c7f5423875ea` |

The source hash was independently computed and matched the primary's frozen
hash. The source is 700 lines, with 58 authored theorem declarations: 31 public
and 27 private. All definitions, private induction bundles, theorem statements
and proof bodies were read.

## Source and dependency correspondence inspected

- Root operating instructions, the repository Lean proof skill and its source /
  execution references, and `.codex/agents/compiler-referee.toml`.
- `PaperTermSubstitution.lean`: actual `renameTermValue` /
  `renameTermComputation`, one- and N-binder lifts, `replaceTermValue` /
  `replaceTermComputation`, type-binder shift, support predicates, public
  `Option` APIs, `TermSubstitutionTyped`, existing typed replacement/support
  proofs and `compose`, and `graphFormalReplacements`.
- `PaperCoreStep.lean`: actual `singleReplacement`, its index-zero/successor
  equations, and its independent typing theorem.
- `PaperExecutionSyntax.lean`: actual type substitution through values,
  computations, type abstractions, operation instances and omitted term forms.
- `PaperExecutionBinderLaws.lean`: exact
  `mapPaperValue_shift_substitution_commutes`, including its binder depth and
  lifted type substitution; the new module correctly uses depth zero.
- Operational manuscript substitution/binder clauses at lines 952–977,
  simultaneous source `rec` allocation at 324–326 and 980–990, and saved
  continuation/response clauses at 458–466. Corrected core note V1 in §2 was
  read with its source/guard/full-language boundary.

The four direct foundations checked against the earlier frozen baseline were
unchanged:

| Foundation | SHA-256 |
| --- | --- |
| `PaperTermSubstitution.lean` | `42d7f46d992e715443a7116066b51ae1748849718f6c4e716d9169ea069059d9` |
| `PaperCoreStep.lean` | `6357b14217e82421eed87da981cef8e94014dcaea634d746ad0b4bb39bff6144` |
| `PaperExecutionSyntax.lean` | `78f23b9e946b0259cdb63797ed226706112f71375a013e0b9cc8745ad5afe8b0` |
| `PaperExecutionBinderLaws.lean` | `568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a` |

## Adversarial checks and findings

### 1. Raw opacity is preserved and disclosed

The module header at lines 3–7 explicitly identifies the existing operations and
states that omitted constructors remain opaque. The underlying term renaming
and replacement functions use identity fallbacks. Their supported syntax is
unchanged, and the public partial APIs still reject omitted constructors,
including nested omissions.

Consequently, the raw equations quantify over all actual `Value` /
`Computation` objects but do **not** establish a complete traversal of every raw
constructor. In particular the equation on an opaque `recursive`, `handle`,
`mapOperation`, nominal or variant form must not be promoted to source
substitution for that form. This is an explicit existing scope boundary, not a
missing case concealed by the new proofs. The module does not modify it.

### 2. Binder composition uses the correct dimensions and order

The term-renaming and replacement induction bundles quantify over arbitrary
functions/vectors at each original subtree size. This supports the changing
lifted vectors under binders without an induction hypothesis restricted to the
initial vector. The replacement result's possibly greater size is not used as
an unjustified induction decrease.

One-binder and N-binder laws retain bound indices and shift free replacements.
N-binder lifting uses the actual tuple binder count; it neither permutes tuple
formals nor asserts source-to-de-Bruijn ordering. Lambda, adapter, continuation
response and let/union binders use the matching one-binder lift. Type
abstractions use `shiftTermSubstitution`, not a term-binder lift.

The private `RenameAt`, `TypeRenameAt`, `ReplaceRenameAt`, `RenameReplaceAt`,
`TypeReplaceAt`, `CompositionAt` and identity bundles are all concretely proved
for every size. They are not externally assumed `LocalLaws` or preservation
certificates. The public composition equations have no such law premise.

### 3. Type/term commutation transports the substitution vector too

At lines 393–474, the right side of type/term replacement commutation applies
the same type substitution to both the original syntax and every replacement
value. The type-abstraction case uses `liftSub σ` on the body and the actual
type-shift commutation law for the replacement vector. Ordinary term-binder
lifting commutes with the type map using the independently proved type/term
renaming law.

The fact that the type map traverses more raw constructors than the term
operation does not invalidate these equations: term-opaque constructors remain
term-opaque on both sides after the type map preserves their constructors.
Nothing here implies their full source term-substitution semantics.

### 4. Simultaneous composition is oriented correctly

`composeTermSubstitution outer inner n` is the existing
`replaceTermValue outer (inner n)`. The new composition statements at lines
551–560 use exactly this order: first replace by `inner`, then replace by
`outer`. The arbitrary-vector equations include variable capture under term,
response, tuple and type binders through the proved lift/shift laws. They do not
replace a simultaneous substitution with an ordered sequence of single-variable
substitutions.

The identity and associativity statements at lines 614–633 follow from those
same actual operations. No alternate substitution definition is introduced.

### 5. Graph formal identity and order remain literal

`compose_graphFormals` / `graphFormals_computation` at lines 637–654 use the same
`formals` list on both sides. At index zero a formal remains its literal graph
reference; the successor case recurses through the same list, and only the
captured-value tail is composed. The equations establish no new lookup,
freshness, uniqueness, allocation or guard premise. They are appropriate
algebraic components for the existing explicit graph-formal convention.

### 6. Response cancellation does not replace captures twice

`response_after_environment` at lines 658–670 first lifts the capture vector
over the response binder, then applies actual `singleReplacement response`.
Its successor case cancels the inserted `Nat.succ` renaming and uses the proved
replacement identity; its zero case inserts the supplied response. The exact
resulting vector is:

```text
0       ↦ response
k + 1   ↦ rho k
```

Thus the free variables of captures survive the removed response binder under
the represented operations. As a direct source-level discriminator,
`rho 0 = variable 0` and body `return (variable 1)` return that free variable,
not the response. Body `return (variable 0)` receives the response instead.
The response is already the value supplied after environment substitution;
the theorem correctly does not apply `rho` to it again. This is an equation
about term substitution, not owner freshening or dynamic-world restoration.

### 7. Typed public Option composition proves its second support check

At lines 675–698 the source, middle and target lexical environments are linked
by the unchanged `TermSubstitutionTyped` relation, with declarations, graph and
result type shared literally. The proof uses
`(hv.termReplace hi).termSupported` or
`(hc.termReplace hi).termSupported` for the second public API call. This is a
derived fact about the actual intermediate result, not a new support or
preservation hypothesis.

This distinction matters: on arbitrary untyped vectors, replacing a variable by
an opaque unsupported variant can make the first public call succeed and the
second call fail, while the one-shot public call still succeeds on the original
variable. The submitted theorem excludes that mismatch by actual typing; it
does not claim unconditional `Option` composition. Final typing follows through
the existing typed composition proof. No final result typing is assumed.

## Checker evidence inspected

No Lean/Lake/checker was run by this reviewer. The supplied final direct-check
log is empty, the build log ends with a successful build of the frozen module
and `Build completed successfully (11 jobs)`, and the complete audit ends with
`YULANG_AUDIT_COUNT 306`.

The audit implementation was read. It selects constants by actual originating
module, rejects project axiom declarations, prints exact theorem types and
transitive axiom lists, validates required theorem roots, and rejects every
axiom outside the stated standard whitelist.

An independent read-only parse verified 306 unique, complete BEGIN/END records;
all 58 authored theorem names appear exactly once. Every authored exact printed
type was inspected against the source statement. All 306 transitive axiom
reports were parsed and checked:

| Complete axiom list | Count |
| --- | ---: |
| `[propext, Quot.sound]` | 294 |
| `[Quot.sound]` | 3 |
| `[]` | 9 |

There is no `sorryAx`, project axiom, `Classical.choice`, native-evaluation axiom,
or other axiom dependency in the audit. The new module has no build warning.
Its local unused-simp-argument linter suppression surrounds explicit proof
scripts and does not disable kernel checking. Source scanning found no holes,
unsafe declarations, project axioms or kernel bypass. Generated size-decrease
proofs are included in the complete audit; they are not additional claimed
source-language theorems.

## Review limits and parent status

This review covers the complete submitted module and the relevant actual
dependency definitions. It inspects supplied checker evidence; it is not an
independent checker rerun, a reproof of every pre-existing foundation, a native
compiler review, or validation of all manuscript claims.

No full source traversal, source rec ordering/guard, nonempty-owner freshening,
world-state restoration, progress, source/native realization or original
inference A/B closure follows. Those original obligations remain OPEN. The
review accepts the stated algebra and represented typed API laws without
shrinking or promoting the original parent theorem.

## Write cessation

Only this exact leased review path was written. The frozen source, all caches,
audit artifacts, configuration, other modules and the allocation artifact were
left untouched. No source repair, checker rerun, Git operation or child agent
was performed. Review writes are stopped.
