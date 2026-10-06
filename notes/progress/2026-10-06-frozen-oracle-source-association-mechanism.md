# Frozen Oracle: stored declaration signature to typed definition root

Date: 2026-10-06
Status: frozen, independently compiler-referee-reviewed research-only historical characterization; no findings
Yulang3 baseline: `d312b9445309ee4a946e887567429362ad51b7cd`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`, `/tmp/yulang2-oracle-rebuild`
Exclusive lease: this note only
Semantic and implementation authority: none
Method: bounded read-only source trace and conditional representation derivation
Review: compiler_referee PASS on content SHA-256 `398097806b54e9a5140b8a538e6d3e58791352547f77693ceba5336c3950af28`; scope covers cited producer/consumer chain, receiver-position discriminator, novelty against named archaeology, and historical/non-authoritative boundary

## Objective and distinct result

Find an actual historical source-definition/type-position producer adjacent
to the current missing judgment
`OriginalAssocType_X(beta,p0,j_call;s0,c0)`. The governing current frontier is
[Attach law construction](2026-10-06-attach-law-construction-attempt.md)
§§3–5 and [main source generation](2026-10-06-main-source-generation-minimal-clause.md)
§6. Their selected source meaning, original scopes, complete Call operand and
Q-independent original association requirements are inputs, not reconsidered
here. The Oracle is historical evidence only.

The distinct historical seam is a **stored source signature on a declared
role method**. It retains a source CST and a declaration `DefId`, then builds
a declared structured type, elaborates a receiver where applicable, lowers
that structure to graph nodes, and constrains the same definition root. This
is adjacent evidence for keeping source declaration identity through structural
elaboration. It is not the current inferred-formal Call producer.

The source CST survives in the module declaration; the lowered signature and
graph do not carry nested source-node coordinates. Receiver elaboration gives
a concrete discriminator: a declared scalar at the source signature root
becomes the return child of a generated Function, whose argument is generated
from the role input. Thus a declaration lookup and a typed root are not alone
a source-position-to-typed-position law.

This differs from the prior Function derivation/path trace, claim-qualified
post-projection attribution, and local effect-view/Catch trace. The annotation
variable/closed-row identity path is already covered by the earlier remaining
licensing producer archaeology and is not repeated as this result.

## Hypotheses and claim class

H1: the eight decisive Oracle files below equal the pinned commit bytes.
Verified. The two current governing notes, three assigned rules and three
historical comparison notes also equal the current pinned baseline bytes.

H2: source registration successfully recognizes a role-method binding with
an annotation, allocates its definition, and stores its `TypeExpr` CST as
`StoredSignature::Source`. The corresponding no-body lowering branch is
selected with the same ordered method declaration. Source resolution and
allocation succeed. Registration/order correspondence is a hypothesis for
this selected local trace, not a proved exhaustive module traversal theorem.

H3: annotation building and subsequent signature lowering succeed. For the
discriminator only, the receiver is present, there is a first role input
named `a`, and the built source signature is `Builtin(Int)`. This is a
supplied representation state; no accepted surface program was constructed
or executed to realize it.

Established observations are exact pinned assignments and branch structure.
The consequences under H2/H3 are a bounded historical characterization and
a conditional local representation derivation. They are neither an established
current-language theorem nor a minimized accepted-source counterexample.

## Producer, consumer and lifecycle

All locators in this section are relative to the frozen Oracle checkout.

1. **Declaration and CST are stored together.**
   `crates/infer/src/module_map/mod.rs:1188–1220` recognizes a role-method
   binding, allocates a `DefId`, inserts a module value with its name span,
   and stores `RoleMethodDecl` with owner, name, receiver, definition,
   visibility, source order and the binding annotation CST. The data types
   in `crates/infer/src/lib.rs:436–450,543–552` explicitly distinguish
   `StoredSignature::Source(Cst)` from `StoredSignature::Lowered(SignatureType)`.
   The declaration therefore retains more than the normalized annotation
   shape. The name span stored with the module value is not a map from each
   nested annotation subtree to a typed position.

2. **The same definition gets a symbolic typed root.**
   `lowering/body/role.rs:23–51` chooses signature lowering for a matched
   declaration with no body. `lowering/body/impl_decl.rs:710–744` allocates
   the root, calls `typing.set_def(method.def, root)`, queues `RegisterDef`,
   then calls `connect_role_method_signature`. This association is formed
   before the selected method signature's final subtype submission, without
   consuming solved `RuntimeEvidenceSite` or projected output provenance.

3. **CST is consumed in the declaration's resolution scope.**
   `impl_decl.rs:755–774` reads `method.signature`, builds an annotation
   builder using the supplied module and `method.order`, adds role input and
   associated variables, and adds the `self` alias when a first input exists.
   `lowering/body/signature_helpers.rs:49–65` routes a Source signature through
   `AnnTypeBuilder`, then `signature_from_ann_type`; a Lowered signature
   bypasses CST building. `annotation/builder.rs:117–146` constructs the
   four-port Function structure from source children when an arrow is present.
   `annotation.rs:35–62` and `signature_helpers.rs:259–296` show that the
   resulting value structures retain named declaration/type-variable data
   and type structure, but no nested CST identity or span fields. The stored
   declaration CST is not deleted by this temporary conversion.

4. **Receiver elaboration changes positions.**
   `signature_helpers.rs:68–85` returns the declared signature unchanged
   unless both a receiver and a receiver type are present. Otherwise it
   constructs a new Function with the first role input as parameter, no
   explicit argument-effect row, and the supplied signature as return after
   splitting a top-level effectful form (`:88–95`). This is a concrete
   position-transforming producer before the selected final comparison.

5. **Structured signature becomes graph nodes.**
   `impl_decl.rs:789–812` invokes `SignatureLowerer::lower_pos` and associates
   its output with the already registered root by requesting
   `pos <: Neg::Var(root)` with `OriginId::unknown_internal()`.
   `lowering/mod.rs:571–616` recursively lowers a Function's parameter
   negatively, argument effect negatively, return effect positively and
   return positively, and assembles `Pos::Fun { arg,arg_eff,ret_eff,ret }`.
   The structural slots are therefore real graph constructor fields. This
   inspected final edge has no emitted annotation-node/typed-path association
   record. It still has its typed endpoint and declaration-root association;
   no global loss or impossibility of a later join is claimed.

The relative order is registration → definition-root association → declared
signature construction → receiver elaboration → graph construction → final
subtype request. This is a source lowering trace before projection and before
that final comparison's result. It does **not** establish that no earlier or
nested lowering operation has submitted or processed solver constraints.

## Smallest position discriminator

Under H3, the exact receiver construction gives:

```text
source signature T = Builtin(Int), source signature root = epsilon
receiver = Some(name), first role input = a

elaborate(T) = Function {
    param = Var(a), arg_eff = None, ret_eff = None, ret = Builtin(Int)
}

lower_pos(elaborate(T)) = Pos::Fun {
    arg = lower_neg(Var(a)),
    arg_eff = lower_arg_effect_neg(None),
    ret_eff = lower_ret_effect_pos(None),
    ret = lower_pos(Builtin(Int))
}
```

The declared scalar's source root corresponds, in this constructor trace,
to the generated Function's return child. The generated argument child is
not a child of T's scalar annotation tree. One scalar and one generated
wrapper suffice to falsify the tempting rule “reuse the source annotation
path unchanged as the complete typed signature path.” Removing the receiver
is a logical mutation: `role_method_signature_with_receiver` returns T itself,
so this wrapper and path shift disappear. No runtime mutation was executed,
and no acceptance, effect behavior or final solver difference is claimed.

This does not prove a current `p0 -> s0` mapping. It demonstrates that even
a historical producer which retains CST and definition identity needs an
explicit elaboration-aware position correspondence. No graph-ID uniqueness
or interning assumption is required for this discriminator.

## Exact current gap, independence and stop condition

The historical declaration can supply its `DefId`, stored signature CST,
resolution order, receiver elaboration and structured graph root. This
selected consumer does not emit a current original source incidence
`(beta,s0,p0,c0)` at the complete source-rooted `j_call`. Its input is an
explicit declaration, not the unannotated shared formal in the selected
nested `apply` example. It does not type a contribution containing the whole
invocation, establish its own-upper versus inherited tags, construct a
complete `Slots(beta)` inventory, interpret the original `(nu,K,D)`, or
prove either licensing direction. The root constraint cannot fill those
coordinates merely because it is attached to a source definition.

Oracle source is independent historical artifact evidence relative to current
stipulated-transition probes. Its registration, annotation builder and
signature lowerer are parts of one implementation and share resolution,
allocation and graph assumptions; they are not independent semantic oracles.
No checker is used to assume or certify these rules. Byte equality establishes
artifact provenance, not source semantic truth or implementation correctness.

Omitted: accepted-source realization of H3, all other method/annotation/import
routes, complete declaration traversal/order correctness, dynamic method
selection and execution, solver/projection correctness, global provenance
reconstruction, current complete profile/admission/licensing and production
gates. Failure conditions are changed decisive blobs, registration/order
mismatch, absent receiver or first role input for the discriminator, build or
lowering failure, and treating earlier solver work as absent without proof.
No repository-wide absence claim is made.

Stop condition is met: one distinct producer/consumer chain and one position
falsifier are characterized. Recommended next action: define and audit the
current contribution-typing clause with an explicit source-to-elaborated
position relation; use this historical wrapper witness only to reject an
identity-path shortcut. Further Oracle attribution tracing does not close
the current source introduction law by itself.

## Checks, resources and frozen dependencies

Commands: bounded `rg -n`, `rg --files`, `sed -n`; `git rev-parse HEAD` in
both repositories; Python byte/SHA-256 comparisons against `git show` of the
two pins; lease-path absence check and note-local whitespace check. Initial
aggregate captures truncated; decisive cited source windows were read in
bounded captures. One exploratory lookup used nonexistent `expr/name.rs`
and `body/act_decl.rs` paths; those failed searches supply no absence evidence.

Eight decisive Oracle files matched their pinned bytes:

| Path under `crates/infer/src/` | SHA-256 |
|---|---|
| `lib.rs` | `59c3ca10066606a13e4fa15e6c10442b9ab2e2cf809537faa39861ddd8bad4dd` |
| `module_map/mod.rs` | `05415473b824ce540207e694bf35883536cb5ef0ec67e8dae12f943411388134` |
| `lowering/body/role.rs` | `5081c5b9624413c846edf7b30a662f8197461770d303e580ec4f3e98a28eb81c` |
| `lowering/body/impl_decl.rs` | `7353af913f609b32502e8a0c18515aee95ef7419dc478432a9444b13e80d7b05` |
| `lowering/body/signature_helpers.rs` | `8302de665ec38ef4a1cf2e00b762b74c7f5fb85e866526224ec527d487cea4cd` |
| `lowering/mod.rs` | `244e5f8ea339d2e24aa1f8456e99072e4a491b97da58348a4e79eed188ce61a1` |
| `annotation.rs` | `bfbd137ebe18546be645300a45e4c1d7acd13f703647f4a2ce1cad787a8a9602` |
| `annotation/builder.rs` | `baad6a964909eaee3e7822aa5445dca8cd2f70185bd5a1f2157e878a512ddf7b` |

One lightweight sequential shell/source process at a time; zero Oracle runs,
builds, tests, heavyweight processes, runtime samples or executable mutations.
Seeds and search ranges are inapplicable. The approximately 15-minute wall
budget was not instrumented; CPU time and peak RAM are unknown. Only this
leased note was written. No compiler, manifest, lockfile, shared task/index,
question, another worker output, scratch file or Git state was changed.

## Commit packet

- Exact leased/changed path:
  `notes/progress/2026-10-06-frozen-oracle-source-association-mechanism.md`.
- Baseline SHA: `d312b9445309ee4a946e887567429362ad51b7cd`.
- Oracle dependency SHA: `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none in the eight Oracle and eight current-input
  byte comparisons; integration must recheck any subsequently changed inputs.
- Review status: independently compiler-referee reviewed with no findings in
  the stated scope; no current semantic authority or established association
  theorem.
- Checks already run: cited source windows; declaration/constructor/order
  audit; conditional scalar/receiver path derivation; pinned byte comparisons;
  lease-path absence and note-local whitespace checks. No execution/build/test.
- Proposed one-line research-checkpoint commit message:
  `research: trace Oracle stored signatures to typed definition roots`.
- Shared-record deltas intentionally left for the primary/curator: optionally
  link this adjacent declaration mechanism and its receiver path discriminator;
  retain `OriginalAssocType_X` and all licensing/profile/admission gates open.

Research writing stops before submission for frozen independent review.
