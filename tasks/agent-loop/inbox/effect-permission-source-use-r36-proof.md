# R36 source callback-use proof handoff

Sprint: `EFFECT-PERMISSION-SOURCE-USE/20261031-R36`, contract revision 1,
SHA-256 `c471c7dd5d8ef2515022f4665f1ef2151577141a3f0942ea107489ecd86c5ac0`.
Assignment: `/root/effect_permission_source_use_r36_proof`; frozen handoff revision 1.
Baseline: `yulang3`, `1388bdc476e5dc0c0bb96532715c7280aa95b10e`.
Manifest: `effect-permission-source-use-20261031-r36-inputs-r1.json`,
SHA-256 `cf03b01ba1cb057972303540dd7deb881e0cfff2f8dbafd93e4912035bee37e4`.
Requested role: Lean prover; actual worker identity as above, current R36 parent
assignment received in this session. Observed model/effort: UNKNOWN.
Author: this worker only. No descendants or reviewer appointments.

Exact leases: `notes/theory/lean/YulangClosure/SourceCallbackUseR36.lean` and
this handoff. Those are the only changed paths. No compiler edits, scratch,
cache, target, build, tests, worktree, environment creation, installation,
quarantined source reads, root import edits, or Git operations.

Outcome: kernel-accepted conditional mathematics for the explicit candidate
source projection; pending fresh independent review and correspondence
adjudication. This is not self-certification or production authority.

## Sources, definitions and scope

Governing specification: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`
§1 (general composed polarity), §1.1 (approved callback/computation examples),
§1.2 (permission/inflow/residual distinction), §§3–4 (retained typed transport
results and missing construction/consumer bridge). §6 retracts the old example's
claimed scheme; no oracle or inferred output from that section is used.
Primary adjudication preserved the general callback argument type: §1.1 is an
approved example, not an exhaustive domain restriction.

Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§§1,3,5, retaining every supported original source program, lawful finite history,
actual extrusion occurrence, one joint source-scoped strategy and all Call/effect
evidence. Current correction: `notes/design/2026-10-24-birth-level-scc-intrusion.md`
§§2–6. The broader source/native targets in `docs/yulang-whole-proof-closure-ja.md`
§§1,3–4 remain open. No Simple-sub paper theorem or research draft is treated as
an axiom establishing this instance.

Pinned implementation definitions read: `local_source.rs` `LocalSourceExpr`,
`LocalSourceForm::{Lambda,Name,Apply}`, `LocalSourceResolution::Parameter`,
`LocalSourceParameter`; `program.rs` formal role construction, which classifies
outer-effects-free formals as `NameConsumption::Observe`. Name spelling does
not select a formal. Resolver identity supplies lexical binding; no separate
source-body reachability theorem is asserted.

Lean declaration namespace: `YulangClosure.SourceCallbackUseR36`.
`Pool`, `Root`, `Expression`, `Form`, and `Resolution` explicitly retain the
Lambda, exact parameter resolution and direct Apply-callee edge. `Pool.toR35`
projects the same owner-indexed arena, preserving source root and expression
coordinates, and introduces no independent row table. `lookupLambda`,
`lookupEdge`, `issue` and `authenticate` compute the selected values. The only
authenticity premise is the result of that computation, not a supplied
source-authenticity law or row equality. `issueSelected` from R35 additionally
checks formal/annotation root ownership and looks up `[TypeStep.result]`.

Supported selection: outer-effects-free direct Function with a present direct
result effect row; any argument/result value type permitted by R35's annotation
constructors. Exact parameter Name as direct Apply callee only. Global
`unambiguous` rejects the formal's inventory if any exact-formal Name has more
than one incoming Apply-callee parent. Multiple distinct direct uses are
queryable by their actual source indices; there is no arbitrary first-use
choice. `Observe` follows from the same absent outer row.

Represented: exact owner/root/Lambda/formal/Name/Apply identity, source keys and
ranges; direct resolved Parameter Names; actual callee indices; full ordered
concrete rows with multiplicity and symbolic variable lists; arbitrary R35
annotation function/tuple structure retained in the projection.
Other source forms/resolution variants are opaque rejectable payloads, with no
claim to prove the parent for a smaller source language. Grouped/indirect
callees, named root formals and computation-effect formals are outside this
selection. This Lean API proves each selected use; it does not construct or
prove a Rust list enumeration, empty-inventory equality, HIR ownership-map
validity, unique native occurrence allocation or a source-to-Rust simulation.

## Parent application and remaining premise

`authenticated_r35` applies the R36 computation directly to
`YulangClosure.SourceCallbackPermissionR35.authenticate` at `[.result]` over
`pool.toR35`. `authenticated_coordinates` derives one shared owner/root/Lambda/
formal/Name/Apply witness, exact resolution and Observe. `authenticated_result_row`
then identifies the exact Function result row, full concrete list at every Nat
index, full symbolic list, result path, and contravariant polarity. No caller
can replace the row or choose another nested path.

`foreign_parameter_name_rejected`, `nonparameter_name_rejected`,
`ambiguity_withholds`, `falsifier_rejection` and
`covariant_or_other_path_rejected` cover shadowed/foreign resolution, ambiguous
callee parents, swapped Name/Apply coordinates, foreign binding/formal/owner,
changed row position/content/multiplicity/symbols, covariant allowance and other
nested paths. Rejection of substitutions is always relative to the same
computed lookup, not equality of family sets.

First remaining local premise: relate retained native HIR extraction and Rust's
inventory enumeration to this explicit Lean arena and per-use lookup, including
source ownership/source-key agreement. Owner: primary source/correspondence
lane, with fresh reviewer comparing the frozen producer artifacts. Next runtime
premise: actual invocation/Name consumption and annotation permission emission
at the runtime consumer owners; those paths remain quarantined. No generated
constraints, propagation, runtime receipt, invocation, Grant, Catch, native
Step/History, whole-language hygiene, original A/B, soundness, principality,
progress, termination or production result follows here. The original source
joint-strategy premise in the parent §5 is unchanged.

## Frozen artifacts and dependency checks

Delivered Lean source SHA-256:
`9e15cb4982248cf90d7a11ef0c66ee7ee95ec0abe99c217d8187c31c488731de`.
Direct dependencies: R35
`f4d6c85dc12d9e5b9f58a6635c76ee49fba85ff732b5538f9924e1ab052dbcc9`;
R34 standalone source
`24ca25828e1a58f9c3246e5f50f2c73ba8ead6d2d003d05c8c2a8a3d2e85795a`.
All fourteen immutable manifest inputs (excluding the concurrently edited
`program.rs`) were freshly SHA-256 checked and MATCHED. This includes design,
HIR/syntax, toolchain/lakefile, R31–R35, R35 review and R35 outcome.
Rust producer reported frozen source
`1a6f27609bc510d905b85be6f33a43b87bb95e1224794fe0fdd01688381e89b2`
and handoff r2
`df72f3c643b1267f4d9ff40e737890d45fe4059f4c9e5b75a7c246bb5d480ec5`;
these are correspondence inputs, not a Rust compilation/runtime receipt.
This handoff's final byte hash is returned separately after freeze.

## Verification and resources

Read the skill's `references/sources.md` and `references/execution.md`, pinned
toolchain, lakefile, empty package manifest and relevant project README.
`elan which lake` exited 0, resolved the existing pinned native Lake, and emitted
its failed-latest-query warning while retaining the existing 4.35.0 installation.
No unresolved proxy was invoked and no installation/dependency change occurred.
Actual read-only version commands:

```text
bwrap --ro-bind / / --dev /dev --proc /proc /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --version
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
bwrap --ro-bind / / --dev /dev --proc /proc /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean --version
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

Both version commands exited 0. The standard skill checker would build and is
inapplicable under this packet's no-build constraint. The approved stdin route
reads the byte-pinned complete standalone R34, appends R35 and R36 with only
their first import lines removed, and appends every theorem's fully qualified
`#check @...` and `#print axioms ...`. One Lean process checks their full source
against the pinned Std library; no local import artifact is generated or assumed
fresh. No Lake/default/public-root build or original import integration is claimed.

Final attempt 5: exit 0, no diagnostics/warnings, thirteen printed theorem types
and complete transitive axiom results, preserved verbatim below. Seven theorems
use `[propext]`; six use `[propext, Quot.sound]`; none uses `Classical.choice`,
`sorryAx`, project axioms or bypasses. Source search over complete R34/R35/R36
for holes/project axioms/native evaluation/kernel bypass had no matches (rg
exit 1). The theorem declarations and final printed types are mathematical
evidence for this candidate source model only; independent review is pending.

All actual failed diagnostics remain below: attempt 1 exposed case-equality
orientations and missing existential/index types; attempt 2 exposed Bool-guard
conjunction simplification; attempt 4 exposed an insertion into the middle of
a proof branch. Attempts 3 and 5 passed. Failure-time Lean-generated `sorryAx`
outputs are failed elaboration evidence and are not delivered proofs.

Five measured Lean subprocess durations: 12.034310, 6.875978, 6.540259,
8.178845 and 8.360617 seconds; total 41.990009 seconds. Each was bounded by
90 seconds, `-j1 -M1024`, and read-only bwrap. Peak memory was not measured.
First explicit wall clock: 2026-10-30 18:12:22 UTC. Full dispatch-to-finish
elapsed is UNKNOWN because startup was not clocked; no invented elapsed receipt.
Lean allocation: 1,600 seconds. No persistent verification process or generated
output remains. Frozen code awaits independent review/integration by Luna.

Worker state: STOPPED after this handoff freeze; writes stopped to both leased
paths. No descendants, unresolved child leases, scratch or generated outputs.

## Actual construction diagnostics

### Attempt 1

Command: `bwrap --ro-bind / / --dev /dev --proc /proc /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean --stdin -j1 -M1024`

Exit: 1; measured subprocess seconds: 12.034310.

```text
<stdin>:2273:23: error: Application type mismatch: The argument
  hr
has type
  (pool.roots owner.hirOwner)[ri]? = some root
but is expected to have type
  some root =
    some { root := root, expression := expression, formal := formal, body := body, annotation := annotation }.root
in the application
  And.intro hr
<stdin>:2271:24: warning: This simp argument is unused:
  hr

Hint: Omit it from the simp argument list.
  [apply] simp [he, hf, ha, ht, hu] at found

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:2271:28: warning: This simp argument is unused:
  he

Hint: Omit it from the simp argument list.
  [apply] simp [hr, hf, ha, ht, hu] at found

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:2271:32: warning: This simp argument is unused:
  hf

Hint: Omit it from the simp argument list.
  [apply] simp [hr, he, ha, ht, hu] at found

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:2271:36: warning: This simp argument is unused:
  ha

Hint: Omit it from the simp argument list.
  [apply] simp [hr, he, hf, ht, hu] at found

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:2271:40: warning: This simp argument is unused:
  ht

Hint: Omit it from the simp argument list.
  [apply] simp [hr, he, hf, ha, hu] at found

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:2313:21: error: Application type mismatch: The argument
  ha
has type
  root.expressions[ai]? = some application
but is expected to have type
  some application =
    some
      { nameIndex := callee, name := name, applyIndex := ai, application := application,
          argument := argument }.application
in the application
  And.intro ha
<stdin>:2337:36: error: Application type mismatch: The argument
  hl
has type
  lookupLambda pool owner ri li = some l
but is expected to have type
  some l = some l
in the application
  And.intro hl
<stdin>:2357:46: error(lean.invalidField): Invalid field notation: Type of
  l
is not known; cannot resolve field `root`

Hint: Consider replacing the field projection with a call to one of the following:
  • `IO.FS.DirEntry.root`
  • `CallbackHygieneCorrespondence.Site.root`
  • `Binding.root`
  • `SelectedFormal.root`
  • `SelectedLambda.root`
<stdin>:2358:6: error(lean.invalidField): Invalid field notation: Type of
  l
is not known; cannot resolve field `root`

Hint: Consider replacing the field projection with a call to one of the following:
  • `IO.FS.DirEntry.root`
  • `CallbackHygieneCorrespondence.Site.root`
  • `Binding.root`
  • `SelectedFormal.root`
  • `SelectedLambda.root`
<stdin>:2358:37: error(lean.invalidField): Invalid field notation: Type of
  l
is not known; cannot resolve field `expression`

Hint: Consider replacing the field projection with a call to one of the following:
  • `RootId.expression`
  • `SelectedLambda.expression`
<stdin>:2359:6: error(lean.invalidField): Invalid field notation: Type of
  l
is not known; cannot resolve field `expression`

Hint: Consider replacing the field projection with a call to one of the following:
  • `RootId.expression`
  • `SelectedLambda.expression`
<stdin>:2359:26: error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.lambda` could not be determined

Hint: Using one of these would be unambiguous:
  [apply] `SourceCallbackPermissionR35.Form.lambda`
  [apply] `Form.lambda`
<stdin>:2360:6: error(lean.invalidField): Invalid field notation: Type of
  l
is not known; cannot resolve field `formal`

Hint: Consider replacing the field projection with a call to one of the following:
  • `CallbackHygieneCorrespondence.Annotation.formal`
  • `CallbackHygieneCorrespondence.Kind.formal`
  • `CallbackHygieneCorrespondence.NameRead.formal`
  • `CallbackHygieneCorrespondence.Permission.formal`
  • `CallbackHygieneCorrespondence.Receipt.formal`
  • `Binding.formal`
  • `SelectedFormal.formal`
  • `SelectedLambda.formal`
<stdin>:2360:33: error(lean.invalidField): Invalid field notation: Type of
  l
is not known; cannot resolve field `annotation`

Hint: Consider replacing the field projection with a call to one of the following:
  • `CallbackHygieneCorrespondence.Permission.annotation`
  • `CallbackHygieneCorrespondence.Step.annotation`
  • `Parameter.annotation`
  • `SelectedFormal.annotation`
  • `SelectedLambda.annotation`
<stdin>:2361:6: error(lean.invalidField): Invalid field notation: Type of
  l
is not known; cannot resolve field `root`

Hint: Consider replacing the field projection with a call to one of the following:
  • `IO.FS.DirEntry.root`
  • `CallbackHygieneCorrespondence.Site.root`
  • `Binding.root`
  • `SelectedFormal.root`
  • `SelectedLambda.root`
<stdin>:2361:37: error(lean.invalidField): Invalid field notation: Type of
  edge
is not known; cannot resolve field `application`

Hint: Consider replacing the field projection with a call to one of the following:
  • `Edge.application`
  • `Witness.application`
<stdin>:2362:6: error(lean.invalidField): Invalid field notation: Type of
  edge
is not known; cannot resolve field `application`

Hint: Consider replacing the field projection with a call to one of the following:
  • `Edge.application`
  • `Witness.application`
<stdin>:2362:30: error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.apply` could not be determined

Hint: Using one of these would be unambiguous:
  [apply] `WellFounded.apply`
  [apply] `Lean.Order.PredTrans.apply`
  [apply] `Lean.Parser.Tactic.apply`
  [apply] `Std.Do.PredTrans.apply`
  [apply] `Form.apply`
  [apply] `Float.Model.UnpackedFloat.Sign.apply`
<stdin>:2363:6: error(lean.invalidField): Invalid field notation: Type of
  l
is not known; cannot resolve field `root`

Hint: Consider replacing the field projection with a call to one of the following:
  • `IO.FS.DirEntry.root`
  • `CallbackHygieneCorrespondence.Site.root`
  • `Binding.root`
  • `SelectedFormal.root`
  • `SelectedLambda.root`
<stdin>:2363:25: error(lean.invalidField): Invalid field notation: Type of
  edge
is not known; cannot resolve field `nameIndex`

Hint: Consider replacing the field projection with a call to one of the following:
  • `Edge.nameIndex`
  • `Witness.nameIndex`
<stdin>:2363:49: error(lean.invalidField): Invalid field notation: Type of
  edge
is not known; cannot resolve field `name`

Hint: Consider replacing the field projection with a call to one of the following:
  • `Lean.MacroScopesView.name`
  • `Lean.Try.Config.name`
  • `Std.Net.InterfaceAddress.name`
  • `Std.Time.TimeZone.name`
  • `Edge.name`
  • `Form.name`
  • `Witness.name`
  • `Std.Async.System.OSInfo.name`
  • `Std.Http.URI.Host.name`
  • `Std.Time.TimeZone.DaylightSavingRule.name`
<stdin>:2364:6: error(lean.invalidField): Invalid field notation: Type of
  edge
is not known; cannot resolve field `name`

Hint: Consider replacing the field projection with a call to one of the following:
  • `Lean.MacroScopesView.name`
  • `Lean.Try.Config.name`
  • `Std.Net.InterfaceAddress.name`
  • `Std.Time.TimeZone.name`
  • `Edge.name`
  • `Form.name`
  • `Witness.name`
  • `Std.Async.System.OSInfo.name`
  • `Std.Http.URI.Host.name`
  • `Std.Time.TimeZone.DaylightSavingRule.name`
<stdin>:2364:23: error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.name` could not be determined

Hint: Using one of these would be unambiguous:
  [apply] `Lean.MacroScopesView.name`
  [apply] `Lean.Try.Config.name`
  [apply] `Std.Net.InterfaceAddress.name`
  [apply] `Std.Time.TimeZone.name`
  [apply] `Edge.name`
  [apply] `Form.name`
  [apply] `Witness.name`
  [apply] `Std.Async.System.OSInfo.name`
  [apply] `Std.Http.URI.Host.name`
  [apply] `Std.Time.TimeZone.DaylightSavingRule.name`
<stdin>:2365:18: error(lean.invalidField): Invalid field notation: Type of
  l
is not known; cannot resolve field `root`

Hint: Consider replacing the field projection with a call to one of the following:
  • `IO.FS.DirEntry.root`
  • `CallbackHygieneCorrespondence.Site.root`
  • `Binding.root`
  • `SelectedFormal.root`
  • `SelectedLambda.root`
<stdin>:2365:25: error(lean.invalidField): Invalid field notation: Type of
  l
is not known; cannot resolve field `formal`

Hint: Consider replacing the field projection with a call to one of the following:
  • `CallbackHygieneCorrespondence.Annotation.formal`
  • `CallbackHygieneCorrespondence.Kind.formal`
  • `CallbackHygieneCorrespondence.NameRead.formal`
  • `CallbackHygieneCorrespondence.Permission.formal`
  • `CallbackHygieneCorrespondence.Receipt.formal`
  • `Binding.formal`
  • `SelectedFormal.formal`
  • `SelectedLambda.formal`
<stdin>:2366:15: error(lean.invalidField): Invalid field notation: Type of
  edge
is not known; cannot resolve field `name`

Hint: Consider replacing the field projection with a call to one of the following:
  • `Lean.MacroScopesView.name`
  • `Lean.Try.Config.name`
  • `Std.Net.InterfaceAddress.name`
  • `Std.Time.TimeZone.name`
  • `Edge.name`
  • `Form.name`
  • `Witness.name`
  • `Std.Async.System.OSInfo.name`
  • `Std.Http.URI.Host.name`
  • `Std.Time.TimeZone.DaylightSavingRule.name`
<stdin>:2366:48: error(lean.invalidField): Invalid field notation: Type of
  edge
is not known; cannot resolve field `application`

Hint: Consider replacing the field projection with a call to one of the following:
  • `Edge.application`
  • `Witness.application`
<stdin>:2367:20: error(lean.invalidField): Invalid field notation: Type of
  edge
is not known; cannot resolve field `nameIndex`

Hint: Consider replacing the field projection with a call to one of the following:
  • `Edge.nameIndex`
  • `Witness.nameIndex`
<stdin>:2368:25: error(lean.invalidField): Invalid field notation: Type of
  l
is not known; cannot resolve field `formal`

Hint: Consider replacing the field projection with a call to one of the following:
  • `CallbackHygieneCorrespondence.Annotation.formal`
  • `CallbackHygieneCorrespondence.Kind.formal`
  • `CallbackHygieneCorrespondence.NameRead.formal`
  • `CallbackHygieneCorrespondence.Permission.formal`
  • `CallbackHygieneCorrespondence.Receipt.formal`
  • `Binding.formal`
  • `SelectedFormal.formal`
  • `SelectedLambda.formal`
<stdin>:2368:69: error(lean.invalidField): Invalid field notation: Type of
  l
is not known; cannot resolve field `formal`

Hint: Consider replacing the field projection with a call to one of the following:
  • `CallbackHygieneCorrespondence.Annotation.formal`
  • `CallbackHygieneCorrespondence.Kind.formal`
  • `CallbackHygieneCorrespondence.NameRead.formal`
  • `CallbackHygieneCorrespondence.Permission.formal`
  • `CallbackHygieneCorrespondence.Receipt.formal`
  • `Binding.formal`
  • `SelectedFormal.formal`
  • `SelectedLambda.formal`
<stdin>:2369:34: error(lean.invalidField): Invalid field notation: Type of
  l
is not known; cannot resolve field `root`

Hint: Consider replacing the field projection with a call to one of the following:
  • `IO.FS.DirEntry.root`
  • `CallbackHygieneCorrespondence.Site.root`
  • `Binding.root`
  • `SelectedFormal.root`
  • `SelectedLambda.root`
<stdin>:2370:46: error(lean.invalidField): Invalid field notation: Type of
  l
is not known; cannot resolve field `expression`

Hint: Consider replacing the field projection with a call to one of the following:
  • `RootId.expression`
  • `SelectedLambda.expression`
<stdin>:2393:52: error: typeclass instance problem is stuck
  GetElem? (List (SourceEffectId Module Parse Green)) (?m.185 l argument result row)
    (?m.186 l argument result row index) (?m.189 l argument result row index)

Note: Lean will not try to resolve this typeclass instance problem because the second type argument to `GetElem?` contains metavariables. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
<stdin>:2447:4: error(lean.unknownIdentifier): Unknown identifier `authenticated_result_row`
<stdin>:2446:9: error: Tactic `rcases` failed: `x✝ : ?m.56` is not an inductive datatype
@YulangClosure.SourceCallbackUseR36.lookupLambda_origin : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li : Nat)
  (l : YulangClosure.SourceCallbackUseR36.SelectedLambda Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.lookupLambda pool owner ri li = some l →
    (pool.roots owner.hirOwner)[ri]? = some l.root ∧
      l.root.expressions[li]? = some l.expression ∧
        l.expression.form = YulangClosure.SourceCallbackUseR36.Form.lambda l.formal l.body ∧
          l.formal.annotation = some l.annotation ∧
            (∃ argument result,
                l.annotation.ty =
                  YulangClosure.SourceCallbackPermissionR35.AnnotationType.mk none
                    (YulangClosure.SourceCallbackPermissionR35.AnnotationValue.function argument result)) ∧
              YulangClosure.SourceCallbackUseR36.unambiguous l.root l.formal.id = true
'YulangClosure.SourceCallbackUseR36.lookupLambda_origin' depends on axioms: [propext, sorryAx]
@YulangClosure.SourceCallbackUseR36.lookupLambda_r35 : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li : Nat)
  (l : YulangClosure.SourceCallbackUseR36.SelectedLambda Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.lookupLambda pool owner ri li = some l →
    YulangClosure.SourceCallbackPermissionR35.selectFormal pool.toR35 owner ri li = some l.selection
'YulangClosure.SourceCallbackUseR36.lookupLambda_r35' depends on axioms: [propext, sorryAx]
@YulangClosure.SourceCallbackUseR36.lookupEdge_origin : ∀ {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (root : YulangClosure.SourceCallbackUseR36.Root Artifact Definition Module Parse Green)
  (formal : YulangClosure.SourceCallbackPermissionR35.ParameterId Artifact Definition Module Parse Green) (ai : Nat)
  (edge : YulangClosure.SourceCallbackUseR36.Edge Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.lookupEdge root formal ai = some edge →
    root.expressions[ai]? = some edge.application ∧
      edge.applyIndex = ai ∧
        edge.application.form = YulangClosure.SourceCallbackUseR36.Form.apply edge.nameIndex edge.argument ∧
          root.expressions[edge.nameIndex]? = some edge.name ∧
            edge.name.form =
              YulangClosure.SourceCallbackUseR36.Form.name
                (YulangClosure.SourceCallbackUseR36.Resolution.parameter formal)
'YulangClosure.SourceCallbackUseR36.lookupEdge_origin' depends on axioms: [propext, sorryAx]
@YulangClosure.SourceCallbackUseR36.source_origin : ∀ {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory}
  {Artifact Definition Module Parse Green : Type} [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition]
  [inst_2 : DecidableEq Module] [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (w : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai w →
    ∃ l edge permission,
      YulangClosure.SourceCallbackUseR36.lookupLambda pool owner ri li = some l ∧
        YulangClosure.SourceCallbackUseR36.lookupEdge l.root l.formal.id ai = some edge ∧
          YulangClosure.SourceCallbackPermissionR35.issueSelected owner l.selection
                [YulangClosure.SourceCallbackPermissionR35.TypeStep.result] =
              some permission ∧
            w = YulangClosure.SourceCallbackUseR36.assemble l edge permission
'YulangClosure.SourceCallbackUseR36.source_origin' depends on axioms: [propext, sorryAx, Quot.sound]
@YulangClosure.SourceCallbackUseR36.authenticated_r35 : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (w : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai w →
    YulangClosure.SourceCallbackPermissionR35.authenticate pool.toR35 owner ri li
      [YulangClosure.SourceCallbackPermissionR35.TypeStep.result] w.permission
'YulangClosure.SourceCallbackUseR36.authenticated_r35' depends on axioms: [propext, sorryAx, Quot.sound]
@YulangClosure.SourceCallbackUseR36.authenticated_coordinates : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (w : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green)
  (authentic : YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai w),
  ∃ l edge,
    (pool.roots owner.hirOwner)[ri]? = some sorry ∧
      (sorry pool owner ri li ai w authentic l edge)[li]? = some (sorry pool owner ri li ai w authentic l edge) ∧
        sorry pool owner ri li ai w authentic l edge = sorry pool owner ri li ai w authentic l edge ∧
          sorry pool owner ri li ai w authentic l edge = some (sorry pool owner ri li ai w authentic l edge) ∧
            (sorry pool owner ri li ai w authentic l edge)[ai]? = some (sorry pool owner ri li ai w authentic l edge) ∧
              sorry pool owner ri li ai w authentic l edge = sorry pool owner ri li ai w authentic l edge ∧
                (sorry pool owner ri li ai w authentic l edge)[sorry pool owner ri li ai w authentic l edge]? =
                    some (sorry pool owner ri li ai w authentic l edge) ∧
                  sorry pool owner ri li ai w authentic l edge = sorry pool owner ri li ai w authentic l edge ∧
                    YulangClosure.SourceCallbackUseR36.unambiguous (sorry pool owner ri li ai w authentic l edge)
                          (sorry pool owner ri li ai w authentic l edge) =
                        true ∧
                      w.name = sorry ∧
                        w.application = sorry ∧
                          w.nameIndex = sorry ∧
                            w.applyIndex = ai ∧
                              w.resolvedFormal = sorry ∧
                                w.permission.binding.formal = sorry ∧
                                  w.permission.binding.root = sorry ∧
                                    w.permission.binding.lambdaOccurrence = sorry ∧
                                      w.permission.binding.snapshotOwner = owner.hirOwner ∧
                                        w.consumption = YulangClosure.SourceCallbackUseR36.Consumption.observe
'YulangClosure.SourceCallbackUseR36.authenticated_coordinates' depends on axioms: [propext, sorryAx, Quot.sound]
<stdin>:2472:8: error(lean.unknownIdentifier): Unknown identifier `YulangClosure.SourceCallbackUseR36.authenticated_result_row`
<stdin>:2473:14: error(lean.unknownIdentifier): Unknown constant `YulangClosure.SourceCallbackUseR36.authenticated_result_row`
@YulangClosure.SourceCallbackUseR36.reject_changed_projection : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green] {α : Type}
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (issued candidate : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.issue pool owner ri li ai = some issued →
    ∀ (projection : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green → α),
      projection candidate ≠ projection issued →
        ¬YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai candidate
'YulangClosure.SourceCallbackUseR36.reject_changed_projection' depends on axioms: [propext]
@YulangClosure.SourceCallbackUseR36.falsifier_rejection : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (issued candidate : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.issue pool owner ri li ai = some issued →
    candidate.permission.binding ≠ issued.permission.binding ∨
        candidate.resolvedFormal ≠ issued.resolvedFormal ∨
          candidate.name ≠ issued.name ∨
            candidate.application ≠ issued.application ∨
              candidate.nameIndex ≠ issued.nameIndex ∨
                candidate.applyIndex ≠ issued.applyIndex ∨
                  candidate.permission.row.concrete ≠ issued.permission.row.concrete ∨
                    candidate.permission.row.variables ≠ issued.permission.row.variables ∨
                      candidate.permission.row.position ≠ issued.permission.row.position ∨
                        candidate.consumption ≠ issued.consumption →
      ¬YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai candidate
'YulangClosure.SourceCallbackUseR36.falsifier_rejection' depends on axioms: [propext]
@YulangClosure.SourceCallbackUseR36.covariant_or_other_path_rejected : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (candidate : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  candidate.permission.binding.rowContravariant = false ∨
      candidate.permission.binding.rowPath ≠ [YulangClosure.SourceCallbackPermissionR35.TypeStep.result] →
    ¬YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai candidate
'YulangClosure.SourceCallbackUseR36.covariant_or_other_path_rejected' depends on axioms: [propext, sorryAx]
```

### Attempt 2

Command: `bwrap --ro-bind / / --dev /dev --proc /proc /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean --stdin -j1 -M1024`

Exit: 1; measured subprocess seconds: 6.875978.

```text
<stdin>:2273:18: error: Tactic `contradiction` failed

case false
history : AllocationHistory
Artifact Definition Module Parse Green : Type
inst✝⁴ : DecidableEq Artifact
inst✝³ : DecidableEq Definition
inst✝² : DecidableEq Module
inst✝¹ : DecidableEq Parse
inst✝ : DecidableEq Green
pool : Pool history Artifact Definition Module Parse Green
owner : RuntimeOwner history
ri li : Nat
l : SelectedLambda Artifact Definition Module Parse Green
root : Root Artifact Definition Module Parse Green
hr : (pool.roots owner.hirOwner)[ri]? = some root
expression : Expression Artifact Definition Module Parse Green
he : root.expressions[li]? = some expression
formal : Parameter Artifact Definition Module Parse Green
body : Nat
hf : expression.form = Form.lambda formal body
annotation : SourceAnnotation Artifact Definition Module Parse Green
ha : formal.annotation = some annotation
argument result : AnnotationType Module Parse Green
ht : annotation.ty = AnnotationType.mk none (AnnotationValue.function argument result)
hu : unambiguous root formal.id = false
found : False ∧ { root := root, expression := expression, formal := formal, body := body, annotation := annotation } = l
⊢ some root = some l.root ∧
    l.root.expressions[li]? = some l.expression ∧
      l.expression.form = Form.lambda l.formal l.body ∧
        l.formal.annotation = some l.annotation ∧
          (∃ argument result, l.annotation.ty = AnnotationType.mk none (AnnotationValue.function argument result)) ∧
            unambiguous l.root l.formal.id = true
<stdin>:2274:16: error: Tactic `subst` failed: did not find equation for eliminating 'l'

case true
history : AllocationHistory
Artifact Definition Module Parse Green : Type
inst✝⁴ : DecidableEq Artifact
inst✝³ : DecidableEq Definition
inst✝² : DecidableEq Module
inst✝¹ : DecidableEq Parse
inst✝ : DecidableEq Green
pool : Pool history Artifact Definition Module Parse Green
owner : RuntimeOwner history
ri li : Nat
l : SelectedLambda Artifact Definition Module Parse Green
root : Root Artifact Definition Module Parse Green
hr : (pool.roots owner.hirOwner)[ri]? = some root
expression : Expression Artifact Definition Module Parse Green
he : root.expressions[li]? = some expression
formal : Parameter Artifact Definition Module Parse Green
body : Nat
hf : expression.form = Form.lambda formal body
annotation : SourceAnnotation Artifact Definition Module Parse Green
ha : formal.annotation = some annotation
argument result : AnnotationType Module Parse Green
ht : annotation.ty = AnnotationType.mk none (AnnotationValue.function argument result)
hu : unambiguous root formal.id = true
found : True ∧ { root := root, expression := expression, formal := formal, body := body, annotation := annotation } = l
⊢ some root = some l.root ∧
    l.root.expressions[li]? = some l.expression ∧
      l.expression.form = Form.lambda l.formal l.body ∧
        l.formal.annotation = some l.annotation ∧
          (∃ argument result, l.annotation.ty = AnnotationType.mk none (AnnotationValue.function argument result)) ∧
            unambiguous l.root l.formal.id = true
<stdin>:2271:29: warning: This simp argument is unused:
  Option.bind_some

Hint: Omit it from the simp argument list.
  [apply] simp only [hf, ha, ht, hu, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at found

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:2271:47: warning: This simp argument is unused:
  hf

Hint: Omit it from the simp argument list.
  [apply] simp only [Option.bind_some, ha, ht, hu, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at found

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:2271:51: warning: This simp argument is unused:
  ha

Hint: Omit it from the simp argument list.
  [apply] simp only [Option.bind_some, hf, ht, hu, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at found

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:2271:55: warning: This simp argument is unused:
  ht

Hint: Omit it from the simp argument list.
  [apply] simp only [Option.bind_some, hf, ha, hu, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at found

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:2272:20: warning: This simp argument is unused:
  ↓reduceIte

Hint: Omit it from the simp argument list.
  [apply] simp only [Option.bind_some, hf, ha, ht, hu, Bool.false_eq_true, Option.some.injEq] at found

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:2272:32: warning: This simp argument is unused:
  Option.some.injEq

Hint: Omit it from the simp argument list.
  [apply] simp only [Option.bind_some, hf, ha, ht, hu, Bool.false_eq_true, ↓reduceIte] at found

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
@YulangClosure.SourceCallbackUseR36.lookupLambda_origin : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li : Nat)
  (l : YulangClosure.SourceCallbackUseR36.SelectedLambda Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.lookupLambda pool owner ri li = some l →
    (pool.roots owner.hirOwner)[ri]? = some l.root ∧
      l.root.expressions[li]? = some l.expression ∧
        l.expression.form = YulangClosure.SourceCallbackUseR36.Form.lambda l.formal l.body ∧
          l.formal.annotation = some l.annotation ∧
            (∃ argument result,
                l.annotation.ty =
                  YulangClosure.SourceCallbackPermissionR35.AnnotationType.mk none
                    (YulangClosure.SourceCallbackPermissionR35.AnnotationValue.function argument result)) ∧
              YulangClosure.SourceCallbackUseR36.unambiguous l.root l.formal.id = true
'YulangClosure.SourceCallbackUseR36.lookupLambda_origin' depends on axioms: [propext, sorryAx]
@YulangClosure.SourceCallbackUseR36.lookupLambda_r35 : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li : Nat)
  (l : YulangClosure.SourceCallbackUseR36.SelectedLambda Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.lookupLambda pool owner ri li = some l →
    YulangClosure.SourceCallbackPermissionR35.selectFormal pool.toR35 owner ri li = some l.selection
'YulangClosure.SourceCallbackUseR36.lookupLambda_r35' depends on axioms: [propext, sorryAx]
@YulangClosure.SourceCallbackUseR36.lookupEdge_origin : ∀ {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (root : YulangClosure.SourceCallbackUseR36.Root Artifact Definition Module Parse Green)
  (formal : YulangClosure.SourceCallbackPermissionR35.ParameterId Artifact Definition Module Parse Green) (ai : Nat)
  (edge : YulangClosure.SourceCallbackUseR36.Edge Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.lookupEdge root formal ai = some edge →
    root.expressions[ai]? = some edge.application ∧
      edge.applyIndex = ai ∧
        edge.application.form = YulangClosure.SourceCallbackUseR36.Form.apply edge.nameIndex edge.argument ∧
          root.expressions[edge.nameIndex]? = some edge.name ∧
            edge.name.form =
              YulangClosure.SourceCallbackUseR36.Form.name
                (YulangClosure.SourceCallbackUseR36.Resolution.parameter formal)
'YulangClosure.SourceCallbackUseR36.lookupEdge_origin' depends on axioms: [propext]
@YulangClosure.SourceCallbackUseR36.source_origin : ∀ {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory}
  {Artifact Definition Module Parse Green : Type} [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition]
  [inst_2 : DecidableEq Module] [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (w : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai w →
    ∃ l edge permission,
      YulangClosure.SourceCallbackUseR36.lookupLambda pool owner ri li = some l ∧
        YulangClosure.SourceCallbackUseR36.lookupEdge l.root l.formal.id ai = some edge ∧
          YulangClosure.SourceCallbackPermissionR35.issueSelected owner l.selection
                [YulangClosure.SourceCallbackPermissionR35.TypeStep.result] =
              some permission ∧
            w = YulangClosure.SourceCallbackUseR36.assemble l edge permission
'YulangClosure.SourceCallbackUseR36.source_origin' depends on axioms: [propext, Quot.sound]
@YulangClosure.SourceCallbackUseR36.authenticated_r35 : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (w : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai w →
    YulangClosure.SourceCallbackPermissionR35.authenticate pool.toR35 owner ri li
      [YulangClosure.SourceCallbackPermissionR35.TypeStep.result] w.permission
'YulangClosure.SourceCallbackUseR36.authenticated_r35' depends on axioms: [propext, sorryAx, Quot.sound]
@YulangClosure.SourceCallbackUseR36.authenticated_coordinates : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (w : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai w →
    ∃ l edge,
      (pool.roots owner.hirOwner)[ri]? = some l.root ∧
        l.root.expressions[li]? = some l.expression ∧
          l.expression.form = YulangClosure.SourceCallbackUseR36.Form.lambda l.formal l.body ∧
            l.formal.annotation = some l.annotation ∧
              l.root.expressions[ai]? = some edge.application ∧
                edge.application.form = YulangClosure.SourceCallbackUseR36.Form.apply edge.nameIndex edge.argument ∧
                  l.root.expressions[edge.nameIndex]? = some edge.name ∧
                    edge.name.form =
                        YulangClosure.SourceCallbackUseR36.Form.name
                          (YulangClosure.SourceCallbackUseR36.Resolution.parameter l.formal.id) ∧
                      YulangClosure.SourceCallbackUseR36.unambiguous l.root l.formal.id = true ∧
                        w.name = edge.name.site ∧
                          w.application = edge.application.site ∧
                            w.nameIndex = edge.nameIndex ∧
                              w.applyIndex = ai ∧
                                w.resolvedFormal = l.formal.id ∧
                                  w.permission.binding.formal = l.formal.id ∧
                                    w.permission.binding.root = l.root.id ∧
                                      w.permission.binding.lambdaOccurrence = l.expression.occurrence ∧
                                        w.permission.binding.snapshotOwner = owner.hirOwner ∧
                                          w.consumption = YulangClosure.SourceCallbackUseR36.Consumption.observe
'YulangClosure.SourceCallbackUseR36.authenticated_coordinates' depends on axioms: [propext, sorryAx, Quot.sound]
@YulangClosure.SourceCallbackUseR36.authenticated_result_row : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (w : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai w →
    ∃ l argument result row,
      YulangClosure.SourceCallbackUseR36.lookupLambda pool owner ri li = some l ∧
        l.annotation.ty =
            YulangClosure.SourceCallbackPermissionR35.AnnotationType.mk none
              (YulangClosure.SourceCallbackPermissionR35.AnnotationValue.function argument result) ∧
          YulangClosure.SourceCallbackPermissionR35.selectRow result [] = some row ∧
            w.permission.row = row ∧
              (∀ (index : Nat), w.permission.row.concrete[index]? = row.concrete[index]?) ∧
                w.permission.row.variables = row.variables ∧
                  w.permission.binding.rowPath = [YulangClosure.SourceCallbackPermissionR35.TypeStep.result] ∧
                    w.permission.binding.rowContravariant = true
'YulangClosure.SourceCallbackUseR36.authenticated_result_row' depends on axioms: [propext, sorryAx, Quot.sound]
@YulangClosure.SourceCallbackUseR36.reject_changed_projection : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green] {α : Type}
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (issued candidate : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.issue pool owner ri li ai = some issued →
    ∀ (projection : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green → α),
      projection candidate ≠ projection issued →
        ¬YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai candidate
'YulangClosure.SourceCallbackUseR36.reject_changed_projection' depends on axioms: [propext]
@YulangClosure.SourceCallbackUseR36.falsifier_rejection : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (issued candidate : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.issue pool owner ri li ai = some issued →
    candidate.permission.binding ≠ issued.permission.binding ∨
        candidate.resolvedFormal ≠ issued.resolvedFormal ∨
          candidate.name ≠ issued.name ∨
            candidate.application ≠ issued.application ∨
              candidate.nameIndex ≠ issued.nameIndex ∨
                candidate.applyIndex ≠ issued.applyIndex ∨
                  candidate.permission.row.concrete ≠ issued.permission.row.concrete ∨
                    candidate.permission.row.variables ≠ issued.permission.row.variables ∨
                      candidate.permission.row.position ≠ issued.permission.row.position ∨
                        candidate.consumption ≠ issued.consumption →
      ¬YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai candidate
'YulangClosure.SourceCallbackUseR36.falsifier_rejection' depends on axioms: [propext]
@YulangClosure.SourceCallbackUseR36.covariant_or_other_path_rejected : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (candidate : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  candidate.permission.binding.rowContravariant = false ∨
      candidate.permission.binding.rowPath ≠ [YulangClosure.SourceCallbackPermissionR35.TypeStep.result] →
    ¬YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai candidate
'YulangClosure.SourceCallbackUseR36.covariant_or_other_path_rejected' depends on axioms: [propext, sorryAx, Quot.sound]
```

### Attempt 3

Command: `bwrap --ro-bind / / --dev /dev --proc /proc /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean --stdin -j1 -M1024`

Exit: 0; measured subprocess seconds: 6.540259.

```text
@YulangClosure.SourceCallbackUseR36.lookupLambda_origin : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li : Nat)
  (l : YulangClosure.SourceCallbackUseR36.SelectedLambda Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.lookupLambda pool owner ri li = some l →
    (pool.roots owner.hirOwner)[ri]? = some l.root ∧
      l.root.expressions[li]? = some l.expression ∧
        l.expression.form = YulangClosure.SourceCallbackUseR36.Form.lambda l.formal l.body ∧
          l.formal.annotation = some l.annotation ∧
            (∃ argument result,
                l.annotation.ty =
                  YulangClosure.SourceCallbackPermissionR35.AnnotationType.mk none
                    (YulangClosure.SourceCallbackPermissionR35.AnnotationValue.function argument result)) ∧
              YulangClosure.SourceCallbackUseR36.unambiguous l.root l.formal.id = true
'YulangClosure.SourceCallbackUseR36.lookupLambda_origin' depends on axioms: [propext]
@YulangClosure.SourceCallbackUseR36.lookupLambda_r35 : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li : Nat)
  (l : YulangClosure.SourceCallbackUseR36.SelectedLambda Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.lookupLambda pool owner ri li = some l →
    YulangClosure.SourceCallbackPermissionR35.selectFormal pool.toR35 owner ri li = some l.selection
'YulangClosure.SourceCallbackUseR36.lookupLambda_r35' depends on axioms: [propext]
@YulangClosure.SourceCallbackUseR36.lookupEdge_origin : ∀ {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (root : YulangClosure.SourceCallbackUseR36.Root Artifact Definition Module Parse Green)
  (formal : YulangClosure.SourceCallbackPermissionR35.ParameterId Artifact Definition Module Parse Green) (ai : Nat)
  (edge : YulangClosure.SourceCallbackUseR36.Edge Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.lookupEdge root formal ai = some edge →
    root.expressions[ai]? = some edge.application ∧
      edge.applyIndex = ai ∧
        edge.application.form = YulangClosure.SourceCallbackUseR36.Form.apply edge.nameIndex edge.argument ∧
          root.expressions[edge.nameIndex]? = some edge.name ∧
            edge.name.form =
              YulangClosure.SourceCallbackUseR36.Form.name
                (YulangClosure.SourceCallbackUseR36.Resolution.parameter formal)
'YulangClosure.SourceCallbackUseR36.lookupEdge_origin' depends on axioms: [propext]
@YulangClosure.SourceCallbackUseR36.source_origin : ∀ {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory}
  {Artifact Definition Module Parse Green : Type} [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition]
  [inst_2 : DecidableEq Module] [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (w : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai w →
    ∃ l edge permission,
      YulangClosure.SourceCallbackUseR36.lookupLambda pool owner ri li = some l ∧
        YulangClosure.SourceCallbackUseR36.lookupEdge l.root l.formal.id ai = some edge ∧
          YulangClosure.SourceCallbackPermissionR35.issueSelected owner l.selection
                [YulangClosure.SourceCallbackPermissionR35.TypeStep.result] =
              some permission ∧
            w = YulangClosure.SourceCallbackUseR36.assemble l edge permission
'YulangClosure.SourceCallbackUseR36.source_origin' depends on axioms: [propext, Quot.sound]
@YulangClosure.SourceCallbackUseR36.authenticated_r35 : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (w : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai w →
    YulangClosure.SourceCallbackPermissionR35.authenticate pool.toR35 owner ri li
      [YulangClosure.SourceCallbackPermissionR35.TypeStep.result] w.permission
'YulangClosure.SourceCallbackUseR36.authenticated_r35' depends on axioms: [propext, Quot.sound]
@YulangClosure.SourceCallbackUseR36.authenticated_coordinates : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (w : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai w →
    ∃ l edge,
      (pool.roots owner.hirOwner)[ri]? = some l.root ∧
        l.root.expressions[li]? = some l.expression ∧
          l.expression.form = YulangClosure.SourceCallbackUseR36.Form.lambda l.formal l.body ∧
            l.formal.annotation = some l.annotation ∧
              l.root.expressions[ai]? = some edge.application ∧
                edge.application.form = YulangClosure.SourceCallbackUseR36.Form.apply edge.nameIndex edge.argument ∧
                  l.root.expressions[edge.nameIndex]? = some edge.name ∧
                    edge.name.form =
                        YulangClosure.SourceCallbackUseR36.Form.name
                          (YulangClosure.SourceCallbackUseR36.Resolution.parameter l.formal.id) ∧
                      YulangClosure.SourceCallbackUseR36.unambiguous l.root l.formal.id = true ∧
                        w.name = edge.name.site ∧
                          w.application = edge.application.site ∧
                            w.nameIndex = edge.nameIndex ∧
                              w.applyIndex = ai ∧
                                w.resolvedFormal = l.formal.id ∧
                                  w.permission.binding.formal = l.formal.id ∧
                                    w.permission.binding.root = l.root.id ∧
                                      w.permission.binding.lambdaOccurrence = l.expression.occurrence ∧
                                        w.permission.binding.snapshotOwner = owner.hirOwner ∧
                                          w.consumption = YulangClosure.SourceCallbackUseR36.Consumption.observe
'YulangClosure.SourceCallbackUseR36.authenticated_coordinates' depends on axioms: [propext, Quot.sound]
@YulangClosure.SourceCallbackUseR36.authenticated_result_row : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (w : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai w →
    ∃ l argument result row,
      YulangClosure.SourceCallbackUseR36.lookupLambda pool owner ri li = some l ∧
        l.annotation.ty =
            YulangClosure.SourceCallbackPermissionR35.AnnotationType.mk none
              (YulangClosure.SourceCallbackPermissionR35.AnnotationValue.function argument result) ∧
          YulangClosure.SourceCallbackPermissionR35.selectRow result [] = some row ∧
            w.permission.row = row ∧
              (∀ (index : Nat), w.permission.row.concrete[index]? = row.concrete[index]?) ∧
                w.permission.row.variables = row.variables ∧
                  w.permission.binding.rowPath = [YulangClosure.SourceCallbackPermissionR35.TypeStep.result] ∧
                    w.permission.binding.rowContravariant = true
'YulangClosure.SourceCallbackUseR36.authenticated_result_row' depends on axioms: [propext, Quot.sound]
@YulangClosure.SourceCallbackUseR36.reject_changed_projection : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green] {α : Type}
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (issued candidate : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.issue pool owner ri li ai = some issued →
    ∀ (projection : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green → α),
      projection candidate ≠ projection issued →
        ¬YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai candidate
'YulangClosure.SourceCallbackUseR36.reject_changed_projection' depends on axioms: [propext]
@YulangClosure.SourceCallbackUseR36.falsifier_rejection : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (issued candidate : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.issue pool owner ri li ai = some issued →
    candidate.permission.binding ≠ issued.permission.binding ∨
        candidate.resolvedFormal ≠ issued.resolvedFormal ∨
          candidate.name ≠ issued.name ∨
            candidate.application ≠ issued.application ∨
              candidate.nameIndex ≠ issued.nameIndex ∨
                candidate.applyIndex ≠ issued.applyIndex ∨
                  candidate.permission.row.concrete ≠ issued.permission.row.concrete ∨
                    candidate.permission.row.variables ≠ issued.permission.row.variables ∨
                      candidate.permission.row.position ≠ issued.permission.row.position ∨
                        candidate.consumption ≠ issued.consumption →
      ¬YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai candidate
'YulangClosure.SourceCallbackUseR36.falsifier_rejection' depends on axioms: [propext]
@YulangClosure.SourceCallbackUseR36.covariant_or_other_path_rejected : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (candidate : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  candidate.permission.binding.rowContravariant = false ∨
      candidate.permission.binding.rowPath ≠ [YulangClosure.SourceCallbackPermissionR35.TypeStep.result] →
    ¬YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai candidate
'YulangClosure.SourceCallbackUseR36.covariant_or_other_path_rejected' depends on axioms: [propext, Quot.sound]
```

### Attempt 4

Command: `bwrap --ro-bind / / --dev /dev --proc /proc /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean --stdin -j1 -M1024`

Exit: 1; measured subprocess seconds: 8.178845.
Input stdin SHA-256: `f40dbf45a66d0219359aec327b2230b2463c570bb6d440ebbc631d0b769b58ab`.

```text
<stdin>:2310:12: error: unsolved goals
case pos
Artifact Definition Module Parse Green : Type
inst✝⁴ : DecidableEq Artifact
inst✝³ : DecidableEq Definition
inst✝² : DecidableEq Module
inst✝¹ : DecidableEq Parse
inst✝ : DecidableEq Green
root : Root Artifact Definition Module Parse Green
formal : ParameterId Artifact Definition Module Parse Green
ai : Nat
edge : Edge Artifact Definition Module Parse Green
application : Expression Artifact Definition Module Parse Green
ha : root.expressions[ai]? = some application
callee argument : Nat
hf : application.form = Form.apply callee argument
name : Expression Artifact Definition Module Parse Green
hn : root.expressions[callee]? = some name
resolved : ParameterId Artifact Definition Module Parse Green
hnf : name.form = Form.name (Resolution.parameter resolved)
same : resolved = formal
found : { nameIndex := callee, name := name, applyIndex := ai, application := application, argument := argument } = edge
⊢ some application = some edge.application ∧
    edge.applyIndex = ai ∧
      edge.application.form = Form.apply edge.nameIndex edge.argument ∧
        root.expressions[edge.nameIndex]? = some edge.name ∧ edge.name.form = Form.name (Resolution.parameter formal)
<stdin>:2308:31: error: unsolved goals
case neg
Artifact Definition Module Parse Green : Type
inst✝⁴ : DecidableEq Artifact
inst✝³ : DecidableEq Definition
inst✝² : DecidableEq Module
inst✝¹ : DecidableEq Parse
inst✝ : DecidableEq Green
root : Root Artifact Definition Module Parse Green
formal : ParameterId Artifact Definition Module Parse Green
ai : Nat
edge : Edge Artifact Definition Module Parse Green
found :
  (do
      let application ← root.expressions[ai]?
      match application.form with
        | Form.apply callee argument => do
          let name ← root.expressions[callee]?
          match name.form with
            | Form.name (Resolution.parameter resolved) =>
              if resolved = formal then
                some
                  { nameIndex := callee, name := name, applyIndex := ai, application := application,
                    argument := argument }
              else none
            | x => none
        | x => none) =
    some edge
application : Expression Artifact Definition Module Parse Green
ha : root.expressions[ai]? = some application
callee argument : Nat
hf : application.form = Form.apply callee argument
name : Expression Artifact Definition Module Parse Green
hn : root.expressions[callee]? = some name
resolved : ParameterId Artifact Definition Module Parse Green
hnf : name.form = Form.name (Resolution.parameter resolved)
same : ¬resolved = formal
⊢ some application = some edge.application ∧
    edge.applyIndex = ai ∧
      edge.application.form = Form.apply edge.nameIndex edge.argument ∧
        root.expressions[edge.nameIndex]? = some edge.name ∧ edge.name.form = Form.name (Resolution.parameter formal)
<stdin>:2356:14: error: unexpected identifier; expected command
@YulangClosure.SourceCallbackUseR36.lookupLambda_origin : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li : Nat)
  (l : YulangClosure.SourceCallbackUseR36.SelectedLambda Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.lookupLambda pool owner ri li = some l →
    (pool.roots owner.hirOwner)[ri]? = some l.root ∧
      l.root.expressions[li]? = some l.expression ∧
        l.expression.form = YulangClosure.SourceCallbackUseR36.Form.lambda l.formal l.body ∧
          l.formal.annotation = some l.annotation ∧
            (∃ argument result,
                l.annotation.ty =
                  YulangClosure.SourceCallbackPermissionR35.AnnotationType.mk none
                    (YulangClosure.SourceCallbackPermissionR35.AnnotationValue.function argument result)) ∧
              YulangClosure.SourceCallbackUseR36.unambiguous l.root l.formal.id = true
'YulangClosure.SourceCallbackUseR36.lookupLambda_origin' depends on axioms: [propext]
@YulangClosure.SourceCallbackUseR36.lookupLambda_r35 : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li : Nat)
  (l : YulangClosure.SourceCallbackUseR36.SelectedLambda Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.lookupLambda pool owner ri li = some l →
    YulangClosure.SourceCallbackPermissionR35.selectFormal pool.toR35 owner ri li = some l.selection
'YulangClosure.SourceCallbackUseR36.lookupLambda_r35' depends on axioms: [propext]
@YulangClosure.SourceCallbackUseR36.lookupEdge_origin : ∀ {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (root : YulangClosure.SourceCallbackUseR36.Root Artifact Definition Module Parse Green)
  (formal : YulangClosure.SourceCallbackPermissionR35.ParameterId Artifact Definition Module Parse Green) (ai : Nat)
  (edge : YulangClosure.SourceCallbackUseR36.Edge Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.lookupEdge root formal ai = some edge →
    root.expressions[ai]? = some edge.application ∧
      edge.applyIndex = ai ∧
        edge.application.form = YulangClosure.SourceCallbackUseR36.Form.apply edge.nameIndex edge.argument ∧
          root.expressions[edge.nameIndex]? = some edge.name ∧
            edge.name.form =
              YulangClosure.SourceCallbackUseR36.Form.name
                (YulangClosure.SourceCallbackUseR36.Resolution.parameter formal)
'YulangClosure.SourceCallbackUseR36.lookupEdge_origin' depends on axioms: [propext, sorryAx]
@YulangClosure.SourceCallbackUseR36.foreign_parameter_name_rejected : ∀ {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (root : YulangClosure.SourceCallbackUseR36.Root Artifact Definition Module Parse Green)
  (formal foreign : YulangClosure.SourceCallbackPermissionR35.ParameterId Artifact Definition Module Parse Green)
  (ai callee argument : Nat)
  (application name : YulangClosure.SourceCallbackUseR36.Expression Artifact Definition Module Parse Green),
  root.expressions[ai]? = some application →
    application.form = YulangClosure.SourceCallbackUseR36.Form.apply callee argument →
      root.expressions[callee]? = some name →
        name.form =
            YulangClosure.SourceCallbackUseR36.Form.name
              (YulangClosure.SourceCallbackUseR36.Resolution.parameter foreign) →
          foreign ≠ formal → YulangClosure.SourceCallbackUseR36.lookupEdge root formal ai = none
'YulangClosure.SourceCallbackUseR36.foreign_parameter_name_rejected' depends on axioms: [propext]
@YulangClosure.SourceCallbackUseR36.nonparameter_name_rejected : ∀ {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (root : YulangClosure.SourceCallbackUseR36.Root Artifact Definition Module Parse Green)
  (formal : YulangClosure.SourceCallbackPermissionR35.ParameterId Artifact Definition Module Parse Green)
  (ai callee argument constructor : Nat)
  (application name : YulangClosure.SourceCallbackUseR36.Expression Artifact Definition Module Parse Green),
  root.expressions[ai]? = some application →
    application.form = YulangClosure.SourceCallbackUseR36.Form.apply callee argument →
      root.expressions[callee]? = some name →
        name.form =
            YulangClosure.SourceCallbackUseR36.Form.name
              (YulangClosure.SourceCallbackUseR36.Resolution.other constructor) →
          YulangClosure.SourceCallbackUseR36.lookupEdge root formal ai = none
'YulangClosure.SourceCallbackUseR36.nonparameter_name_rejected' depends on axioms: [propext]
@YulangClosure.SourceCallbackUseR36.ambiguity_withholds : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li : Nat)
  (root : YulangClosure.SourceCallbackUseR36.Root Artifact Definition Module Parse Green)
  (expression : YulangClosure.SourceCallbackUseR36.Expression Artifact Definition Module Parse Green)
  (formal : YulangClosure.SourceCallbackPermissionR35.Parameter Artifact Definition Module Parse Green) (body : Nat)
  (annotation : YulangClosure.SourceCallbackPermissionR35.SourceAnnotation Artifact Definition Module Parse Green),
  (pool.roots owner.hirOwner)[ri]? = some root →
    root.expressions[li]? = some expression →
      expression.form = YulangClosure.SourceCallbackUseR36.Form.lambda formal body →
        formal.annotation = some annotation →
          YulangClosure.SourceCallbackUseR36.unambiguous root formal.id = false →
            YulangClosure.SourceCallbackUseR36.lookupLambda pool owner ri li = none
'YulangClosure.SourceCallbackUseR36.ambiguity_withholds' depends on axioms: [propext, Quot.sound]
@YulangClosure.SourceCallbackUseR36.source_origin : ∀ {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory}
  {Artifact Definition Module Parse Green : Type} [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition]
  [inst_2 : DecidableEq Module] [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (w : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai w →
    ∃ l edge permission,
      YulangClosure.SourceCallbackUseR36.lookupLambda pool owner ri li = some l ∧
        YulangClosure.SourceCallbackUseR36.lookupEdge l.root l.formal.id ai = some edge ∧
          YulangClosure.SourceCallbackPermissionR35.issueSelected owner l.selection
                [YulangClosure.SourceCallbackPermissionR35.TypeStep.result] =
              some permission ∧
            w = YulangClosure.SourceCallbackUseR36.assemble l edge permission
'YulangClosure.SourceCallbackUseR36.source_origin' depends on axioms: [propext, Quot.sound]
@YulangClosure.SourceCallbackUseR36.authenticated_r35 : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (w : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai w →
    YulangClosure.SourceCallbackPermissionR35.authenticate pool.toR35 owner ri li
      [YulangClosure.SourceCallbackPermissionR35.TypeStep.result] w.permission
'YulangClosure.SourceCallbackUseR36.authenticated_r35' depends on axioms: [propext, Quot.sound]
@YulangClosure.SourceCallbackUseR36.authenticated_coordinates : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (w : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai w →
    ∃ l edge,
      (pool.roots owner.hirOwner)[ri]? = some l.root ∧
        l.root.expressions[li]? = some l.expression ∧
          l.expression.form = YulangClosure.SourceCallbackUseR36.Form.lambda l.formal l.body ∧
            l.formal.annotation = some l.annotation ∧
              l.root.expressions[ai]? = some edge.application ∧
                edge.application.form = YulangClosure.SourceCallbackUseR36.Form.apply edge.nameIndex edge.argument ∧
                  l.root.expressions[edge.nameIndex]? = some edge.name ∧
                    edge.name.form =
                        YulangClosure.SourceCallbackUseR36.Form.name
                          (YulangClosure.SourceCallbackUseR36.Resolution.parameter l.formal.id) ∧
                      YulangClosure.SourceCallbackUseR36.unambiguous l.root l.formal.id = true ∧
                        w.name = edge.name.site ∧
                          w.application = edge.application.site ∧
                            w.nameIndex = edge.nameIndex ∧
                              w.applyIndex = ai ∧
                                w.resolvedFormal = l.formal.id ∧
                                  w.permission.binding.formal = l.formal.id ∧
                                    w.permission.binding.root = l.root.id ∧
                                      w.permission.binding.lambdaOccurrence = l.expression.occurrence ∧
                                        w.permission.binding.snapshotOwner = owner.hirOwner ∧
                                          w.consumption = YulangClosure.SourceCallbackUseR36.Consumption.observe
'YulangClosure.SourceCallbackUseR36.authenticated_coordinates' depends on axioms: [propext, sorryAx, Quot.sound]
@YulangClosure.SourceCallbackUseR36.authenticated_result_row : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (w : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai w →
    ∃ l argument result row,
      YulangClosure.SourceCallbackUseR36.lookupLambda pool owner ri li = some l ∧
        l.annotation.ty =
            YulangClosure.SourceCallbackPermissionR35.AnnotationType.mk none
              (YulangClosure.SourceCallbackPermissionR35.AnnotationValue.function argument result) ∧
          YulangClosure.SourceCallbackPermissionR35.selectRow result [] = some row ∧
            w.permission.row = row ∧
              (∀ (index : Nat), w.permission.row.concrete[index]? = row.concrete[index]?) ∧
                w.permission.row.variables = row.variables ∧
                  w.permission.binding.rowPath = [YulangClosure.SourceCallbackPermissionR35.TypeStep.result] ∧
                    w.permission.binding.rowContravariant = true
'YulangClosure.SourceCallbackUseR36.authenticated_result_row' depends on axioms: [propext, Quot.sound]
@YulangClosure.SourceCallbackUseR36.reject_changed_projection : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green] {α : Type}
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (issued candidate : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.issue pool owner ri li ai = some issued →
    ∀ (projection : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green → α),
      projection candidate ≠ projection issued →
        ¬YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai candidate
'YulangClosure.SourceCallbackUseR36.reject_changed_projection' depends on axioms: [propext]
@YulangClosure.SourceCallbackUseR36.falsifier_rejection : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (issued candidate : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.issue pool owner ri li ai = some issued →
    candidate.permission.binding ≠ issued.permission.binding ∨
        candidate.resolvedFormal ≠ issued.resolvedFormal ∨
          candidate.name ≠ issued.name ∨
            candidate.application ≠ issued.application ∨
              candidate.nameIndex ≠ issued.nameIndex ∨
                candidate.applyIndex ≠ issued.applyIndex ∨
                  candidate.permission.row.concrete ≠ issued.permission.row.concrete ∨
                    candidate.permission.row.variables ≠ issued.permission.row.variables ∨
                      candidate.permission.row.position ≠ issued.permission.row.position ∨
                        candidate.consumption ≠ issued.consumption →
      ¬YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai candidate
'YulangClosure.SourceCallbackUseR36.falsifier_rejection' depends on axioms: [propext]
@YulangClosure.SourceCallbackUseR36.covariant_or_other_path_rejected : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (candidate : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  candidate.permission.binding.rowContravariant = false ∨
      candidate.permission.binding.rowPath ≠ [YulangClosure.SourceCallbackPermissionR35.TypeStep.result] →
    ¬YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai candidate
'YulangClosure.SourceCallbackUseR36.covariant_or_other_path_rejected' depends on axioms: [propext, Quot.sound]
```

### Attempt 5

Command: `bwrap --ro-bind / / --dev /dev --proc /proc /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean --stdin -j1 -M1024`

Exit: 0; measured subprocess seconds: 8.360617.
Input stdin SHA-256: `62910405e822f2110317c059970091007bd2a1969211415573f76e68760fa23a`.

```text
@YulangClosure.SourceCallbackUseR36.lookupLambda_origin : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li : Nat)
  (l : YulangClosure.SourceCallbackUseR36.SelectedLambda Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.lookupLambda pool owner ri li = some l →
    (pool.roots owner.hirOwner)[ri]? = some l.root ∧
      l.root.expressions[li]? = some l.expression ∧
        l.expression.form = YulangClosure.SourceCallbackUseR36.Form.lambda l.formal l.body ∧
          l.formal.annotation = some l.annotation ∧
            (∃ argument result,
                l.annotation.ty =
                  YulangClosure.SourceCallbackPermissionR35.AnnotationType.mk none
                    (YulangClosure.SourceCallbackPermissionR35.AnnotationValue.function argument result)) ∧
              YulangClosure.SourceCallbackUseR36.unambiguous l.root l.formal.id = true
'YulangClosure.SourceCallbackUseR36.lookupLambda_origin' depends on axioms: [propext]
@YulangClosure.SourceCallbackUseR36.lookupLambda_r35 : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li : Nat)
  (l : YulangClosure.SourceCallbackUseR36.SelectedLambda Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.lookupLambda pool owner ri li = some l →
    YulangClosure.SourceCallbackPermissionR35.selectFormal pool.toR35 owner ri li = some l.selection
'YulangClosure.SourceCallbackUseR36.lookupLambda_r35' depends on axioms: [propext]
@YulangClosure.SourceCallbackUseR36.lookupEdge_origin : ∀ {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (root : YulangClosure.SourceCallbackUseR36.Root Artifact Definition Module Parse Green)
  (formal : YulangClosure.SourceCallbackPermissionR35.ParameterId Artifact Definition Module Parse Green) (ai : Nat)
  (edge : YulangClosure.SourceCallbackUseR36.Edge Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.lookupEdge root formal ai = some edge →
    root.expressions[ai]? = some edge.application ∧
      edge.applyIndex = ai ∧
        edge.application.form = YulangClosure.SourceCallbackUseR36.Form.apply edge.nameIndex edge.argument ∧
          root.expressions[edge.nameIndex]? = some edge.name ∧
            edge.name.form =
              YulangClosure.SourceCallbackUseR36.Form.name
                (YulangClosure.SourceCallbackUseR36.Resolution.parameter formal)
'YulangClosure.SourceCallbackUseR36.lookupEdge_origin' depends on axioms: [propext]
@YulangClosure.SourceCallbackUseR36.foreign_parameter_name_rejected : ∀ {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (root : YulangClosure.SourceCallbackUseR36.Root Artifact Definition Module Parse Green)
  (formal foreign : YulangClosure.SourceCallbackPermissionR35.ParameterId Artifact Definition Module Parse Green)
  (ai callee argument : Nat)
  (application name : YulangClosure.SourceCallbackUseR36.Expression Artifact Definition Module Parse Green),
  root.expressions[ai]? = some application →
    application.form = YulangClosure.SourceCallbackUseR36.Form.apply callee argument →
      root.expressions[callee]? = some name →
        name.form =
            YulangClosure.SourceCallbackUseR36.Form.name
              (YulangClosure.SourceCallbackUseR36.Resolution.parameter foreign) →
          foreign ≠ formal → YulangClosure.SourceCallbackUseR36.lookupEdge root formal ai = none
'YulangClosure.SourceCallbackUseR36.foreign_parameter_name_rejected' depends on axioms: [propext]
@YulangClosure.SourceCallbackUseR36.nonparameter_name_rejected : ∀ {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (root : YulangClosure.SourceCallbackUseR36.Root Artifact Definition Module Parse Green)
  (formal : YulangClosure.SourceCallbackPermissionR35.ParameterId Artifact Definition Module Parse Green)
  (ai callee argument constructor : Nat)
  (application name : YulangClosure.SourceCallbackUseR36.Expression Artifact Definition Module Parse Green),
  root.expressions[ai]? = some application →
    application.form = YulangClosure.SourceCallbackUseR36.Form.apply callee argument →
      root.expressions[callee]? = some name →
        name.form =
            YulangClosure.SourceCallbackUseR36.Form.name
              (YulangClosure.SourceCallbackUseR36.Resolution.other constructor) →
          YulangClosure.SourceCallbackUseR36.lookupEdge root formal ai = none
'YulangClosure.SourceCallbackUseR36.nonparameter_name_rejected' depends on axioms: [propext]
@YulangClosure.SourceCallbackUseR36.ambiguity_withholds : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li : Nat)
  (root : YulangClosure.SourceCallbackUseR36.Root Artifact Definition Module Parse Green)
  (expression : YulangClosure.SourceCallbackUseR36.Expression Artifact Definition Module Parse Green)
  (formal : YulangClosure.SourceCallbackPermissionR35.Parameter Artifact Definition Module Parse Green) (body : Nat)
  (annotation : YulangClosure.SourceCallbackPermissionR35.SourceAnnotation Artifact Definition Module Parse Green),
  (pool.roots owner.hirOwner)[ri]? = some root →
    root.expressions[li]? = some expression →
      expression.form = YulangClosure.SourceCallbackUseR36.Form.lambda formal body →
        formal.annotation = some annotation →
          YulangClosure.SourceCallbackUseR36.unambiguous root formal.id = false →
            YulangClosure.SourceCallbackUseR36.lookupLambda pool owner ri li = none
'YulangClosure.SourceCallbackUseR36.ambiguity_withholds' depends on axioms: [propext, Quot.sound]
@YulangClosure.SourceCallbackUseR36.source_origin : ∀ {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory}
  {Artifact Definition Module Parse Green : Type} [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition]
  [inst_2 : DecidableEq Module] [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (w : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai w →
    ∃ l edge permission,
      YulangClosure.SourceCallbackUseR36.lookupLambda pool owner ri li = some l ∧
        YulangClosure.SourceCallbackUseR36.lookupEdge l.root l.formal.id ai = some edge ∧
          YulangClosure.SourceCallbackPermissionR35.issueSelected owner l.selection
                [YulangClosure.SourceCallbackPermissionR35.TypeStep.result] =
              some permission ∧
            w = YulangClosure.SourceCallbackUseR36.assemble l edge permission
'YulangClosure.SourceCallbackUseR36.source_origin' depends on axioms: [propext, Quot.sound]
@YulangClosure.SourceCallbackUseR36.authenticated_r35 : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (w : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai w →
    YulangClosure.SourceCallbackPermissionR35.authenticate pool.toR35 owner ri li
      [YulangClosure.SourceCallbackPermissionR35.TypeStep.result] w.permission
'YulangClosure.SourceCallbackUseR36.authenticated_r35' depends on axioms: [propext, Quot.sound]
@YulangClosure.SourceCallbackUseR36.authenticated_coordinates : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (w : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai w →
    ∃ l edge,
      (pool.roots owner.hirOwner)[ri]? = some l.root ∧
        l.root.expressions[li]? = some l.expression ∧
          l.expression.form = YulangClosure.SourceCallbackUseR36.Form.lambda l.formal l.body ∧
            l.formal.annotation = some l.annotation ∧
              l.root.expressions[ai]? = some edge.application ∧
                edge.application.form = YulangClosure.SourceCallbackUseR36.Form.apply edge.nameIndex edge.argument ∧
                  l.root.expressions[edge.nameIndex]? = some edge.name ∧
                    edge.name.form =
                        YulangClosure.SourceCallbackUseR36.Form.name
                          (YulangClosure.SourceCallbackUseR36.Resolution.parameter l.formal.id) ∧
                      YulangClosure.SourceCallbackUseR36.unambiguous l.root l.formal.id = true ∧
                        w.name = edge.name.site ∧
                          w.application = edge.application.site ∧
                            w.nameIndex = edge.nameIndex ∧
                              w.applyIndex = ai ∧
                                w.resolvedFormal = l.formal.id ∧
                                  w.permission.binding.formal = l.formal.id ∧
                                    w.permission.binding.root = l.root.id ∧
                                      w.permission.binding.lambdaOccurrence = l.expression.occurrence ∧
                                        w.permission.binding.snapshotOwner = owner.hirOwner ∧
                                          w.consumption = YulangClosure.SourceCallbackUseR36.Consumption.observe
'YulangClosure.SourceCallbackUseR36.authenticated_coordinates' depends on axioms: [propext, Quot.sound]
@YulangClosure.SourceCallbackUseR36.authenticated_result_row : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (w : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai w →
    ∃ l argument result row,
      YulangClosure.SourceCallbackUseR36.lookupLambda pool owner ri li = some l ∧
        l.annotation.ty =
            YulangClosure.SourceCallbackPermissionR35.AnnotationType.mk none
              (YulangClosure.SourceCallbackPermissionR35.AnnotationValue.function argument result) ∧
          YulangClosure.SourceCallbackPermissionR35.selectRow result [] = some row ∧
            w.permission.row = row ∧
              (∀ (index : Nat), w.permission.row.concrete[index]? = row.concrete[index]?) ∧
                w.permission.row.variables = row.variables ∧
                  w.permission.binding.rowPath = [YulangClosure.SourceCallbackPermissionR35.TypeStep.result] ∧
                    w.permission.binding.rowContravariant = true
'YulangClosure.SourceCallbackUseR36.authenticated_result_row' depends on axioms: [propext, Quot.sound]
@YulangClosure.SourceCallbackUseR36.reject_changed_projection : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green] {α : Type}
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (issued candidate : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.issue pool owner ri li ai = some issued →
    ∀ (projection : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green → α),
      projection candidate ≠ projection issued →
        ¬YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai candidate
'YulangClosure.SourceCallbackUseR36.reject_changed_projection' depends on axioms: [propext]
@YulangClosure.SourceCallbackUseR36.falsifier_rejection : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (issued candidate : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  YulangClosure.SourceCallbackUseR36.issue pool owner ri li ai = some issued →
    candidate.permission.binding ≠ issued.permission.binding ∨
        candidate.resolvedFormal ≠ issued.resolvedFormal ∨
          candidate.name ≠ issued.name ∨
            candidate.application ≠ issued.application ∨
              candidate.nameIndex ≠ issued.nameIndex ∨
                candidate.applyIndex ≠ issued.applyIndex ∨
                  candidate.permission.row.concrete ≠ issued.permission.row.concrete ∨
                    candidate.permission.row.variables ≠ issued.permission.row.variables ∨
                      candidate.permission.row.position ≠ issued.permission.row.position ∨
                        candidate.consumption ≠ issued.consumption →
      ¬YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai candidate
'YulangClosure.SourceCallbackUseR36.falsifier_rejection' depends on axioms: [propext]
@YulangClosure.SourceCallbackUseR36.covariant_or_other_path_rejected : ∀
  {history : YulangClosure.NativeSnapshotOwnerR34.AllocationHistory} {Artifact Definition Module Parse Green : Type}
  [inst : DecidableEq Artifact] [inst_1 : DecidableEq Definition] [inst_2 : DecidableEq Module]
  [inst_3 : DecidableEq Parse] [inst_4 : DecidableEq Green]
  (pool : YulangClosure.SourceCallbackUseR36.Pool history Artifact Definition Module Parse Green)
  (owner : YulangClosure.NativeSnapshotOwnerR34.RuntimeOwner history) (ri li ai : Nat)
  (candidate : YulangClosure.SourceCallbackUseR36.Witness history Artifact Definition Module Parse Green),
  candidate.permission.binding.rowContravariant = false ∨
      candidate.permission.binding.rowPath ≠ [YulangClosure.SourceCallbackPermissionR35.TypeStep.result] →
    ¬YulangClosure.SourceCallbackUseR36.authenticate pool owner ri li ai candidate
'YulangClosure.SourceCallbackUseR36.covariant_or_other_path_rejected' depends on axioms: [propext, Quot.sound]
```
