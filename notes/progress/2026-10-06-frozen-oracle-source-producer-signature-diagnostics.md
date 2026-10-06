# Frozen Oracle signature diagnostics: a bounded exclusion of one candidate producer

Date: 2026-10-06
Yulang3 baseline at assignment inspection: `adfcb1ac0eddb30ff5e6406a1c47b46428504597`
Branch: `research/simple-sub-intrusion`
Frozen Oracle pin: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle checkout: `/tmp/yulang2-oracle-rebuild`
Status: frozen unreviewed historical source characterization
Method: bounded source archaeology and direct branch reduction
Exclusive lease: this note only
Semantic and implementation authority: none

## Objective, governing premises, and distinct seam

Inspect one historical mechanism near the missing original inferred-signature
applicability/contribution producer. The selected seam is the **compact
signature diagnostic gate**, called during method lowering before a separate
requirement connection. Earlier archaeology traced stored method signatures,
receiver elaboration, ordinary application endpoints, annotation markers,
frame grouping, generalized paths, and claim attribution. A bounded search of
the existing `2026-10-06-frozen-oracle-*` notes found no occurrence of
`signature_match`, `compact_type_matches_signature`, or
`check_result_annotation`; the source-association note's stored-signature
producer is retained as prior evidence, not repeated here. This search is a
novelty check over that named note family, not an exhaustive research-history
claim.

Current authority is read directly from:

- `notes/design/2026-10-05-inferred-function-call-views.md` §§1.1–5:
  source/public/internal distinctions, shared source formation, stable slots,
  Q-independent admission, provisional formal treatment, and open judgments.
- `notes/design/2026-10-05-source-contracts-and-common-allowance.md`
  §§2.2, 3, 10: independently active complete constraints, typed source
  incidence and admission certificates, and remaining production obligations.
- `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md`
  §§2–4: an original protected-variable upper-use introduction does not
  propagate protection back into an existing provider lower bound.
- `notes/progress/2026-10-06-original-signature-licensing-construction.md`:
  the first open leaf is an independently interpreted `Attach_C`/`Lic_C`,
  with attachment soundness and exhaustive origin inversion on the same X.

No selected language meaning is changed. In particular an annotation, public
compact type, and original internal contribution are not identified. Oracle
is historical evidence only. Its spelling of a compatibility helper is not
current semantic authority.

## Hypotheses and claim class

H1: the inspected Oracle files have the recorded bytes in the checkout whose
HEAD resolves to the supplied Oracle pin. No Oracle program is executed.

H2: consider the actual receiverless method-lowering branch with a supplied
`ResolvedRoleMethodRequirement`, `defer_receiverless_requirement=false`, and
successful body lowering. The body and requirement already exist before the
diagnostic gate is entered. This is a branch hypothesis, not a claim that the
current nested ordinary-call candidate enters role-method lowering.

H3: for the minimal local discriminator, the compact root has `never=false`,
exactly one `CompactFun`, and no concrete non-Function components. Its return
is the singleton builtin Int. The expected signature is a Function returning
the builtin Int. This is a data-structure witness, not an admitted source
program or complete original row.

The established result of this inspection is bounded historical control and
data flow. The field-independence result below is a conditional theorem about
the inspected helper's branches under H1/H3. Neither is a theorem of current
source semantics, a source counterexample, or a source impossibility result.

## Exact producer/control path

All source locators below are relative to the pinned Oracle checkout.

1. `crates/infer/src/lowering/expr/method_body.rs:459–487` lowers the
   receiverless body, through either `lower_lambda_params` or
   `lower_defined_lambda_params_with_anchors`. With H2, `:522–529` calls
   `connect_impl_method_requirement(body.value, requirement, ..., true)`.
   Thus the inspected compact diagnostic consumes a body value already
   produced by lowering; it is not an upstream formal/upper-use emitter.

2. `method_body.rs:1389–1408` first calls
   `check_impl_method_requirement_shape`, then
   `check_impl_method_requirement_concrete_type`. The latter at `:1487–1499`
   takes `&self`, obtains `compact_type_var` from existing constraints, and
   returns `Ok(())` or `SignatureTypeMismatch`. Its result contains no slot,
   source-use ID, contribution, typed position, or owner certificate.
   `crates/infer/src/compact/surface.rs:8–10` delegates this compact query to
   `CompactCollector::new(machine).compact_root(root)` with an immutable
   `&ConstraintMachine`. This is the ordinary compact query, not the separate
   mutable scheme/projection gateway at `:12–23`. No final-solving phase or
   global post-generalization ordering is assumed here.

3. `crates/infer/src/lowering/signature_match.rs:1–4` explicitly describes
   these helpers as diagnostic classifiers that do not mutate constraints.
   In the concrete helper, `:21–22` discards all expected Function fields
   except `ret`. After rejecting concrete non-Function components at
   `:76–78`, `:79–82` checks every compact Function return. The leaf at
   `:137–142` inspects only `actual.ret`. The analogous shape helper follows
   `:48–49`, `:85–97`, and `:145–150`.

4. The structure really has omitted coordinates:
   `crates/infer/src/compact/mod.rs:541–546` declares
   `CompactFun { arg, arg_eff, ret_eff, ret }`, and
   `crates/infer/src/lowering/mod.rs:270–275` declares
   `SignatureType::Function { param, arg_eff, ret_eff, ret }`.
   Their absence from the Function diagnostic branch is not absence from the
   historical type representation. Effectful expected signatures also recurse
   through `ret` at `signature_match.rs:18–19,45–46`.

5. On diagnostic success, `method_body.rs:1400–1408` constructs a continuation
   from annotation-variable bindings and the current level, then calls
   `connect_impl_method_requirement_from_continuation`. The latter at
   `:1419–1454` separately lowers the supplied signature positively and,
   when `connect_value_upper=true`, negatively; it requests the corresponding
   subtype edges with `OriginId::unknown_internal()`. At `:1456–1462` it
   registers a compact role-implementation member projection under
   `self.parent` and invokes simplification registration. This separate
   connector retains more signature structure than the Boolean classifier.
   The inspected routine still does not emit a current
   `(beta,s,p,c)` association or an exhaustive original licensing judgment.

6. An actual source-annotation consumer uses the same diagnostic family:
   `method_body.rs:1723–1727` builds an `AnnType` from result-annotation CST
   and checks it before upcasts/annotation connection. The wrapper at
   `:1861–1874` converts the annotation to `SignatureType`, compacts the
   body value, and calls the shape helper. The subsequent annotation producer
   at `:1730–1751` is separate. This second call site confirms that classifier
   success is used as a control gate; it does not make the classifier's
   Boolean a source-contribution receipt.

The graph-shape diagnostic at `method_body.rs:1501–1575` is also read to avoid
mistaking the preceding check for a missing producer: it takes `&self`, follows
existing bounds, and returns a Boolean. Its Function branch may descend into
nested return-Function shape. No successful diagnostic constructs source
incidence data in this inspected path. This does not claim that no other
Oracle mechanism retains such data.

## Smallest discriminator and derivation

Use one compact Function and one expected Function. Hold the return fixed:

```text
S  = SignatureType::Function(param=P, arg_eff=AE, ret_eff=RE, ret=Int)
C0 = CompactType(funs=[CompactFun(arg=A, arg_eff=E, ret_eff=R0, ret=Int)])
C1 = CompactType(funs=[CompactFun(arg=A, arg_eff=E, ret_eff=R1, ret=Int)])
R0 != R1; all other root fields satisfy H3 and are identical.
```

`R0` and `R1` may be two distinct compact effect-row data structures; no
interpretation as current permissions, events, or admitted observations is
needed. The smallest difference is one omitted field of the single Function.
The branch reduction is:

```text
matches(Ci,S)
  = every fun in Ci.funs. matches(fun.ret,Int)
  = matches(singleton builtin Int,Int)
  = true, for i=0 and i=1.
```

The last equality follows from the constructor branch at
`signature_match.rs:26–30,162–181` and the builtin constructor conversion at
`:275–280`. The shape helper also returns true for both because the return has
no concrete non-constructor component (`:55–56`). Changing `arg` or `arg_eff`
alone gives the same result, as does changing expected `param`, `arg_eff`, or
`ret_eff` while its `ret` remains fixed. These are direct code reductions;
no toy checker reproducing the supplied rules was used.

Conditional field-independence theorem: under H1/H3, both Boolean helpers are
invariant under the indicated omitted-field mutations. Therefore their
successful result alone cannot recover which return-effect coordinate or
contribution was supplied. This rejects the shortcut “successful signature
diagnostic establishes original contribution attachment.” It does not show
that the later full signature constraints treat C0 and C1 equally, that either
source is accepted, or that diagnostic equality forbids a later independent
join. The witness needs no second call, duplicate endpoint, generalized
projection, runtime execution, or slot-sharing assumption.

Failure conditions are explicit: adding a concrete non-Function root
component can fail before checking returns; altering the return can alter the
concrete result; setting `never=true` takes a separate immediate-success
branch. A mutation making the helper examine `ret_eff` invalidates the
field-independence derivation. A source realization of C0/C1, their complete
admission, and solver outcomes were not constructed.

## Current missing rule, independence, and next action

The current candidate's original upper-use and address witness remains
upstream of `Attach_C(X,e0,(beta,s,p,c))`. A compact signature success neither
types that complete contribution nor supplies attachment soundness or
exhaustive `Lic_C` inversion. H2 also belongs to a role-method requirement
path, while the selected nested ordinary-call candidate has no supplied
role-method requirement. No correspondence into that candidate is invented.

Oracle independence is limited to inspecting a real historical implementation
separately from the current proof notation. Both this note and previous
archaeology share the same frozen Oracle source and governing current
contracts; this is not an independent semantic oracle or independent review.
Historical subtype/compact rules are read as code, not justified as current
source rules by their own operation. The discriminator is a local
information-loss witness, not a language rejection or complete-row witness.

Recommended next action: derive `OriginalAssocType_X`/`Attach_C` for the
already constructed ordinary Call contribution on the fixed original X,
then establish both licensing directions. Do not expand this diagnostic seam
into another matching experiment: its output and omitted fields already
explain the precise blocker, and further variants leave the source-owned
association premise untouched.

## Checks, provenance, coverage, and resources

Read-only commands used `cat`, bounded `sed -n`, `nl -ba`, `rg -n`,
`rg --files`, and inline Python reading files/HEAD/ref metadata and computing
SHA-256. No Git command or mutation, build, test, Oracle execution, compiler
edit, runtime probe, formatting, scratch artifact, or delegation was used.
One initial file locator assumed `src/` and failed; it was corrected to
`crates/infer/src/`. A later direct Oracle `.git/HEAD` read failed because
the checkout uses a `.git` indirection file; the earlier resolved metadata
read succeeded and the final recheck uses that indirection. Initial broad
captures truncated; decisive code and governing sections were reread in
bounded windows. No negative claim rests on a truncated capture.

The two Function matching helpers were inspected in full, including their
return/constructor branches; only the named method/annotation caller windows
and compact entrypoint were traced. Unverified scope includes compact
collection correctness, complete solver behavior, method dispatch reachability
from specific source text, adapters, runtime treatment, recursive/general
source coverage, current profile/admission/nonemptiness, principality,
production Option A/2 membership, and conformance. No seed/range enumeration,
executed mutation, performance sample, or complete source search occurred.

Heavyweight processes: zero. Shell/Python reads were serial at the process
level; no local parallel build or probe. CPU time, peak RAM, and total wall
time were not measured; no numeric process/memory/wall budget was supplied.
Output-path budget: one new note, consumed. Research stops after this distinct
mechanism and local exclusion. The note is frozen before submission for
review; authorship does not certify it.

Yulang3 HEAD moved concurrently to
`ad38945acabfd0c11052686d0006810caa809eef` during inspection. Its relevant
document hashes are rechecked at freeze; unrelated branch movement does not
serve as source evidence. Oracle HEAD remains the supplied pin. Recorded
SHA-256 values identify the inspected bytes. Historical method-body,
lowering-mod, and compact-surface hashes also match prior frozen archaeology
inventories. No Git-object blob comparison was performed for the newly
inspected matcher; HEAD equality alone is not a worktree-cleanliness proof.

| Direct Yulang3 dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/progress/2026-10-06-original-signature-licensing-construction.md` | `f5032a91781706551dcd01474f6024eb34fcb0cb110fa6157f7ec577ccfc5cff` |
| `notes/progress/2026-10-06-frozen-oracle-source-association-mechanism.md` | `570ed6b7ebb6adedf9ad78d9c137e215442c0fc4f74f69987738872d28499db4` |

| Oracle dependency under `crates/infer/src/` | SHA-256 |
| --- | --- |
| `lowering/signature_match.rs` | `180434c5a29e56549111dc3d26fd4ec2a487502470eaa544cac9b203cd3dc251` |
| `lowering/expr/method_body.rs` | `3319db30fd3d6771eea156a2b902372c59db75ce1e27f64fcb44d987c3e52b74` |
| `lowering/mod.rs` | `244e5f8ea339d2e24aa1f8456e99072e4a491b97da58348a4e79eed188ce61a1` |
| `compact/mod.rs` | `122b349ce5adcc273738828736a8f4a7701aa60a57922b286e9fc96965f2ddc4` |
| `compact/surface.rs` | `1516be08117a372269909fcb7f64780cee4389a52a4f86ef63dd6eaa752b0d89` |

## Commit packet

- Exact leased/change path:
  `notes/progress/2026-10-06-frozen-oracle-source-producer-signature-diagnostics.md`.
- Baseline SHA: `adfcb1ac0eddb30ff5e6406a1c47b46428504597`;
  integration recheck HEAD `ad38945acabfd0c11052686d0006810caa809eef`;
  Oracle pin `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed direct dependency hashes: none at freeze. Shared task record may
  move independently; no claim depends on its final bytes.
- Review status: frozen unreviewed research characterization and conditional
  helper field-independence result. No independent review, source theorem
  closure, semantic authority, or implementation authority.
- Checks already run: governing/previous-trace reads, exact caller and helper
  branch reductions, prior-note novelty search, path-absence check,
  HEAD/ref-metadata and dependency-hash rechecks, note-local integrity read.
  No executable verification. Primary must inspect exact lease/diff and may
  independently verify matcher bytes against the Oracle commit before review.
- Proposed one-line research-checkpoint commit message:
  `research: exclude Oracle signature diagnostics as contribution producer`.
- Shared-record deltas intentionally left for primary/curator: record this
  distinct diagnostic exclusion only if useful; retain `Attach_C`/`Lic_C`,
  complete profile/admission, source adequacy, principality, and production
  conformance as open. No task/index/theory/authority/question file changed.
