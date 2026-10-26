# INFERENCE-PROFILE-RESTRICTION-20261026/r1

Status: FROZEN producer proof; independent review pending. Author `/root/profile_transport`.
Parent/integration owner: `/root`. No children, Git operations, shared-status writes,
compiler changes, new semantics, dependency installs or root-import edits.
Baseline supplied by primary: `eb3eef2f6a29d9c2a6132d648866c60900db276c` on `yulang3`.
The worker did not use Git to assert baseline byte equality; direct input bytes
are identified below for primary revalidation.

## 1. Constructed outcome and original parent application

The paper's NPR theorem proves, for every actual finite selected native
`L/DeclContribution` derivation and every true licensed field key, that

```text
NP(restricted original leaf packets, sigma_*derivation)[sigma_*key]
  = restrict_sigma(NP(original leaf packets, derivation)[key]).
```

It uses the existing native constructors and PF1/PF2, with the actual lawful
hereditary restriction of W/VB1. No generated-profile naturality premise,
`LocalLaws` package, new native datatype, certificate redefinition or source
restriction is introduced. Original complete tuples, source tags, actual
licenses, original source owners and receiving registrations stay distinct.
The proof includes Primitive/inherited/local-default, Operand, Ref, Scope,
Rename, Union/Alt, shared Pair, Op, actual Bind/Call/Record/Result/Delay/Lambda
instances, root Insert, L-Declared, L-UpperCall, L-Reference, L-Annotation and
all original Whole certificate cases, including one-hidden-package admission.
Actual complete independent arms remain their own genuine leaf packets.

VB-NP applies NPR to VB1's actual typed Return and fresh dynamic ValueBind,
then the original Resolve/capture route and selected `Call(Name h,Name x)` /
ReadInvoke field maps. The separately assumed *generated native profile
transport* component is now derived at the new binding, Name lookup, pending
suffix and every original compatible future use. Source-result CIncl is still
provided by GC3; this theorem adds the hereditary native-profile component,
not a new result-typing axiom.

The exact original parent remains `SourceProblem.InferenceSoundness`, with
all original supported source constructors and one shared scoped witness.
Genuine independent primitive/annotation/arm actions and licenses, actual
recursive operand/history realization, and native-success-to-original-full-
solution/source reconstruction remain. A full original `G_call` solution
already contains its decorated certificate and may be reconstructed by the
existing fixed decorated Call rule. No new exhaustive certificate declaration
is required merely to consume such a supplied solution.

## 2. Lean scope and represented types

The authoritative native grammar is paper-defined; there is no current Lean
`L`, `DeclContribution` or `NP` datatype. The new module deliberately checks
only the original proof's concrete dependent-record algebra. It does not
claim a Lean theorem about an undeclared native judgment or whole inference.
`W` denotes the entire joint tuple; `P : W -> Type` the whole licensed packet.
`restrictPacket r a` maps `(w,p)` to `(r w,a w p)`. Actual leaf actions `a`
are inputs, not a premise asserting generated NP commutation. Source/native
interpretation is supplied by the exhaustive paper induction, pending review.

Fully qualified theorem namespace: `YulangClosure.NativeProfileRestriction`.
The complete 21 theorem types and every generated/module-origin declaration
are printed verbatim in §7. In particular:

- `assembleFields_restriction` is pointwise dependent case-analysis naturality
  over the inherited/local field partition, preserving empty fibers.
- `dependentBind_restriction` retains one middle witness and its dependent
  suffix/evidence, applicable to actual Bind and one-package hiding.
- `valueBind_profile_restriction` retains one joint tuple, the genuine old and
  new child packets and the unchanged selected local policy.

No actual mutable-State semantics, foreign-profile bridge, source typing
judgment, arbitrary provider replacement, missing license producer or
full-certificate constructor is formalized by this module. These omissions
are not changes to the original parent source domain.

## 3. Checks, resource bounds, and material failures

Pinned installed executable:
`/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.
Actual successful version outputs:

```text
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

Final checker command (exit 0):

```sh
python3 /workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py \
  --project /workspace/scratch/f98087c7ac1a/inference-profile-restriction/project \
  --lake /workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake \
  --module YulangClosure.NativeProfileRestriction \
  --theorem YulangClosure.NativeProfileRestriction.assembleFields_restriction \
  --theorem YulangClosure.NativeProfileRestriction.dependentBind_restriction \
  --theorem YulangClosure.NativeProfileRestriction.valueBind_profile_restriction \
  --timeout 120
```

The helper freshly built the requested module and checked each listed theorem's
kind/type/axioms; build completed successfully, 2 jobs. The complete module
check then used (exit 0):

```sh
timeout 120s env LEAN_NUM_THREADS=1 \
  /workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake \
  env lean -j1 -M1024 AuditNativeProfileRestriction.lean
```

Its inventory uses `env.getModuleIdxFor?` for **all** constants originating
in the module, including generated/private declarations; every constant is
`#check`ed and `#print axioms` is run. A project `axiomInfo` declaration fails
immediately. `collectAxioms` rejects anything outside the existing standard
whitelist. Result: **33 declarations, 21 theorems, all 33 have no axioms**.
Generated `restrictPacket.match_1` and `restrictAlternative.match_1` are
included. No originating private declaration was omitted. This module imports
only `Init`; no repository proof dependency is hidden in its Lean import cone.
Source search found no `sorry`, `admit`, project axiom or bypass token in the
module. Exact scratch/repository module bytes match. All paper links resolve
and code fences balance. No full moving-project/default-target build was run.

Five bounded proof/audit invocations total: first helper failed; repaired
helper passed; complete module audit passed; final helper passed; final
complete audit passed. All used at most 120 seconds each, one active checker
process and one Lean thread, Lean `-M1024`. No timeout occurred. Assignment
budget was 1600 seconds and <=16 checks. The earliest recorded clock read
in this worker was 02:12:48 UTC; the final evidence read was 02:23:09 UTC.
Exact total worker active duration was not instrumented and is not invented.

Material failures retained:

1. Initial `assembleFields` used distinct universe levels for the two branches
   passed to `Sum.elim`; Lean rejected it with `Q : J -> Type w'` where
   `J -> Type w` was required. Both fields of the same family now share its
   universe, while source and target families remain separately polymorphic.
   No hypothesis or semantic case was changed. Exact first diagnostic is in
   `logs/check-01-failure.txt` under the scratch root.
2. Ordinary sandbox runtime self-location failed (`could not detect the
   configuration of the Lake installation`; `error: failed to locate
   application`). Task-local SYSROOT/HOME overrides did not solve it and were
   not retained. The primary supplied the known approved `require_escalated`
   invocation; the exact unmodified native toolchain then succeeded. No
   installation, global configuration edit or bypass was used.
3. A first copy command used the wrong working-directory-relative path and
   failed before executing any checker. Corrected the path and preserved the
   failure receipt with the above diagnostics.

## 4. Frozen files and ownership

Leased outputs only:

- `notes/theory/lean/YulangClosure/NativeProfileRestriction.lean`
- `notes/theory/2026-10-26-native-profile-hereditary-restriction.md`
- this handoff path.

Owned scratch root:
`/workspace/scratch/f98087c7ac1a/inference-profile-restriction`.
It contains the isolated project/cache, the copied pinned configuration,
`AuditNativeProfileRestriction.lean`, initial/final logs and source hash
manifest. No shared build/cache was written. No toolchain/config source file
was edited. The final hash scan revalidated every listed dependency and both
artifacts. All writer activity stops with publication of this handoff; no
background checker or child remains. **WRITES STOPPED.**

## 5. Independent-review seam and next original obligation

Primary owns independent review, integration, shared status and Git. Review
should check the actual annotation and whole-certificate leaf-action boundary,
that PF2's suspended-function restriction is a future-obligation restriction
rather than arbitrary world substitution, that all original field/arm/license
witnesses remain, and that the actual VB1/Name Call application removes only
its generated-profile transport premise. The Leaf is not self-approved.

The remaining concrete source/native owner must produce actual original
native-success evidence for the entire `G_call` conjunction (or consume a
supplied original full solution), with the actual independent arm and source
constructor leaves. Recursive history/operand realization remains at its
original introduction owner. No additional search for an exhaustive
certificate declaration was performed as a substitute for constructing NPR.

## 6. Exact frozen hashes

The following SHA-256 hashes identify actual bytes at freeze; historical
hashes embedded in older papers need not equal their later adoption-notice
versions. They are not a claim of Git-baseline verification by this leaf.

| File | SHA-256 |
| --- | --- |
| `notes/design/2026-10-08-native-signature-formation-definition.md` | `e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9` |
| `notes/theory/2026-10-08-source-signature-incidence-construction.md` | `7367ce8eb69376583386c6d675d067712ec6fa173e96f458ee34ce390dc8901a` |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| `notes/theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| `notes/theory/2026-10-24-native-local-profile-construction.md` | `7ca5a4a3b77fcf2f0bd0dd01b514b8920fa6de5aa955887d806416ba5f9b4e9b` |
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| `notes/theory/2026-10-08-call-semantic-input-realization.md` | `fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a` |
| `notes/theory/2026-10-24-fresh-valuebind-complete-call.md` | `6fd9926a5874ad4c419245f21a4cacf0ff7e2f00b2294b1b6657423c61a313cd` |
| `notes/theory/2026-10-24-generated-call-descriptor-typing.md` | `ef2dec5bdfaf7a8e55132cafedea1c3ced507ff19acea5189a0106d117c76e4c` |
| `notes/design/2026-10-07-complete-call-contribution-definition.md` | `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e` |
| `notes/design/2026-10-08-pure-read-call-result-constructor.md` | `8d1eb7ecea3e63d7ba0ae091dc673f3321e52fc0e31c5d824bdf4f1656b99488` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/YulangClosure/CoreComposition.lean` | `1527cd3c5961b413ec2b97495744b218aba6247956881318485364d15065294c` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `cab85ff9a8a7dc5103fe932739dcea0dfc02e6420b1277565449882c802473bd` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| `notes/theory/lean/YulangClosure/NativeProfileRestriction.lean` | `527d89b982b962e423cfaa15ecf76a2d778603102bfc9e8d12b22af2eb1c7fb2` |
| `notes/theory/2026-10-26-native-profile-hereditary-restriction.md` | `ac0138744d265056a9ca4c00037719a81de8ce5d97dc0b1607b54e0ed4f97702` |

Scratch evidence hashes:

| Path relative to scratch root | SHA-256 |
| --- | --- |
| `logs/check-final.log` | `35653cda616bfcceda6732c786168ac2c526240ebc917f3c7bfab34d332ed1e5` |
| `logs/module-audit-final.log` | `86f6611007bee85c85b7351e3e9d7b795f8218b38c9dd46365ba8d05464f6139` |
| `logs/check-01-failure.txt` | `3df5a88fe881d0e9b609da19c7a14051e3f5fe88542007a4ed5ccfe1dac1750d` |
| `project/AuditNativeProfileRestriction.lean` | `f08a9d5f680c178fc3113d436533716e440e316ba280ece9e8ff139f6f61c79f` |
| `source-and-artifact-hashes.json` | `bbf1346db84f5e0f2902dc8dac03bedace3af9cb51e4742dd84b56f37ffcfe60` |

## 7. Complete module-origin type and axiom output

```text
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.restrictSuffix_comp
@YulangClosure.NativeProfileRestriction.restrictSuffix_comp : ∀ {A : Type u_1} {A' : Type u_3} {A'' : Type u_4}
  {P : A → Type u_2} (r : A' → A) (s : A'' → A') (f : (a : A) → P a),
  YulangClosure.NativeProfileRestriction.restrictSuffix s (YulangClosure.NativeProfileRestriction.restrictSuffix r f) =
    YulangClosure.NativeProfileRestriction.restrictSuffix (fun a'' => r (s a'')) f
'YulangClosure.NativeProfileRestriction.restrictSuffix_comp' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.restrictSuffix_comp
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.appendLocal_restriction
@YulangClosure.NativeProfileRestriction.appendLocal_restriction : ∀ {W : Type u_1} {W' : Type u_4} {P : W → Type u_2}
  {P' : W' → Type u_5} {D : Type u_3} (r : W → W') (a : (x : W) → P x → P' (r x)) (defaultPolicy : D)
  (p : YulangClosure.NativeProfileRestriction.Packet P),
  YulangClosure.NativeProfileRestriction.restrictPacket r (fun x pd => (a x pd.fst, pd.snd))
      (YulangClosure.NativeProfileRestriction.appendLocal defaultPolicy p) =
    YulangClosure.NativeProfileRestriction.appendLocal defaultPolicy
      (YulangClosure.NativeProfileRestriction.restrictPacket r a p)
'YulangClosure.NativeProfileRestriction.appendLocal_restriction' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.appendLocal_restriction
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.tagged
@YulangClosure.NativeProfileRestriction.tagged : {Tag : Type u_3} →
  {W : Type u_1} →
    {P : W → Type u_2} →
      Tag → YulangClosure.NativeProfileRestriction.Packet P → Tag × YulangClosure.NativeProfileRestriction.Packet P
'YulangClosure.NativeProfileRestriction.tagged' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.tagged
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.appendLocal_policy
@YulangClosure.NativeProfileRestriction.appendLocal_policy : ∀ {W : Type u_1} {P : W → Type u_2} {D : Type u_3}
  (defaultPolicy : D) (p : YulangClosure.NativeProfileRestriction.Packet P),
  (YulangClosure.NativeProfileRestriction.appendLocal defaultPolicy p).snd.snd = defaultPolicy
'YulangClosure.NativeProfileRestriction.appendLocal_policy' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.appendLocal_policy
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.sharedFields
@YulangClosure.NativeProfileRestriction.sharedFields : {W : Type u_1} →
  {K : Type u_3} →
    {P : W → K → Type u_2} →
      (x : W) → ((k : K) → P x k) → YulangClosure.NativeProfileRestriction.Packet fun x => (k : K) → P x k
'YulangClosure.NativeProfileRestriction.sharedFields' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.sharedFields
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.restrictPacket.match_1
@YulangClosure.NativeProfileRestriction.restrictPacket.match_1 : {W : Type u_1} →
  {P : W → Type u_2} →
    (motive : YulangClosure.NativeProfileRestriction.Packet P → Sort u_3) →
      (x : YulangClosure.NativeProfileRestriction.Packet P) → ((w : W) → (p : P w) → motive ⟨w, p⟩) → motive x
'YulangClosure.NativeProfileRestriction.restrictPacket.match_1' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.restrictPacket.match_1
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.assembleFields_restriction
@YulangClosure.NativeProfileRestriction.assembleFields_restriction : ∀ {I : Type u_1} {J : Type u_2} {P : I → Type u_3}
  {Q : J → Type u_3} {P' : I → Type u_4} {Q' : J → Type u_4} (a : (i : I) → P i → P' i) (b : (j : J) → Q j → Q' j)
  (inherited : (i : I) → P i) (localFields : (j : J) → Q j) (k : I ⊕ J),
  YulangClosure.NativeProfileRestriction.assembleFields (fun i => a i (inherited i)) (fun j => b j (localFields j)) k =
    match k with
    | Sum.inl i => a i (YulangClosure.NativeProfileRestriction.assembleFields inherited localFields (Sum.inl i))
    | Sum.inr j => b j (YulangClosure.NativeProfileRestriction.assembleFields inherited localFields (Sum.inr j))
'YulangClosure.NativeProfileRestriction.assembleFields_restriction' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.assembleFields_restriction
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.valueBind_profile_restriction
@YulangClosure.NativeProfileRestriction.valueBind_profile_restriction : ∀ {W : Type u_1} {W' : Type u_4}
  {Old : W → Type u_2} {Old' : W' → Type u_5} {New : W → Type u_3} {New' : W' → Type u_6} {D : Type u_7} (r : W → W')
  (oldAct : (x : W) → Old x → Old' (r x)) (newAct : (x : W) → New x → New' (r x)) (defaultPolicy : D) (x : W)
  (old : Old x) (new : New x),
  YulangClosure.NativeProfileRestriction.restrictPacket r (fun x p => ((oldAct x p.fst.fst, newAct x p.fst.snd), p.snd))
      (YulangClosure.NativeProfileRestriction.appendLocal defaultPolicy
        (YulangClosure.NativeProfileRestriction.sharedPair x old new)) =
    YulangClosure.NativeProfileRestriction.appendLocal defaultPolicy
      (YulangClosure.NativeProfileRestriction.sharedPair (r x) (oldAct x old) (newAct x new))
'YulangClosure.NativeProfileRestriction.valueBind_profile_restriction' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.valueBind_profile_restriction
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.dependentBind_restriction
@YulangClosure.NativeProfileRestriction.dependentBind_restriction : ∀ {W : Type u_1} {W' : Type u_4} {B : W → Type u_2}
  {B' : W' → Type u_5} {P : (x : W) → B x → Type u_3} {P' : (x : W') → B' x → Type u_6} (r : W → W')
  (middle : (x : W) → B x → B' (r x)) (a : (x : W) → (b : B x) → P x b → P' (r x) (middle x b)) (x : W) (b : B x)
  (p : P x b),
  YulangClosure.NativeProfileRestriction.restrictPacket r (fun x bp => ⟨middle x bp.fst, a x bp.fst bp.snd⟩)
      (YulangClosure.NativeProfileRestriction.dependentBind x b p) =
    YulangClosure.NativeProfileRestriction.dependentBind (r x) (middle x b) (a x b p)
'YulangClosure.NativeProfileRestriction.dependentBind_restriction' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.dependentBind_restriction
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.Packet
@YulangClosure.NativeProfileRestriction.Packet : {W : Type u_1} → (W → Type u_2) → Type (max u_1 u_2)
'YulangClosure.NativeProfileRestriction.Packet' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.Packet
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.restrictPacket_comp
@YulangClosure.NativeProfileRestriction.restrictPacket_comp : ∀ {W : Type u_1} {W' : Type u_3} {W'' : Type u_5}
  {P : W → Type u_2} {P' : W' → Type u_4} {P'' : W'' → Type u_6} (r : W → W') (a : (w : W) → P w → P' (r w))
  (s : W' → W'') (b : (w : W') → P' w → P'' (s w)) (p : YulangClosure.NativeProfileRestriction.Packet P),
  YulangClosure.NativeProfileRestriction.restrictPacket s b
      (YulangClosure.NativeProfileRestriction.restrictPacket r a p) =
    YulangClosure.NativeProfileRestriction.restrictPacket (fun w => s (r w)) (fun w x => b (r w) (a w x)) p
'YulangClosure.NativeProfileRestriction.restrictPacket_comp' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.restrictPacket_comp
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.restrictAlternative_left
@YulangClosure.NativeProfileRestriction.restrictAlternative_left : ∀ {P : Type u_1} {Q : Type u_2} {P' : Type u_3}
  {Q' : Type u_4} (a : P → P') (b : Q → Q') (p : P),
  YulangClosure.NativeProfileRestriction.restrictAlternative a b (Sum.inl p) = Sum.inl (a p)
'YulangClosure.NativeProfileRestriction.restrictAlternative_left' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.restrictAlternative_left
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.restrictPacket_mk
@YulangClosure.NativeProfileRestriction.restrictPacket_mk : ∀ {W : Type u_1} {W' : Type u_3} {P : W → Type u_2}
  {P' : W' → Type u_4} (r : W → W') (a : (w : W) → P w → P' (r w)) (w : W) (p : P w),
  YulangClosure.NativeProfileRestriction.restrictPacket r a ⟨w, p⟩ = ⟨r w, a w p⟩
'YulangClosure.NativeProfileRestriction.restrictPacket_mk' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.restrictPacket_mk
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.restrictSuffix
@YulangClosure.NativeProfileRestriction.restrictSuffix : {A : Type u_1} →
  {A' : Type u_3} → {P : A → Type u_2} → (r : A' → A) → ((a : A) → P a) → (a' : A') → P (r a')
'YulangClosure.NativeProfileRestriction.restrictSuffix' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.restrictSuffix
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.dependentBind_middle
@YulangClosure.NativeProfileRestriction.dependentBind_middle : ∀ {W : Type u_1} {B : W → Type u_2}
  {P : (x : W) → B x → Type u_3} (x : W) (b : B x) (p : P x b),
  (YulangClosure.NativeProfileRestriction.dependentBind x b p).snd.fst = b
'YulangClosure.NativeProfileRestriction.dependentBind_middle' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.dependentBind_middle
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.dependentBind
@YulangClosure.NativeProfileRestriction.dependentBind : {W : Type u_1} →
  {B : W → Type u_2} →
    {P : (x : W) → B x → Type u_3} →
      (x : W) → (b : B x) → P x b → YulangClosure.NativeProfileRestriction.Packet fun x => Sigma (P x)
'YulangClosure.NativeProfileRestriction.dependentBind' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.dependentBind
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.restrictPacket
@YulangClosure.NativeProfileRestriction.restrictPacket : {W : Type u_1} →
  {W' : Type u_3} →
    {P : W → Type u_2} →
      {P' : W' → Type u_4} →
        (r : W → W') →
          ((w : W) → P w → P' (r w)) →
            YulangClosure.NativeProfileRestriction.Packet P → YulangClosure.NativeProfileRestriction.Packet P'
'YulangClosure.NativeProfileRestriction.restrictPacket' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.restrictPacket
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.appendLocal
@YulangClosure.NativeProfileRestriction.appendLocal : {W : Type u_1} →
  {P : W → Type u_2} →
    {D : Type u_3} →
      D →
        YulangClosure.NativeProfileRestriction.Packet P → YulangClosure.NativeProfileRestriction.Packet fun x => P x × D
'YulangClosure.NativeProfileRestriction.appendLocal' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.appendLocal
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.appendLocal_original
@YulangClosure.NativeProfileRestriction.appendLocal_original : ∀ {W : Type u_1} {P : W → Type u_2} {D : Type u_3}
  (defaultPolicy : D) (p : YulangClosure.NativeProfileRestriction.Packet P),
  ⟨(YulangClosure.NativeProfileRestriction.appendLocal defaultPolicy p).fst,
      (YulangClosure.NativeProfileRestriction.appendLocal defaultPolicy p).snd.fst⟩ =
    p
'YulangClosure.NativeProfileRestriction.appendLocal_original' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.appendLocal_original
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.restrictAlternative
@YulangClosure.NativeProfileRestriction.restrictAlternative : {P : Type u_1} →
  {Q : Type u_2} → {P' : Type u_3} → {Q' : Type u_4} → (P → P') → (Q → Q') → P ⊕ Q → P' ⊕ Q'
'YulangClosure.NativeProfileRestriction.restrictAlternative' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.restrictAlternative
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.sharedFields_restriction
@YulangClosure.NativeProfileRestriction.sharedFields_restriction : ∀ {W : Type u_1} {W' : Type u_4} {K : Type u_3}
  {P : W → K → Type u_2} {P' : W' → K → Type u_5} (r : W → W') (a : (x : W) → (k : K) → P x k → P' (r x) k) (x : W)
  (p : (k : K) → P x k),
  YulangClosure.NativeProfileRestriction.restrictPacket r (fun x ps k => a x k (ps k))
      (YulangClosure.NativeProfileRestriction.sharedFields x p) =
    YulangClosure.NativeProfileRestriction.sharedFields (r x) fun k => a x k (p k)
'YulangClosure.NativeProfileRestriction.sharedFields_restriction' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.sharedFields_restriction
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.restrictAlternative_right
@YulangClosure.NativeProfileRestriction.restrictAlternative_right : ∀ {P : Type u_1} {Q : Type u_2} {P' : Type u_3}
  {Q' : Type u_4} (a : P → P') (b : Q → Q') (q : Q),
  YulangClosure.NativeProfileRestriction.restrictAlternative a b (Sum.inr q) = Sum.inr (b q)
'YulangClosure.NativeProfileRestriction.restrictAlternative_right' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.restrictAlternative_right
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.assembleFields
@YulangClosure.NativeProfileRestriction.assembleFields : {I : Type u_1} →
  {J : Type u_2} →
    {P : I → Type u_3} → {Q : J → Type u_3} → ((i : I) → P i) → ((j : J) → Q j) → (k : I ⊕ J) → Sum.elim P Q k
'YulangClosure.NativeProfileRestriction.assembleFields' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.assembleFields
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.assembleFields_local
@YulangClosure.NativeProfileRestriction.assembleFields_local : ∀ {I : Type u_1} {J : Type u_2} {P : I → Type u_3}
  {Q : J → Type u_3} (inherited : (i : I) → P i) (localFields : (j : J) → Q j) (j : J),
  YulangClosure.NativeProfileRestriction.assembleFields inherited localFields (Sum.inr j) = localFields j
'YulangClosure.NativeProfileRestriction.assembleFields_local' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.assembleFields_local
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.assembleFields_inherited
@YulangClosure.NativeProfileRestriction.assembleFields_inherited : ∀ {I : Type u_1} {J : Type u_2} {P : I → Type u_3}
  {Q : J → Type u_3} (inherited : (i : I) → P i) (localFields : (j : J) → Q j) (i : I),
  YulangClosure.NativeProfileRestriction.assembleFields inherited localFields (Sum.inl i) = inherited i
'YulangClosure.NativeProfileRestriction.assembleFields_inherited' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.assembleFields_inherited
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.tagged_restriction
@YulangClosure.NativeProfileRestriction.tagged_restriction : ∀ {Tag : Type u_3} {Tag' : Type u_6} {W : Type u_1}
  {W' : Type u_4} {P : W → Type u_2} {P' : W' → Type u_5} (tagMap : Tag → Tag') (r : W → W')
  (a : (w : W) → P w → P' (r w)) (t : Tag) (p : YulangClosure.NativeProfileRestriction.Packet P),
  Prod.map tagMap (YulangClosure.NativeProfileRestriction.restrictPacket r a)
      (YulangClosure.NativeProfileRestriction.tagged t p) =
    YulangClosure.NativeProfileRestriction.tagged (tagMap t)
      (YulangClosure.NativeProfileRestriction.restrictPacket r a p)
'YulangClosure.NativeProfileRestriction.tagged_restriction' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.tagged_restriction
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.sharedPair
@YulangClosure.NativeProfileRestriction.sharedPair : {W : Type u_1} →
  {P : W → Type u_2} →
    {Q : W → Type u_3} → (x : W) → P x → Q x → YulangClosure.NativeProfileRestriction.Packet fun x => P x × Q x
'YulangClosure.NativeProfileRestriction.sharedPair' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.sharedPair
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.tagged_projection
@YulangClosure.NativeProfileRestriction.tagged_projection : ∀ {Tag : Type u_3} {W : Type u_1} {P : W → Type u_2}
  (t : Tag) (p : YulangClosure.NativeProfileRestriction.Packet P),
  (YulangClosure.NativeProfileRestriction.tagged t p).snd = p
'YulangClosure.NativeProfileRestriction.tagged_projection' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.tagged_projection
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.restrictAlternative.match_1
@YulangClosure.NativeProfileRestriction.restrictAlternative.match_1 : {P : Type u_1} →
  {Q : Type u_2} →
    (motive : P ⊕ Q → Sort u_3) →
      (x : P ⊕ Q) → ((p : P) → motive (Sum.inl p)) → ((q : Q) → motive (Sum.inr q)) → motive x
'YulangClosure.NativeProfileRestriction.restrictAlternative.match_1' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.restrictAlternative.match_1
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.sharedPair_restriction
@YulangClosure.NativeProfileRestriction.sharedPair_restriction : ∀ {W : Type u_1} {W' : Type u_4} {P : W → Type u_2}
  {P' : W' → Type u_5} {Q : W → Type u_3} {Q' : W' → Type u_6} (r : W → W') (a : (x : W) → P x → P' (r x))
  (b : (x : W) → Q x → Q' (r x)) (x : W) (p : P x) (q : Q x),
  YulangClosure.NativeProfileRestriction.restrictPacket r (fun x pq => (a x pq.fst, b x pq.snd))
      (YulangClosure.NativeProfileRestriction.sharedPair x p q) =
    YulangClosure.NativeProfileRestriction.sharedPair (r x) (a x p) (b x q)
'YulangClosure.NativeProfileRestriction.sharedPair_restriction' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.sharedPair_restriction
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.restrictPacket_tuple
@YulangClosure.NativeProfileRestriction.restrictPacket_tuple : ∀ {W : Type u_1} {W' : Type u_3} {P : W → Type u_2}
  {P' : W' → Type u_4} (r : W → W') (a : (w : W) → P w → P' (r w))
  (p : YulangClosure.NativeProfileRestriction.Packet P),
  (YulangClosure.NativeProfileRestriction.restrictPacket r a p).fst = r p.fst
'YulangClosure.NativeProfileRestriction.restrictPacket_tuple' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.restrictPacket_tuple
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.restrictPacket_identity
@YulangClosure.NativeProfileRestriction.restrictPacket_identity : ∀ {W : Type u_1} {P : W → Type u_2}
  (p : YulangClosure.NativeProfileRestriction.Packet P),
  YulangClosure.NativeProfileRestriction.restrictPacket id (fun x x_1 => x_1) p = p
'YulangClosure.NativeProfileRestriction.restrictPacket_identity' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.restrictPacket_identity
PROFILE_AUDIT_BEGIN YulangClosure.NativeProfileRestriction.restrictSuffix_apply
@YulangClosure.NativeProfileRestriction.restrictSuffix_apply : ∀ {A : Type u_1} {A' : Type u_3} {P : A → Type u_2}
  (r : A' → A) (f : (a : A) → P a) (a' : A'), YulangClosure.NativeProfileRestriction.restrictSuffix r f a' = f (r a')
'YulangClosure.NativeProfileRestriction.restrictSuffix_apply' does not depend on any axioms
PROFILE_AUDIT_END YulangClosure.NativeProfileRestriction.restrictSuffix_apply
PROFILE_AUDIT_MODULE YulangClosure.NativeProfileRestriction
PROFILE_AUDIT_DECLARATIONS 33
PROFILE_AUDIT_THEOREMS 21
```
