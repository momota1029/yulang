# R170 frozen R169 verification receipt

Worker: `/root/formal_entry_r170_verify`; exact read-only verification lane.
Status: **KERNEL CHECK AND 18 AUDITS PASSED; INDEPENDENT REVIEW PENDING**.
Only write: this handoff. No scratch, source edits, build, checker helper, dependency changes, children or Git mutations.

## Frozen source and authority

Module: `notes/theory/lean/YulangClosure/FormalEntryPrestateBridgeR169.lean`.
SHA-256 before and after: `bb0aaffe95f99881b089807a202991c4349a7c61e9ebb0f42f56d7f080a7baf4` / `bb0aaffe95f99881b089807a202991c4349a7c61e9ebb0f42f56d7f080a7baf4`.
R169 handoff SHA-256: `b08ac4ac3a566802084dba43cb72dfebed3ca72eac2f3e03ad7943692d1fdc61`.
The R170 contract and R169 outcome were read; R169 earlier two failed checks are retained in the prior handoff and are not replaced by this receipt.

Original parent: `YulangClosure.SourceProblem.InferenceSoundness`, `Contracts.lean:127`: for every supported `s`, original `x`, generated `d`, solved `a`, one shared `e` satisfying `sourceJudgment s x e ∧ sameScoped s x e a`. This remains a proposition definition with no concrete source instance established here.
Read original claim in `docs/yulang-whole-proof-closure-ja.md` §1 and `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1–3; read opening source-owner/resume corrections in both source and operational type-safety manuscripts; read authoritative annotation-effect policy §1–1.2 and inference top-level principles. Manuscripts and this finite transcription do not adopt semantics.


Read-only source SHA-256s:

- `docs/yulang-whole-proof-closure-ja.md`: `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5`.
- `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`: `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`.
- `docs/yulang-operational-type-safety-ja.tex`: `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
- `docs/yulang-source-type-safety-ja.tex`: `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`.
- `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`: `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`.
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md`: `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
- `notes/theory/lean/YulangClosure/Contracts.lean`: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`.

Source supplement: `rg -n 'sorry|admit|axiom|skipKernelTC|native_decide|implemented_by|unsafe'` over the exact R169 module and its ten-module cone exited 0; inspected matches were comments containing admitted/axiom and existing R116 `#print axioms` commands. No actual hole, project axiom, bypass, native_decide or unsafe declaration matched. This source search is supplemental to the transitive audit.

## Import authentication before any Lean command

Direct import: `YulangClosure.SuppressionPermissionR116`. All ten project sources matched frozen R169 SHA-256s. Every source byte sequence recomputed to its trace input hash after CRLF normalization; every existing olean byte sequence recomputed to both its `.olean.hash` and trace output hash. Every trace names Lean 4.35.0 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc and the same project arguments. The installed runtime hash primitives were loaded read-only with ctypes and applied to in-memory byte/string structures described in pinned lean.h; Lake Hash.ofHashable mix is from pinned Lake/Build/Trace.lean and lean_uint64_mix_hash.
Hash runtime `libleanshared.so` SHA-256: `efef27df56f2197139afe12f1a2b63913a05f1aba81ce88824c44100431ed8c4`.
Project lean-toolchain/lakefile.toml/lake-manifest.json hashes matched the R169 handoff. Empty manifest packages and TOML loader avoid generated lakefile outputs. Inspected pinned Lake.Load.Package.loadConfigFile, Lake.Load.Toml.loadTomlConfig, Lake.Load.Workspace.loadWorkspace, Workspace.materializeDeps, CLI Main env, and Lean Shell stdin/output defaults before execution. No build/output options are passed.

```json
[
  {
    "module": "YulangClosure.AuthenticatedResidualConsumerR49",
    "source_sha256": "4fc4380f3ad1827ecf155f982e5186b32d6d66d91909039fb118063d8f1e2df2",
    "source_trace_hash": "9e5830b41bb2c530",
    "olean_sha256": "2ec911490c13ce611284965c94e2cb30fc2313faea7b312aa14ba7044d6627db",
    "olean_trace_hash": "62ae7e0ea8a57d39",
    "trace_sha256": "6a9729a8afbb6b53741a56a4a118e29ab7a1b7fd7aa67557bba2c530f552f0f1"
  },
  {
    "module": "YulangClosure.ComputationPermissionEntryR39",
    "source_sha256": "748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e",
    "source_trace_hash": "b63d4294b527f1e1",
    "olean_sha256": "e6efb347db05a8171236d03187cd5da601d81abe56fd1a30c3e9e8f7c9f97489",
    "olean_trace_hash": "255a584c844384db",
    "trace_sha256": "9ee7b62a4dffbf06fccc63fecc45813815d088b94ca53ac7849555e6d16c4cd1"
  },
  {
    "module": "YulangClosure.CurrentEmissionOwnershipR47",
    "source_sha256": "d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c",
    "source_trace_hash": "0799c249ecf5bac7",
    "olean_sha256": "e6a188912d9e8d361e0084b7dc90a0e4e11d8e1ad948a01db3c411a1dec6faa6",
    "olean_trace_hash": "75e54b9c9d11b774",
    "trace_sha256": "172ca0d741d01aa7ea645d176406353292a3756f875779889455c6c351c3c6de"
  },
  {
    "module": "YulangClosure.InternalPermissionIncidenceR45",
    "source_sha256": "9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f",
    "source_trace_hash": "32cdd0fe8e9b3ea0",
    "olean_sha256": "5da13590e510800915da32888c2490a7b9d5d1a80b9e4f266a777d65878f10c8",
    "olean_trace_hash": "d5e1b6e5d0304f49",
    "trace_sha256": "d7929e36b8b97c8edcd41bf5ba3e6cc742207038d7125beaaa608513dee846be"
  },
  {
    "module": "YulangClosure.NativeResidualPublicationR51",
    "source_sha256": "78a729b25e95812ba292c4e625ec69e46ff5eb70ff3ac2ae5b85dd1b33214d61",
    "source_trace_hash": "a4f7c4f1d3613962",
    "olean_sha256": "ba3b93f84e5b5bca6de1c240cba1c5692241b36090797b0fd38559e06f2e4a35",
    "olean_trace_hash": "8070fda240bbdaf5",
    "trace_sha256": "6841f95d64bbb7fa23c3ba6913a601eb4a26a63d1810288e3c83a5224ca7fdd0"
  },
  {
    "module": "YulangClosure.OwnedResidualProjectionR54",
    "source_sha256": "cc5d0b01485560e5091ce454b066ca2fc41eb350eee24ae525133a13bed401c9",
    "source_trace_hash": "4383a1c667636605",
    "olean_sha256": "89cc437745c68776c837133227a5f08bf866633da1f66f7455d7fadf6964a42a",
    "olean_trace_hash": "238b65ed9a2a4f1b",
    "trace_sha256": "b0a44fee339b570f5f9c92a2bfe92acff5e5eacf3d3c55bbfdf949ef49b720f5"
  },
  {
    "module": "YulangClosure.PerCallResidualPublicationR52",
    "source_sha256": "d0ffaad36139148c3898d70c9da2e03d1b0e17cbb8b71841f751a8720570e73e",
    "source_trace_hash": "dd8967765451c9a6",
    "olean_sha256": "640cc877c1266662ff47d13f9707e2bfed7b06d966750cecf7723a8d4e68e464",
    "olean_trace_hash": "4944366f9be8f817",
    "trace_sha256": "30ff80b4d0709852e488c1e6044f631f710b285416d17db47e13d0512025435c"
  },
  {
    "module": "YulangClosure.ProviderEntryArrivalR48",
    "source_sha256": "b85dfad5c0e80f7fbc2480e7f38421cc6c50107144d9abb160e688208b192575",
    "source_trace_hash": "24eb86a31d8ccc7f",
    "olean_sha256": "10563346e3630ac3470d31547e896192ccfbb47c99cd6c3b2d4f1ed7307052aa",
    "olean_trace_hash": "4ce600da5832739f",
    "trace_sha256": "0132d4de88689616fb4b93a0b7dfe6c28df15a938f0c327e703d55debc3870a8"
  },
  {
    "module": "YulangClosure.SuppressionPermissionR116",
    "source_sha256": "2aed350468964d90d8d83714177fff77d477e3df0846ae23150194bd76270e3a",
    "source_trace_hash": "f1627e55d503c891",
    "olean_sha256": "c31c0274523ac3068cf6d1bb87c767560b0b5e31d7f6566267f2833574238c15",
    "olean_trace_hash": "d7b1a26e193e633c",
    "trace_sha256": "acc9a397a33da80f194a6887d809b4839a697b92d7f90a6ac8babb0808394f7b"
  },
  {
    "module": "YulangClosure.WholePublicationResidualR53",
    "source_sha256": "dc9c89e562f905c2c6284fd15eb82e9482a82bc9b2881f567c3454198318f391",
    "source_trace_hash": "9d4b84a0ea893366",
    "olean_sha256": "a704c5771e8edcf4d68689f4b696bfddafc389fa67d4e799705358e0963ddc74",
    "olean_trace_hash": "bc6f829a42b79380",
    "trace_sha256": "af7603f65417b6574b1c7b261a05eb8859770feec190d649c4ed253158204009"
  }
]
```

## Commands, complete stdout and stderr

All commands run in `notes/theory/lean`; LEAN_NUM_THREADS=1. Python parent used `python3 -B` with subprocess pipes; the audit stream was exact frozen module bytes followed by the below commands, with no temporary file. The helper was prohibited because it materializes outputs. One audit invocation only.
Audit stream SHA-256: `8be509865bbaa47a37f6c01d663480d7d0b5d42ef4d5312fd8c3fa4a06d38a71`; module bytes 22844; appended bytes 2815.

```lean
#check @YulangClosure.FormalEntryPrestateBridgeR169.erased_source_read
#print axioms YulangClosure.FormalEntryPrestateBridgeR169.erased_source_read
#check @YulangClosure.FormalEntryPrestateBridgeR169.collected_parameter_payload
#print axioms YulangClosure.FormalEntryPrestateBridgeR169.collected_parameter_payload
#check @YulangClosure.FormalEntryPrestateBridgeR169.entry_prepared
#print axioms YulangClosure.FormalEntryPrestateBridgeR169.entry_prepared
#check @YulangClosure.FormalEntryPrestateBridgeR169.copied_exact
#print axioms YulangClosure.FormalEntryPrestateBridgeR169.copied_exact
#check @YulangClosure.FormalEntryPrestateBridgeR169.linked_exact
#print axioms YulangClosure.FormalEntryPrestateBridgeR169.linked_exact
#check @YulangClosure.FormalEntryPrestateBridgeR169.published_exact
#print axioms YulangClosure.FormalEntryPrestateBridgeR169.published_exact
#check @YulangClosure.FormalEntryPrestateBridgeR169.successful_nonempty
#print axioms YulangClosure.FormalEntryPrestateBridgeR169.successful_nonempty
#check @YulangClosure.FormalEntryPrestateBridgeR169.successful_empty
#print axioms YulangClosure.FormalEntryPrestateBridgeR169.successful_empty
#check @YulangClosure.FormalEntryPrestateBridgeR169.duplicate_guard_derived
#print axioms YulangClosure.FormalEntryPrestateBridgeR169.duplicate_guard_derived
#check @YulangClosure.FormalEntryPrestateBridgeR169.retained_input_rejected
#print axioms YulangClosure.FormalEntryPrestateBridgeR169.retained_input_rejected
#check @YulangClosure.FormalEntryPrestateBridgeR169.malformed_input_rejected
#print axioms YulangClosure.FormalEntryPrestateBridgeR169.malformed_input_rejected
#check @YulangClosure.FormalEntryPrestateBridgeR169.sample_error_changed_state
#print axioms YulangClosure.FormalEntryPrestateBridgeR169.sample_error_changed_state
#check @YulangClosure.FormalEntryPrestateBridgeR169.selected_endpoint_application
#print axioms YulangClosure.FormalEntryPrestateBridgeR169.selected_endpoint_application
#check @YulangClosure.FormalEntryPrestateBridgeR169.duplicate_order_preserved
#print axioms YulangClosure.FormalEntryPrestateBridgeR169.duplicate_order_preserved
#check @YulangClosure.FormalEntryPrestateBridgeR169.finite_entry_example
#print axioms YulangClosure.FormalEntryPrestateBridgeR169.finite_entry_example
#check @YulangClosure.FormalEntryPrestateBridgeR169.finite_symbolic_publication_example
#print axioms YulangClosure.FormalEntryPrestateBridgeR169.finite_symbolic_publication_example
#check @YulangClosure.FormalEntryPrestateBridgeR169.finite_symbolic_success_and_error_example
#print axioms YulangClosure.FormalEntryPrestateBridgeR169.finite_symbolic_success_and_error_example
#check @YulangClosure.FormalEntryPrestateBridgeR169.finite_empty_example
#print axioms YulangClosure.FormalEntryPrestateBridgeR169.finite_empty_example
```

Command argv: `["/home/momota1029/.elan/bin/elan", "which", "lake"]`
Exit: 0; elapsed seconds: 0.027151.
stdout:
```text
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake

```
stderr:
```text

```

Command argv: `["/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake", "--version"]`
Exit: 0; elapsed seconds: 0.414277.
stdout:
```text
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)

```
stderr:
```text

```

Command argv: `["/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake", "env", "lean", "--version"]`
Exit: 0; elapsed seconds: 0.075116.
stdout:
```text
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)

```
stderr:
```text

```

Command argv: `["/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake", "env", "lean", "-j1", "-M1024", "--stdin"]`
Exit: 0; elapsed seconds: 4.660547.
stdout:
```text
@YulangClosure.FormalEntryPrestateBridgeR169.erased_source_read : ∀ {Id : Type} [inst : DecidableEq Id]
  (sources : List (Id × List (YulangClosure.FormalEntryPrestateBridgeR169.Expression Id))) (owner : Id),
  YulangClosure.ComputationPermissionEntryR39.localSource
      (YulangClosure.FormalEntryPrestateBridgeR169.eraseSources sources) owner =
    Option.map (List.map YulangClosure.FormalEntryPrestateBridgeR169.eraseExpression)
      (YulangClosure.FormalEntryPrestateBridgeR169.readSource sources owner)
'YulangClosure.FormalEntryPrestateBridgeR169.erased_source_read' depends on axioms: [propext]
@YulangClosure.FormalEntryPrestateBridgeR169.collected_parameter_payload : ∀ {Id : Type} [inst : DecidableEq Id]
  (x : YulangClosure.FormalEntryPrestateBridgeR169.Raw Id) (a : YulangClosure.ComputationPermissionEntryR39.Action Id),
  YulangClosure.FormalEntryPrestateBridgeR169.Collected x a →
    ∃ owner index expressions parameter formal,
      YulangClosure.FormalEntryPrestateBridgeR169.readSource x.sources owner = some expressions ∧
        expressions[index]? =
            some (YulangClosure.FormalEntryPrestateBridgeR169.Expression.lambda a.occurrence parameter) ∧
          parameter.annotation = some a.annotation ∧
            YulangClosure.FormalEntryPrestateBridgeR169.readRegistration x.formalRegistrations parameter.id =
                some a.registration ∧
              x.formals[a.registration]? = some formal ∧ a.scope = formal.scope
'YulangClosure.FormalEntryPrestateBridgeR169.collected_parameter_payload' depends on axioms: [propext]
@YulangClosure.FormalEntryPrestateBridgeR169.entry_prepared : ∀ {Id : Type} [inst : DecidableEq Id]
  (x : YulangClosure.FormalEntryPrestateBridgeR169.Raw Id) (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port : Id),
  YulangClosure.FormalEntryPrestateBridgeR169.Trace x a
      (YulangClosure.FormalEntryPrestateBridgeR169.Phase.entry f r port) x.before →
    YulangClosure.ComputationPermissionEntryR39.prepare (YulangClosure.FormalEntryPrestateBridgeR169.inputs x) a =
      some (f, r, port)
'YulangClosure.FormalEntryPrestateBridgeR169.entry_prepared' depends on axioms: [propext, Quot.sound]
@YulangClosure.FormalEntryPrestateBridgeR169.copied_exact : ∀ {Id : Type} [inst : DecidableEq Id]
  (x : YulangClosure.FormalEntryPrestateBridgeR169.Raw Id) (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port : Id)
  (pending : Option (YulangClosure.ComputationPermissionEntryR39.Permission Id)),
  YulangClosure.FormalEntryPrestateBridgeR169.Trace x a
      (YulangClosure.FormalEntryPrestateBridgeR169.Phase.copied f r port pending) x.before →
    YulangClosure.ComputationPermissionEntryR39.prepare (YulangClosure.FormalEntryPrestateBridgeR169.inputs x) a =
        some (f, r, port) ∧
      pending = YulangClosure.ComputationPermissionEntryR39.permissionFor a f r port
'YulangClosure.FormalEntryPrestateBridgeR169.copied_exact' depends on axioms: [propext, Quot.sound]
@YulangClosure.FormalEntryPrestateBridgeR169.linked_exact : ∀ {Id : Type} [inst : DecidableEq Id]
  (x : YulangClosure.FormalEntryPrestateBridgeR169.Raw Id) (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port : Id)
  (pending : Option (YulangClosure.ComputationPermissionEntryR39.Permission Id))
  (after : YulangClosure.ComputationPermissionEntryR39.State Id),
  YulangClosure.FormalEntryPrestateBridgeR169.Trace x a
      (YulangClosure.FormalEntryPrestateBridgeR169.Phase.linked f r port pending) after →
    YulangClosure.ComputationPermissionEntryR39.prepare (YulangClosure.FormalEntryPrestateBridgeR169.inputs x) a =
        some (f, r, port) ∧
      pending = YulangClosure.ComputationPermissionEntryR39.permissionFor a f r port ∧
        after =
          { permissions := x.before.permissions,
            links := x.before.links ++ YulangClosure.ComputationPermissionEntryR39.symbolicLinks a r port,
            inflow := x.before.inflow }
'YulangClosure.FormalEntryPrestateBridgeR169.linked_exact' depends on axioms: [propext, Quot.sound]
@YulangClosure.FormalEntryPrestateBridgeR169.published_exact : ∀ {Id : Type} [inst : DecidableEq Id]
  (x : YulangClosure.FormalEntryPrestateBridgeR169.Raw Id) (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port : Id)
  (pending : Option (YulangClosure.ComputationPermissionEntryR39.Permission Id))
  (after : YulangClosure.ComputationPermissionEntryR39.State Id),
  YulangClosure.FormalEntryPrestateBridgeR169.Trace x a
      (YulangClosure.FormalEntryPrestateBridgeR169.Phase.published f r port pending) after →
    YulangClosure.ComputationPermissionEntryR39.prepare (YulangClosure.FormalEntryPrestateBridgeR169.inputs x) a =
        some (f, r, port) ∧
      pending = YulangClosure.ComputationPermissionEntryR39.permissionFor a f r port ∧
        after =
          { permissions := x.before.permissions ++ pending.toList,
            links := x.before.links ++ YulangClosure.ComputationPermissionEntryR39.symbolicLinks a r port,
            inflow := x.before.inflow }
'YulangClosure.FormalEntryPrestateBridgeR169.published_exact' depends on axioms: [propext, Quot.sound]
@YulangClosure.FormalEntryPrestateBridgeR169.successful_nonempty : ∀ {Id : Type} [inst : DecidableEq Id]
  (x : YulangClosure.FormalEntryPrestateBridgeR169.Raw Id) (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port : Id)
  (pending : Option (YulangClosure.ComputationPermissionEntryR39.Permission Id))
  (after : YulangClosure.ComputationPermissionEntryR39.State Id),
  YulangClosure.FormalEntryPrestateBridgeR169.Trace x a
      (YulangClosure.FormalEntryPrestateBridgeR169.Phase.ok f r port pending) after →
    r.concrete ≠ [] →
      ∃ p,
        YulangClosure.ComputationPermissionEntryR39.prepare (YulangClosure.FormalEntryPrestateBridgeR169.inputs x) a =
            some (f, r, port) ∧
          YulangClosure.ComputationPermissionEntryR39.permissionFor a f r port = some p ∧
            pending = some p ∧
              after =
                  { permissions := x.before.permissions ++ [p],
                    links := x.before.links ++ YulangClosure.ComputationPermissionEntryR39.symbolicLinks a r port,
                    inflow := x.before.inflow } ∧
                p.concrete = r.concrete
'YulangClosure.FormalEntryPrestateBridgeR169.successful_nonempty' depends on axioms: [propext, Quot.sound]
@YulangClosure.FormalEntryPrestateBridgeR169.successful_empty : ∀ {Id : Type} [inst : DecidableEq Id]
  (x : YulangClosure.FormalEntryPrestateBridgeR169.Raw Id) (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port : Id)
  (pending : Option (YulangClosure.ComputationPermissionEntryR39.Permission Id))
  (after : YulangClosure.ComputationPermissionEntryR39.State Id),
  YulangClosure.FormalEntryPrestateBridgeR169.Trace x a
      (YulangClosure.FormalEntryPrestateBridgeR169.Phase.ok f r port pending) after →
    r.concrete = [] →
      YulangClosure.ComputationPermissionEntryR39.prepare (YulangClosure.FormalEntryPrestateBridgeR169.inputs x) a =
          some (f, r, port) ∧
        YulangClosure.ComputationPermissionEntryR39.permissionFor a f r port = none ∧
          pending = none ∧ after.permissions = x.before.permissions
'YulangClosure.FormalEntryPrestateBridgeR169.successful_empty' depends on axioms: [propext, Quot.sound]
@YulangClosure.FormalEntryPrestateBridgeR169.duplicate_guard_derived : ∀ {Id : Type} [inst : DecidableEq Id]
  (x : YulangClosure.FormalEntryPrestateBridgeR169.Raw Id) (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port : Id),
  YulangClosure.FormalEntryPrestateBridgeR169.Trace x a
      (YulangClosure.FormalEntryPrestateBridgeR169.Phase.entry f r port) x.before →
    ¬a.registration ∈ (YulangClosure.FormalEntryPrestateBridgeR169.inputs x).retainedRegistrations ∧
      ¬∃ p, p ∈ x.before.permissions ∧ p.registration = a.registration
'YulangClosure.FormalEntryPrestateBridgeR169.duplicate_guard_derived' depends on axioms: [propext, Quot.sound]
@YulangClosure.FormalEntryPrestateBridgeR169.retained_input_rejected : ∀ {Id : Type} [inst : DecidableEq Id]
  (x : YulangClosure.FormalEntryPrestateBridgeR169.Raw Id) (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id),
  x.formals[a.registration]? = some f →
    (∃ p, p ∈ x.before.permissions ∧ p.registration = a.registration) →
      YulangClosure.ComputationPermissionEntryR39.prepare (YulangClosure.FormalEntryPrestateBridgeR169.inputs x) a =
        none
'YulangClosure.FormalEntryPrestateBridgeR169.retained_input_rejected' depends on axioms: [propext, Quot.sound]
@YulangClosure.FormalEntryPrestateBridgeR169.malformed_input_rejected : ∀ {Id : Type} [inst : DecidableEq Id]
  (x : YulangClosure.FormalEntryPrestateBridgeR169.Raw Id) (a : YulangClosure.ComputationPermissionEntryR39.Action Id),
  a.annotation.row = none ∨ x.formals[a.registration]? = none →
    YulangClosure.ComputationPermissionEntryR39.prepare (YulangClosure.FormalEntryPrestateBridgeR169.inputs x) a = none
'YulangClosure.FormalEntryPrestateBridgeR169.malformed_input_rejected' depends on axioms: [propext, Quot.sound]
@YulangClosure.FormalEntryPrestateBridgeR169.sample_error_changed_state : ∀ {Id : Type} [inst : DecidableEq Id]
  (x : YulangClosure.FormalEntryPrestateBridgeR169.Raw Id) (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port : Id)
  (pending : Option (YulangClosure.ComputationPermissionEntryR39.Permission Id))
  (after : YulangClosure.ComputationPermissionEntryR39.State Id),
  YulangClosure.FormalEntryPrestateBridgeR169.Trace x a
      (YulangClosure.FormalEntryPrestateBridgeR169.Phase.sampleError f r port pending) after →
    r.concrete ≠ [] →
      ∃ p,
        YulangClosure.ComputationPermissionEntryR39.prepare (YulangClosure.FormalEntryPrestateBridgeR169.inputs x) a =
            some (f, r, port) ∧
          YulangClosure.ComputationPermissionEntryR39.permissionFor a f r port = some p ∧
            pending = some p ∧ after.permissions = x.before.permissions ++ [p] ∧ after ≠ x.before
'YulangClosure.FormalEntryPrestateBridgeR169.sample_error_changed_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
@YulangClosure.FormalEntryPrestateBridgeR169.selected_endpoint_application : ∀ {Id : Type} [inst : DecidableEq Id]
  (x : YulangClosure.FormalEntryPrestateBridgeR169.Raw Id) (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port endpoint : Id)
  (pending : Option (YulangClosure.ComputationPermissionEntryR39.Permission Id))
  (after : YulangClosure.ComputationPermissionEntryR39.State Id)
  (provider arm : YulangClosure.SuppressionPermissionR116.Operation Id),
  YulangClosure.FormalEntryPrestateBridgeR169.Trace x a
      (YulangClosure.FormalEntryPrestateBridgeR169.Phase.ok f r port pending) after →
    r.concrete ≠ [] →
      YulangClosure.SuppressionPermissionR116.SelectedSource a r arm →
        YulangClosure.SuppressionPermissionR116.operationMatch provider arm = true →
          endpoint = provider.family →
            ∃ p, pending = some p ∧ after.permissions = x.before.permissions ++ [p] ∧ endpoint ∈ p.concrete
'YulangClosure.FormalEntryPrestateBridgeR169.selected_endpoint_application' depends on axioms: [propext, Quot.sound]
@YulangClosure.FormalEntryPrestateBridgeR169.duplicate_order_preserved : ∀ {Id : Type} [inst : DecidableEq Id]
  (x : YulangClosure.FormalEntryPrestateBridgeR169.Raw Id) (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port first last : Id)
  (pending : Option (YulangClosure.ComputationPermissionEntryR39.Permission Id))
  (after : YulangClosure.ComputationPermissionEntryR39.State Id),
  YulangClosure.FormalEntryPrestateBridgeR169.Trace x a
      (YulangClosure.FormalEntryPrestateBridgeR169.Phase.ok f r port pending) after →
    r.concrete = [first, first, last] →
      ∃ p, pending = some p ∧ after.permissions = x.before.permissions ++ [p] ∧ p.concrete = [first, first, last]
'YulangClosure.FormalEntryPrestateBridgeR169.duplicate_order_preserved' depends on axioms: [propext, Quot.sound]
YulangClosure.FormalEntryPrestateBridgeR169.finite_entry_example : ∀ (concrete variables : List Nat),
  variables.length ≤ 1 →
    YulangClosure.FormalEntryPrestateBridgeR169.Trace
      (YulangClosure.FormalEntryPrestateBridgeR169.exampleRaw concrete variables)
      (YulangClosure.FormalEntryPrestateBridgeR169.exampleAction concrete variables)
      (YulangClosure.FormalEntryPrestateBridgeR169.Phase.entry YulangClosure.FormalEntryPrestateBridgeR169.exampleFormal
        (YulangClosure.FormalEntryPrestateBridgeR169.exampleRow concrete variables) 4)
      (YulangClosure.FormalEntryPrestateBridgeR169.exampleRaw concrete variables).before
'YulangClosure.FormalEntryPrestateBridgeR169.finite_entry_example' depends on axioms: [propext]
YulangClosure.FormalEntryPrestateBridgeR169.finite_symbolic_publication_example : have x :=
  YulangClosure.FormalEntryPrestateBridgeR169.exampleRaw [7, 7, 11] [13];
have a := YulangClosure.FormalEntryPrestateBridgeR169.exampleAction [7, 7, 11] [13];
have r := YulangClosure.FormalEntryPrestateBridgeR169.exampleRow [7, 7, 11] [13];
have p :=
  YulangClosure.FormalEntryPrestateBridgeR169.copiedRecord a YulangClosure.FormalEntryPrestateBridgeR169.exampleFormal r
    4;
have after :=
  { permissions := [p],
    links :=
      [{ occurrence := 17, slot := 45, lower := YulangClosure.ComputationPermissionEntryR39.Endpoint.entry 4,
          upper := YulangClosure.ComputationPermissionEntryR39.Endpoint.symbolic 3 13 },
        { occurrence := 17, slot := 46, lower := YulangClosure.ComputationPermissionEntryR39.Endpoint.symbolic 3 13,
          upper := YulangClosure.ComputationPermissionEntryR39.Endpoint.entry 4 }],
    inflow := [] };
YulangClosure.FormalEntryPrestateBridgeR169.Trace x a
  (YulangClosure.FormalEntryPrestateBridgeR169.Phase.published YulangClosure.FormalEntryPrestateBridgeR169.exampleFormal
    r 4 (some p))
  after
'YulangClosure.FormalEntryPrestateBridgeR169.finite_symbolic_publication_example' depends on axioms: [propext]
YulangClosure.FormalEntryPrestateBridgeR169.finite_symbolic_success_and_error_example : have x :=
  YulangClosure.FormalEntryPrestateBridgeR169.exampleRaw [7, 7, 11] [13];
have a := YulangClosure.FormalEntryPrestateBridgeR169.exampleAction [7, 7, 11] [13];
have r := YulangClosure.FormalEntryPrestateBridgeR169.exampleRow [7, 7, 11] [13];
have p :=
  YulangClosure.FormalEntryPrestateBridgeR169.copiedRecord a YulangClosure.FormalEntryPrestateBridgeR169.exampleFormal r
    4;
have after :=
  { permissions := [p],
    links :=
      [{ occurrence := 17, slot := 45, lower := YulangClosure.ComputationPermissionEntryR39.Endpoint.entry 4,
          upper := YulangClosure.ComputationPermissionEntryR39.Endpoint.symbolic 3 13 },
        { occurrence := 17, slot := 46, lower := YulangClosure.ComputationPermissionEntryR39.Endpoint.symbolic 3 13,
          upper := YulangClosure.ComputationPermissionEntryR39.Endpoint.entry 4 }],
    inflow := [] };
YulangClosure.FormalEntryPrestateBridgeR169.Trace x a
    (YulangClosure.FormalEntryPrestateBridgeR169.Phase.ok YulangClosure.FormalEntryPrestateBridgeR169.exampleFormal r 4
      (some p))
    after ∧
  YulangClosure.FormalEntryPrestateBridgeR169.Trace x a
      (YulangClosure.FormalEntryPrestateBridgeR169.Phase.sampleError
        YulangClosure.FormalEntryPrestateBridgeR169.exampleFormal r 4 (some p))
      after ∧
    p.concrete = [7, 7, 11] ∧ after ≠ x.before
'YulangClosure.FormalEntryPrestateBridgeR169.finite_symbolic_success_and_error_example' depends on axioms: [propext]
YulangClosure.FormalEntryPrestateBridgeR169.finite_empty_example : have x :=
  YulangClosure.FormalEntryPrestateBridgeR169.exampleRaw [] [];
have a := YulangClosure.FormalEntryPrestateBridgeR169.exampleAction [] [];
have r := YulangClosure.FormalEntryPrestateBridgeR169.exampleRow [] [];
YulangClosure.FormalEntryPrestateBridgeR169.Trace x a
    (YulangClosure.FormalEntryPrestateBridgeR169.Phase.ok YulangClosure.FormalEntryPrestateBridgeR169.exampleFormal r 4
      none)
    x.before ∧
  YulangClosure.ComputationPermissionEntryR39.permissionFor a YulangClosure.FormalEntryPrestateBridgeR169.exampleFormal
      r 4 =
    none
'YulangClosure.FormalEntryPrestateBridgeR169.finite_empty_example' depends on axioms: [propext]

```
stderr:
```text

```

## Axiom groups

Exactly 18 complete groups were printed. Six use `[propext]`; eleven use `[propext, Quot.sound]`; `sample_error_changed_state` uses `[propext, Classical.choice, Quot.sound]`. No sorryAx, project axioms or native-evaluation assumptions occur in these transitive audits. Full theorem types and results appear unabridged above.
```text
'YulangClosure.FormalEntryPrestateBridgeR169.erased_source_read' depends on axioms: [propext]
'YulangClosure.FormalEntryPrestateBridgeR169.collected_parameter_payload' depends on axioms: [propext]
'YulangClosure.FormalEntryPrestateBridgeR169.entry_prepared' depends on axioms: [propext, Quot.sound]
'YulangClosure.FormalEntryPrestateBridgeR169.copied_exact' depends on axioms: [propext, Quot.sound]
'YulangClosure.FormalEntryPrestateBridgeR169.linked_exact' depends on axioms: [propext, Quot.sound]
'YulangClosure.FormalEntryPrestateBridgeR169.published_exact' depends on axioms: [propext, Quot.sound]
'YulangClosure.FormalEntryPrestateBridgeR169.successful_nonempty' depends on axioms: [propext, Quot.sound]
'YulangClosure.FormalEntryPrestateBridgeR169.successful_empty' depends on axioms: [propext, Quot.sound]
'YulangClosure.FormalEntryPrestateBridgeR169.duplicate_guard_derived' depends on axioms: [propext, Quot.sound]
'YulangClosure.FormalEntryPrestateBridgeR169.retained_input_rejected' depends on axioms: [propext, Quot.sound]
'YulangClosure.FormalEntryPrestateBridgeR169.malformed_input_rejected' depends on axioms: [propext, Quot.sound]
'YulangClosure.FormalEntryPrestateBridgeR169.sample_error_changed_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'YulangClosure.FormalEntryPrestateBridgeR169.selected_endpoint_application' depends on axioms: [propext, Quot.sound]
'YulangClosure.FormalEntryPrestateBridgeR169.duplicate_order_preserved' depends on axioms: [propext, Quot.sound]
'YulangClosure.FormalEntryPrestateBridgeR169.finite_entry_example' depends on axioms: [propext]
'YulangClosure.FormalEntryPrestateBridgeR169.finite_symbolic_publication_example' depends on axioms: [propext]
'YulangClosure.FormalEntryPrestateBridgeR169.finite_symbolic_success_and_error_example' depends on axioms: [propext]
'YulangClosure.FormalEntryPrestateBridgeR169.finite_empty_example' depends on axioms: [propext]
```

## Cache and resource evidence

Inventory covers every `.lake` descendant: relative path, kind, mode, size, mtime_ns, ctime_ns and SHA-256 of regular file bytes or symlink targets; access times excluded because reads may update them. JSON serialization is compact separators, sorted path order.
Before: `{"entries": 430, "files": 424, "inventory_sha256": "59dc95c16b95e28f5786e921dfdff8d6fb4c3af990027695ff7bfa2bd5f9c7e0", "regular_bytes": 100516779}`.
After: `{"entries": 430, "files": 424, "inventory_sha256": "59dc95c16b95e28f5786e921dfdff8d6fb4c3af990027695ff7bfa2bd5f9c7e0", "regular_bytes": 100516779}`.
Exact inventory equality: **True**. Added/removed/changed entries: `[]`.
Peak child RSS: 785664 KiB. Audit timeout bound 120 seconds; lane bound 900 seconds. This final receipt-producing command elapsed 5.952813 seconds. No command session remains active.

## Parent application, coverage and open owners

`selected_endpoint_application` consumes `successful_nonempty` and applies `YulangClosure.SuppressionPermissionR116.selected_endpoint_member` to the same appended permission. It supplies R39 prepare and permissionFor producer equations; SelectedSource, complete operation match and provider endpoint equality remain explicit premises.
Represented: raw Lambda parameter/annotation/registration lookup; finite event prefixes; exact concrete copy including ordered duplicates; empty row; symbolic links before publication; publication; success and post-publication sample failure; selected early rejection cases. Quantification remains arbitrary Id with DecidableEq; finite examples use Nat.
Omitted: actual Rust execution authentication, complete branded identity realization, allocation/bytes/scratch/levels/propagation/rollback, exhaustive native error behavior, complete language constructors and actual Catch/subtraction consumption. `other` preserves other expression identities without proving whole-language cases.
First remaining premise: prove that the actual Rust collector and constructor, with the same pre-state and collected action, realize this Trace. Owner: primary source/native lane. Then authenticate R116 SelectedSource, complete operation/declaration identity, endpoint decoding and R45/R54 consumer ownership. Original shared-witness A/B soundness, effects, principality and termination remain OPEN. No production authority or self-certification.

Writes stopped after this handoff. Independent review and primary adjudication are pending.
