# R4 bounded decoder construction

Sprint-ID: `EFFECT-PERMISSION-NATIVE-DECODE/20261029-r4`.
Contract SHA-256: `15a9b86ae2e75133a5667ca072456f83f092fb455e3402ad0decbd91294f69ce`.
Input manifest SHA-256: `b36ac6d4f1463a3e085c7aa11dea7b0c9fa39037213bfc2c4f7293811bf1af84`.
Assignment: `/root/effect_permission_native_decode_r4_lean`; handoff revision 2.
Supersedes revision1 (12484 bytes), SHA-256
`ca6c7846f4fbef9e1fafdcb26d4c4511b18e6f123d12b1151b89e5492125b188`.
Baseline: `d33805eb589ac89925bacab57e362df093456fe0` plus the pinned overlay.
Role: registered Lean leaf; observed model/effort UNKNOWN. Sole author; no descendants.
Outcome at construction freeze: constructed, unchecked bounded mathematical instance.

## Governing source and unchanged parent

Original claim: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§§1,3,5: every supported original source program, lawful finite history and actual
retained occurrence/polar parent-copy pair, with one joint witness at the original
scopes, preserving typing, required principal coverage, soundness, progress and
termination. The birth-level correction is
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6.
Accepted effect policy is
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2:
composed variance, exact concrete identities, local subtraction with actual
constraint-derived inflow/residual and retained symbolic dependencies.
Research drafts supply no semantic authority.

Actual parent-facing theorem:
`YulangClosure.FormalPermissionAuthenticatedSiteExport.extracted_port_and_export`
(`FormalPermissionAuthenticatedSiteExport.lean:130`). It quantifies context,
source tree/path/optional row, source visit and actual port, State/code, one
shared dependent decoded output, snapshot and entire observation list. Its two
extraction premises are `decodeValue = some out` and
`expectedAll ... out.entries = some observations`; the conclusion is EffectVisit
and `decodeObserved = some out`. R4 preserves these premises and computes their
bounded instance, using that same output for both retained source paths.

## Inputs and source-to-model correspondence

All 45 R4 input-manifest entries were read and SHA-256 checked successfully.
Exactly the twelve pinned project inputs were copied to
`/tmp/yulang-effect-permission-native-decode-20261029-r4/lean-project/`:
README, the eight manifest-listed FormalPermission modules, lakefile TOML,
manifest and toolchain. Every copy hash matches the manifest. The complete
path/size/hash inventory is `lean-project/copy-inventory.json`, SHA-256
`26af38faeeefd0cf01931fcd84a5bae7bd8e9bba52adf9b826e1107412039f5b`. No shared `.lake`
was accessed. The manifest contains zero external packages, and the pin is
`leanprover/lean4:v4.35.0`.

R3 observation is evidence revision 5 SHA-256
`b40c83795726801e1f3fd9fede2b039e7079035563ea91173786c8d437e62af1`;
R3 review `13af7799d625efcc05c50411606dffff574e4ca363e2c348bf9540120fb71571`
accepted bounded Rust evidence only. R3's stopped proof handoff
`8513f0691a5e4066fca60e3f0aeb4b684e52696e2424edfde0a645cdd41367e9`
is not a proof. Luna's R4 source handoff is
`tasks/agent-loop/inbox/effect-permission-native-decode-r4-rust.md`, SHA-256
`65058196c3b197cb9b0bbc2cb55fa7e4d58c44444afa143e059d85d1a73937d4`.
Its scope clarification uses ordinary fallback `AnnotationScope::for_source`
with Definition(owner) mapping to Definition(owner), not redacted debug equality.

The Lean tree retains every one of nine source nodes: the root row at position1
with concrete `[0]`, both result rows at positions2/3 with `[1]`/`[2]`, and all six
omitted rows. Full source traversal and chronological constructor-port traversal
are separate computed recurrences. All four chronological ports are represented:
first argument omitted positive, first result concrete negative, nested argument
omitted positive, nested result concrete negative. Root/bare tuple rows are not
ports. Scalar Int/Unit branches and tuple/term assembly do not allocate effects.
Inspected owners are `candidate_effect.rs:1617–1797` and
`lib.rs:10487–10626`; source function recursion is argument value, result value,
argument port, result port; tuple children are ordered. Every fresh effect returns
pre-push length and adds exactly one row. Thus births are n,n+1,n+2,n+3;
first observed origin n+1=22 yields n=21 and the full vector [21,22,23,24].
This is the decoder-slice start, not the whole solver's initial effect counter.
The formal allocation theorem computes all four births rather than assuming
an independently selected entry list or reverse inferring from rows22/24 alone.

Context is parameter0, occurrence4, owner0, scope0. Atom labels0/1 encode only
source constructors Int/Unit; their injectivity is explicit. `allocation_and_decode`
universally quantifies both labels and every State field. It computes the retained
entries, four births and final record update. `initial unread` changes only the
mathematical nextEffect coordinate to21. No default State is used or identified
with native State. Unread nextValue/nextView/value/hole/effect/view/viewData fields
remain arbitrary and preserved. Atomic tags can change shapes; retained entries,
expected observations and successful decoder conclusion are independent of them.

Snapshot capture4/root0 has representative rows22/24 fixed and independently
materialized negative nodes17/14; observations preserve lineage0/1, owner,
metadata, complete paths, original/canonical rows, negative polarity, capture/root,
and matching intern/returned port. Source-order lineage0/1 is not witness2/3.
Parameter value-row23 is not an effect origin or an initial State observation.

## Artifact and declarations

Changed source:
`notes/theory/lean/YulangClosure/FormalPermissionAuthenticatedNativeDecode.lean`;
11294 bytes; SHA-256 `10f28441b17b8900f2d21bde3c0bfee83549214c464eb2e48178cafd3e3add10`.
The scratch copy is byte-identical. No root import was changed.
All declarations below are in
`YulangClosure.FormalPermissionAuthenticatedNativeDecode`:

- `source_constructor_injective`: injectivity of source constructor codes.
- `complete_source_inventory`: exact full ordered nine-node inventory.
- `complete_ordered_ports`: exact complete ordered four-port inventory.
- `code_from_exact_source`: the exact frozen source tree projects to this code,
  with both scalar constructor tags and every child Effect row derived by the
  explicit partial encoder. Unsupported forms fail the bounded projection; no
  original-language source case is removed from the parent claim.
- `allocation_and_decode`: for every State and both tags, a computed shared
  output with decoder equation, exact retained entries, four births and final
  State preserving every other field.
- `output_equations`: the same equations for the chosen dependent output.
- `base_from_forward_allocation`: n+1=22 yields n=21 and all four ordinals.
- `expected_observations`: entire expectedAll equation at21.
- `tags_and_unread_state_irrelevant`: arbitrary tag pairs and arbitrary unread
  States yield identical retained entries and the entire observation list.
- `first_source_port`, `second_source_port`: source visit plus PortPath.
- `extracted_instance`: both EffectVisits and successful decodeObserved for
  that same computed output, universally over tags and unread fields, by direct
  applications of the unchanged parent-facing theorem.
- `source_coded_instance`: concrete Int0/Unit1 source-constructor specialization.

## Frozen audit and execution

Audit input revision3:
`/tmp/yulang-effect-permission-native-decode-20261029-r4/lean-project/audit-inputs.json`,
SHA-256 `7a3118f686840ecf2858acf17d949eb79b869b95557b5bfa24d4cfa7bbade5d2`.
It contains the full argv, all thirteen fully qualified theorem names and raw paths.
Revision2 supersedes provisional command freeze
`d07804d2544cdb888ec53f300caf655d1d9933e58154e0c9b1ac88af4989d1fd`
by replacing inherited environment with explicit `env -i` PATH/TMPDIR/thread values;
Revision3 adds the explicit source encoder and `code_from_exact_source` theorem
after Luna identified the missing formal source/code link; it supersedes revision2
`c9c95f3118615450643e0294f226fe244881bc9ea0b7e8e33006f38026a84756`.
The final artifact froze before 420 seconds; no audit preceded this repair.

Checker SHA-256 `a4f10b70297cbf4d8b5bc0c7526bc29783eaf417f1f70e53eeea341d1150dde6`.
Native Lake binary (read-only hash, not version execution):
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`,
SHA-256 `8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1`;
Lean binary SHA-256
`bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.
No Lean/Lake/version/checker/build/formatter command was run during construction.
Luna subsequently corrected the freeze timing and released exactly one checker
invocation of audit-input revision3. Its failed result is recorded below.
No network or installation ran.

## Parent application and open boundaries

`extracted_instance` applies the unchanged theorem twice with one output,
computing both extraction equations rather than adding either as a hypothesis.
This only constructs bounded mathematical record consistency for the accepted
observation. Native state/scalar identity is neither assumed nor proved.
The next source/native premise is authentication of the code/State projection
and snapshot against the actual complete native execution, owned by Luna's
source/native lane; this bounded abstraction does not establish it universally.
All original A/B, effect hygiene, consumer residual, unequal row transport,
soundness, principality, termination and production gates remain OPEN.

Represented: all nine observed source nodes, every four-port allocation, the
two exact retained identities and complete expected observation list. Omitted
from claims: all other programs, variables/holes, symbolic/delegated histories,
positive concrete cases, unequal representatives, consumer handling/residual,
full capture simulation, native initial-State identity and scalar Term handles.
No source domain or hypothesis of the original parent is strengthened.
Independent review and production authority remain with Luna; no self-review.

Writes remain limited to the leased source/handoff and R4 scratch roots.
No Git, compiler code/test/config/source mutation, descendants or background work.
Final runtime/resource and writes-stopped receipt follows below.


## Final stop receipt — single audit failed

Luna initially withheld release after interpreting the later input recheck as
the construction freeze. The leaf stopped at 2026-10-29T11:32:02.607566Z
(470.6 seconds). Luna then corrected that interpretation and separately released
exactly one checker invocation of the unchanged audit-input revision3.
The released invocation started at 2026-10-29T11:33:00.424693Z and exited1 at
2026-10-29T11:33:10.940634Z, approximately538.9 seconds after admission.
No proof bytes changed and no retry or repair occurred.

Actual versions were Lake5.0.0-src+eb6cafb and Lean4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Both version subprocesses exited0.
All eight imported modules built. The target module failed parsing at42:81 and
66:82, each with `unexpected token 'mutual'`, where declaration documentation
comments immediately precede mutual blocks. The build subprocess and checker
both exited1. The theorem-type and `#print axioms` stage was not reached.
All thirteen declarations remain UNCHECKED; no printed theorem types or axiom
results exist. No axiom-free or whitelist claim is made. Independent review
has NOT RUN. This is not a proof-closure receipt.

Raw receipts, all under the exact leased
`/tmp/yulang-effect-permission-native-decode-20261029-r4/lean-project/`:

- `audit-stdout.txt`:4563 bytes; SHA-256
  `ed2adf256bb2c445b4df2526b58086ff0945e37ab121ce04018619fdf6d6eba2`.
- `audit-stderr.txt`:33 bytes; SHA-256
  `0edf2d238840b65a26de68075c964d099167cf4cae51705f162bcfa4e7addc60`.
- `audit-status.txt`:2 bytes, content `1\n`; SHA-256
  `4355a46b19d348dc2f57c046f8ef63d4538ebb936000f3c9ee954a27460dd865`.
- `audit-time.txt`:2495 bytes; SHA-256
  `9398d3b56732b7787b02e05e5fdd717b9ab3325ef233c9f00f6a47027f9890a7`.

Measured wall10.51 seconds, user5.91 seconds, system1.52 seconds;
peakRSS780860KiB; no timeout, swap or delivered signal. The single audit
allowance is spent. No background process or descendant remains.

Timing clarification retained as evidence: final proof and audit-input revision3
were frozen by the Python write at epoch1793273444.3951793
(2026-10-29T11:30:44.395179Z), approximately392.4 seconds after admission at
11:24:12Z. The later epoch1793273481.591946 (11:31:21.591946Z, ~429.6s)
was a read-only recheck of45 inputs and source/scratch equality, not a proof edit.
Handoff prose was updated between those events. Luna's stop decision remains in
force until Luna issued the separate exact audit release; time itself did not
grant audit authority.

Construction used `cat`, `sed`, `rg` and Python JSON/byte/hash inspection and
copying within the exact leases. The single released execution used exactly the
full argv and explicit environment in audit-input revision3; its checker ran
the two version subprocesses and focused target build reported above.
No separate Lean/Lake probe, formatter, default-target build or second checker ran.

All original-parent, source/native, effect-hygiene, consumer-residual,
unequal-transport, soundness, principality, termination and production gates
remain OPEN. The first executable repair is to change the two documentation
comments to regular comments or move them inside the mutual blocks; that repair
was not performed. A new repair/audit packet and execution release belong to
Luna. The actual failed launch receipt is preserved in the four raw files;
audit-input revision3 preserves its exact command.

Scratch outputs consist of the12 copied inputs, final proof copy,
copy-inventory.json, audit-inputs.json, generated `.lake/` build/configuration
outputs (including the eight imported modules and failed target setup outputs),
and the four raw audit receipts listed above. The leased audit TMPDIR was created
at `/tmp/yulang-effect-permission-native-decode-20261029-r4/lean-receipts/audit-tmp/`.
No cleanup occurred.

Final audit/process stop time: `2026-10-29T11:33:10.940634+00:00`.
Conservative elapsed since admission:538.9 seconds of600; audit resources are
measured above and total active CPU outside that command was not measured.
This reporting-only revision2 changes only the leased handoff, preserving the
11294-byte proof and its frozen SHA-256. Writes are **STOPPED** after revision2;
all leased outputs and scratch are frozen.
