# R108 module-faithful Lean validation plan — revision 1

Status: **CANDIDATE PLAN / UNEXECUTED / FROZEN / WRITES STOPPED**.
Assignment `R108-LEAN-MODULE-VALIDATION`, actual leaf `/root/r108_lean_plan`;
sole author, no descendants. The parent's NEW_TASK is the live assignment
receipt. Requested registered role: lean_prover; observed model/effort UNKNOWN
to this leaf. Baseline `070cc8d2fc8ae519fa9f3eb2d1b872bcb485fba8`.
Contract `tasks/agent-loop/sprints/effect-permission-rust-lib-repair-and-lean-module-validation-20261101-r108.md`,
SHA-256 `e7e024562d59624a9b52a3fb71700156027aa582fb09599cf40816d3c8106658`.
Sole write lease: this handoff. This is a frozen normative runner plan; no
runner, Lean process, generated artifact or cache was materialized by the leaf.
Luna owns runner materialization/execution and generated-root cleanup. A fresh
independent reviewer must check the actual runner against this plan before
launch; this leaf supplies no self-certification.

## Original source and unchanged parent

Read actual original parent `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§§1,3,5 and current correction `notes/design/2026-10-24-birth-level-scc-intrusion.md`
§§2–6. The parent ranges over every supported original source, lawful finite
Simple-sub construction history and actual retained qualified extrusion;
it requires original typing and principal coverage, ordinary inference
progress/termination, original lexical/type/event scopes, complete Call,
effect hygiene, recursive sharing and one lawful joint evidence strategy.
Qualification is SCC membership in the immutable-birth-level induced graph,
with precisely the retained polarity-specific pairs. No quantifier, source
feature, scope or shared witness is removed by this plan.

Source selection: `notes/design/2026-10-08-source-generalize-definition.md`
§§2–3 selects construction §§3–5; actual §3.3 of
`notes/theory/2026-10-08-source-generalize-definition-and-proof.md` distinguishes
ViewLogic before challenges, once-retained Shared and description-owned
EventProof under actual telescopes. Read the opening correction of
`docs/yulang-source-type-safety-ja.tex`: old evidence remains fixed while the
executing owner resolves separately; general source/native correspondence
remains open. That research manuscript supplies no semantic adoption.

Actual definitions inspected: `YulangClosure.OriginalSource.LogicalOwnerBridgeR105`
(Position/advance/follow, appAddress, bodyTelescope/bodyAddress/bodyOwner and all
15 theorem signatures), `YulangClosure.OriginalSourceEnvironment.LocalAdmissions`
and `.DataAdmitted`, and `YulangClosure.SourceProblem.InferenceSoundness`,
`.SourceScopedCoverage`, `.PrincipalCoverage` plus `YulangClosure.LocalLaws`.
The latter are propositions/assumed laws, not concrete source instances.

## Frozen source DAG and topological command order

Every short name denotes `YulangClosure.<name>` and exact unchanged path
`notes/theory/lean/YulangClosure/<name>.lean`. Hashes were recomputed read-only
and match R105. Init/Std are distribution inputs. Exactly 12 project
prerequisites plus the bridge = 13 calls. No concatenation/import stripping,
source copy/edit, added audit file or root import is allowed.

| Call | Name | SHA-256 | Explicit direct imports |
| --- | --- | --- | --- |
| 1 | OriginalSourceSyntax | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` | Std |
| 2 | OriginalSourceGeneration | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` | YulangClosure.OriginalSourceSyntax |
| 3 | SourceLogicalOccurrencesR104 | `0e7a42d66578388585a5abd1da12c77a9d7d46823687ed511d26e359b3078f39` | YulangClosure.OriginalSourceGeneration |
| 4 | NativeClosureEnvironment | `39aa5cefa078dd423e54f0d9790f9a48e136326742e01f65149f317c907be957` | Init |
| 5 | Contracts | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` | Init |
| 6 | SourceIdentityWorld | `6019fd9d57cde50183e016bd0c72de2c6eee72009065d85119fb0348dbcf0168` | YulangClosure.NativeClosureEnvironment; YulangClosure.Contracts |
| 7 | SourceFunctionMembership | `8d370ee57e486ae48607d1bab493ae5135f28bf8a5a7ff1b0ef240fc0247e424` | YulangClosure.SourceIdentityWorld |
| 8 | NativeDictionaryDenotation | `d44a78f08970a09ca4c3e99a1d8dea846286a299d1a2bc91ec3b5e0eabea9070` | Init |
| 9 | OriginalSourceInterpretation | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` | YulangClosure.OriginalSourceGeneration; YulangClosure.SourceFunctionMembership; YulangClosure.NativeDictionaryDenotation |
| 10 | OriginalSourceEnvironment | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` | YulangClosure.OriginalSourceInterpretation |
| 11 | SourceSignatureConstruction | `ed07890e29b4dcb38cabd18ec0e196efde9e95c64902942a9906a470b38c3311` | YulangClosure.OriginalSourceSyntax |
| 12 | OriginalSourceEvents | `cfd5f502a1e68a97e27e11a75400fae8789f167c92596aedb08ef7dfbb724342` | YulangClosure.OriginalSourceEnvironment; YulangClosure.SourceSignatureConstruction |
| 13 | SourceLogicalOwnerBridgeR105 | `6fecc134ac2009392f043331eb4d1a3dd479668208991e60c8a5d339e69b45b4` | YulangClosure.SourceLogicalOccurrencesR104; YulangClosure.OriginalSourceEvents |

## Pins and exact execution manifest

All listed hashes were re-read without invoking the listed tools. Native Lean
is the installed 4.35.0 path, not an elan proxy. `lean-toolchain` reads
`leanprover/lean4:v4.35.0`; lakefile has `-j1 -M1024`, YulangClosure default,
and the manifest has no external packages. Actual version commands: NOT RUN.
No Lake, checker, default target, version, extra audit or R106 retry call is
part of this batch. The skill checker is unavailable within this exact call/
cache envelope; existing R105 #check/#print axioms commands are the audit.

| Exact path | SHA-256 |
| --- | --- |
| `/home/momota1029/rust/yulang/tasks/agent-loop/inbox/effect-permission-module-output-protocol-r107.md` | `8301f19752e74f8a2c3eaf864a44a32d41a3710b18f6dc46748f417a2186a44f` |
| `/home/momota1029/rust/yulang/tasks/agent-loop/inbox/effect-permission-logical-owner-r105-proof.md` | `32f3fcf62b5fbc14eb040d570e0752e0ab8a8ad65e44f5f6c2f7b65f14baf422` |
| `/home/momota1029/rust/yulang/notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `/home/momota1029/rust/yulang/notes/theory/lean/lakefile.toml` | `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` |
| `/home/momota1029/rust/yulang/notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean` | `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38` |
| `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean/libInit_shared.so` | `7831b707e868cee76c353d26649fbd8981b2f4d7e0329af55bbf4fa9e0c69350` |
| `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean/libleanshared.so` | `efef27df56f2197139afe12f1a2b63913a05f1aba81ce88824c44100431ed8c4` |
| `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean/libleanshared_1.so` | `691bf49d9e542a15808fad9d1f8c5df45860166f77efa57961b5335e65a3a0ed` |
| `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean/libleanshared_2.so` | `141cbfdb3bc2016cd68e0bebc2e5494818213b462ed985afa6d975d4872fb8ec` |
| `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean/Init.olean` | `84ffd94782b2f2f65408dee401a4332bfa7c3274abc7b1040cea7d7a307314f5` |
| `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean/Std.olean` | `81655926012444f214099f1ed6610ed63ade63f9e91b2e5af6689acd9cf1b400` |
| `/usr/bin/time` | `3b11dec50514a8473e9f6efa7a34d584d0657538c09988f61b72d38ad4991a10` |
| `/usr/bin/timeout` | `12690a043dfd555a6c14ccc1564f5649c18f1762c0d6ff66729948130898ec52` |
| `/usr/bin/taskset` | `a431738fadddc2e2326c8ab81843e72f4011658379381aef1502a6ddb1c1115b` |
| `/usr/bin/python3.12` | `e50d468e8b0adfb05733f5b87b3cff34829c4a8c1aea50c865aa8bdfe4bb150f` |
| `/home/momota1029/rust/yulang/notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `/home/momota1029/rust/yulang/notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `/home/momota1029/rust/yulang/docs/yulang-source-type-safety-ja.tex` | `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166` |
| `/home/momota1029/rust/yulang/notes/theory/2026-10-13-intrusion-source-preservation-proof.md` | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| `/home/momota1029/rust/yulang/notes/design/2026-10-24-birth-level-scc-intrusion.md` | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |

`readelf -d` confirmed Lean's direct distribution shared-library names and
RUNPATH `$ORIGIN/../lib:$ORIGIN/../lib/lean`. These pins include those four
Lean shared libraries, not the full OS loader/libc/Python or transitive
standard-library artifact closure. Do not report a hermetically pinned OS or
whole distribution. If review requires that stronger scope, return it to
Luna before any execution; no dependency fetch/install is authorized here.

Define these exact immutable strings:

```text
PROJECT=/home/momota1029/rust/yulang/notes/theory/lean
ROOT=/dev/shm/yulang-source-owner-module-validation-20261101-r108
LEAN=/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean
```

For each table row `Name`, in order, substitute that literal name into this
argv array; this uniquely specifies all 13 commands:

```text
["/usr/bin/timeout", "--signal=KILL", "60s",
 "/usr/bin/taskset", "-c", "0", "/usr/bin/time", "-v",
 LEAN, "-j1", "-M1024", "--root=" + PROJECT,
 "-o", ROOT + "/YulangClosure/" + Name + ".olean",
 PROJECT + "/YulangClosure/" + Name + ".lean"]
```

`cwd=PROJECT`; stdin=`DEVNULL`; stdout/stderr separate pipes;
`start_new_session=True`, direct wrapper PID is session/process-group ID.
Construct the entire environment afresh, exactly
`{"PATH":"/usr/bin:/bin","LC_ALL":"C","LEAN_PATH":ROOT,"LEAN_NUM_THREADS":"1"}`;
inherit no LD_PRELOAD/LD_LIBRARY_PATH/LEAN_PATH/PYTHONPATH additions.
No shell interpretation and no `--stdin`, `--run`, `--trust`, `--version`.
Inherited child limits: RLIMIT_FSIZE soft=hard 16 MiB, RLIMIT_CORE=0.
Native binary/standard library, frozen .lean sources and ROOT are the only
Lean import inputs. Installed `Lean/Util/Path.lean:95–125` puts LEAN_PATH
before builtin library and resolves final `.olean` names. Confirm no
YulangClosure.olean or YulangClosure directory in the builtin library,
no empty LEAN_PATH element, and no project .olean lookup in .lake or cwd.
No previous project artifacts qualify as imports. Recheck every earlier
completed final's identity/hash before consuming its dependent module.

## Corrected monitor state machine

This section fixes the acceptance/abort protocol. Actual executable runner
bytes remain Luna-owned and require independent pre-execution review. It is
not authority to execute the older R106 Python body with a changed root.

1. **Preflight without writing:** rehash every pin and all 13 sources; parse
   exact imports and require the DAG above; reject source/module-header drift.
   Verify CPU 0 is allowed, no concurrent Cargo/Lean verification owner, enough
   remaining sprint time, stdout receipt capacity, and ROOT lexists=false.
   An existing root is preserved and aborts the batch. Never inspect/reuse the
   quarantined R106 root. No version/checker call is a preflight prerequisite.
2. **Acquire root:** atomically mkdir exact ROOT mode 0700 (no exist_ok), open
   it with O_DIRECTORY|O_NOFOLLOW, record `(st_dev,st_ino,uid,mode)` and parent
   identity; create exactly its YulangClosure child, mode 0700, retain that
   directory's fd/identity. No other directory is allowed. Verify root and child
   identity on every scan and before cleanup; mismatch means quarantine/stop.
3. **Per-call allowlist:** completed rows admit only their exact final
   `YulangClosure/<Name>.olean`. Future rows admit no output. During one active
   call allow its exact final and at most one filename matching anchored
   `^<escaped-active-Name>\.olean\.tmp\.[0-9]+$` in that same child directory.
   The observed `.olean.tmp.7` is covered. This numeric pattern is a **guarded
   experimental hypothesis**, not a native implementation theorem; suffix
   meaning/PID/atomicity and crash cleanup are unknown. No server/private/IR
   sidecars, other temporary classes or subdirectories are admitted. At most
   14 regular filenames exist in an accepted scan (13 finals plus one active
   temp). Never rename/copy a temporary into a final.
4. **Scan safely:** every 50 ms while draining both pipes nonblocking with
   selectors, enumerate relative to retained directory fds. For each entry
   first validate the observed name (record any forbidden name immediately,
   even if it disappears), then use lstat/fstatat without following symlinks.
   Only nonsymlink regular files with st_nlink=1, expected uid/dev and size
   <=16 MiB qualify. Open with O_NOFOLLOW, fstat and compare the inspected
   identity; reject symlink, hardlink, special file or directory. Count both
   active temp and final, every completed final, and directory allocation:
   sum st_size for logical bytes and st_blocks*512 for allocated bytes.
   Account stdout+stderr in-memory bytes separately. Reject either output sum
   >2 GiB or >one temporary, unexpected names/types, or pinned-final drift.
   During publication ENOENT or changed known allowed-file identity triggers
   at most three complete immediate rescans; keep anomaly observations.
   Persistent instability is failure. Do not silently skip entries or carry
   forward an undercount. Unexpected-name/type evidence always aborts;
   rescan never erases it. Temporary snapshots are not import evidence.
5. **Limits:** stop at first nonzero exit, signal, missing/truncated output,
   monitor exception, hash drift, deadline or resource breach. CPU affinity 0,
   Lean -j1/-M1024 plus LEAN_NUM_THREADS=1; per-call wall <=60 seconds; cumulative
   monotonic launch-to-reap charge <=1,200 seconds (13*60 <=780 before bounded
   cessation/receipt overhead), within the 2,400-second sprint remainder.
   Sample full group's RSS every 50 ms; >1 GiB is failure. Require GNU time's
   final maximum RSS <=1 GiB and present; absence is incomplete evidence.
   Bound combined stdout/stderr to 8 MiB per call and retained batch buffers
   to 104 MiB; log overflow aborts and labels the retained output incomplete.
   No disk logs, scratch script, persistent cache or hidden extra process.
   Keep at most one active Lean group and serialize with Cargo. Per-file
   RLIMIT_FSIZE is enforced; sampled RSS/aggregate-size monitoring can overshoot
   between samples and supplies no cgroup/quota hard-limit claim. Accepted
   legal names and 16-MiB per-file limit imply at most 224 MiB file data at an
   observed valid state. Native extern behavior is not established by that
   arithmetic. A strict unsampled 2-GiB root guarantee requires a separately
   available quota/enforcement mechanism approved by Luna; never claim one
   was installed or silently widen this resource envelope.
6. **Quiesce after every call:** retain pgid/session/launch starttime, direct
   child and observed descendant `(pid,starttime)` identities. On ordinary
   return, reap the direct child and require no live group/session member or
   recorded live descendant before accepting a module. On any failure or
   leftover member, SIGKILL only the owned group/recorded owned descendants;
   retain kill errors, poll/reap for up to five monotonic seconds at 50-ms
   intervals, never just scan immediately after kill. Record every observation,
   including zero-RSS live processes. Reaping the wrapper alone is insufficient.
   /proc ENOENT races may be rescanned; permission/parse errors mean UNKNOWN.
   PID identity reuse must not authorize killing a foreign process. Track
   process-group and session IDs (GNU timeout may move its child group), and
   inspect known descendants for a live writer that escaped the group.
   Require two clean census samples at least 100 ms apart after direct-child
   reaping, pipes at EOF, and no unknown scan result. Zombie identities may be
   recorded separately as nonwriting; never describe them as reaped by this
   runner unless it actually reaped them. This is bounded observational
   cessation evidence, not a proof about arbitrary daemonizing executables.
   If ownership/cessation cannot be confirmed, quarantine ROOT and stop;
   no next module, deletion, automatic retry or retry on a new root follows.
7. **Stable final validation:** only after exit zero and confirmed cessation,
   perform two identity/size inventories 100 ms apart, now allowing precisely
   completed finals plus the active final and **zero temporaries**. Require
   active final present, no sidecars, no prior-final drift. Hash each file via
   opened fd with before/after fstat identity/size/time checks; retain full
   sorted relative-path/size/allocated-byte/SHA-256 inventory and root identity.
   Only then mark the module completed and use its final as a fresh import.
   Any inventory/hash exception is failure, never proof of module success.
   Recheck all frozen inputs before next launch and after the final call.
8. **Receipt then cleanup:** in a finally path preserve the first failure and
   secondary monitor/kill/reap/scan/cleanup exceptions independently. Do not
   allow a cleanup exception to replace the mathematical/compiler diagnostic.
   Drain bounded captured output and report complete argv, env, cwd, monotonic
   wall charges, exits/signals, sampled peak, GNU-time fields and artifact
   inventory. If cessation and owned-root identities are confirmed, remove
   only regular owned entries relative to retained fds, then child and root;
   no recursive wildcard deletion or symlink traversal. Record removal result
   and parent-relative lstat/lexists=false. If root already vanished, report
   unexplained disappearance, not successful runner deletion. On any uncertainty
   preserve/quarantine exact root and return to Luna. Cleanup is the primary
   verification owner's duty; independent post-execution review checks it.

This narrows output permission to each active module and repairs the R106
post-kill race. It does not establish native temporary naming, publication,
fsync, signal cleanup or all possible writer escape behavior. R107 found the
serializer is opaque extern `lean_compacted_region_save`; installed Lean source
has no matching native C++ implementation. No suffix-derived PID inference is
used. The 13 files have no new `module` header; actual `Lean.writeModule` legacy
branch writes one final. An unfamiliar output is a falsifier of this plan,
not permission to widen its guard during the run.

## All 15 declaration and axiom requirements

All names have fully qualified prefix
`YulangClosure.OriginalSource.LogicalOwnerBridgeR105.`. The source appendix
below is copied read-only from the frozen theorem headers, not checker output.
Require exactly these 15 declarations to be actual `theorem` declarations,
with all source quantifiers/premises/conclusions intact. Each already has its
own `#check @fully.qualified.name` and `#print axioms fully.qualified.name`
in the unchanged bridge. Preserve every full printed type and every complete
axiom list from call 13. Missing output, unknown name, nonzero exit, or lack
of a theorem-kind source declaration fails acceptance; a definition of Prop
cannot substitute. The only allowed reported dependencies are `propext`,
`Classical.choice`, `Quot.sound`; reject sorryAx, project axioms, native
unchecked assumptions and checker bypasses. Report actual lists, including
empty lists, without assuming them in advance. Do not infer axiom-freedom
from source grep. No extra theorem audit call is authorized.

### `forest_head_route`

```lean
theorem forest_head_route (route : OriginalSourceEvents.Route)
    (telescope : List OriginalSourceEvents.ScopeEntry)
    (scope : List LogicalOccurrencesR104.ScopeFrame) (head : RuleTree) (tail : RuleForest) :
    (advance ⟨route, telescope, scope, .forest (.cons head tail)⟩ false).map Position.route =
      some route
```

### `forest_sibling_route`

```lean
theorem forest_sibling_route (route : OriginalSourceEvents.Route)
    (telescope : List OriginalSourceEvents.ScopeEntry)
    (scope : List LogicalOccurrencesR104.ScopeFrame) (head : RuleTree) (tail : RuleForest) :
    (advance ⟨route, telescope, scope, .forest (.cons head tail)⟩ true).map Position.route =
      some (route ++ [1])
```

### `choice_right_route`

```lean
theorem choice_right_route (route : OriginalSourceEvents.Route)
    (telescope : List OriginalSourceEvents.ScopeEntry)
    (scope : List LogicalOccurrencesR104.ScopeFrame) (site : Site) (left right : RuleTree) :
    (advance ⟨route, telescope, scope, .tree (.choice site left right)⟩ true).map Position.route =
      some (route ++ [3])
```

### `advance_erases`

```lean
theorem advance_erases (position : Position) (bit : Bool) :
    (advance position bit).map erase =
      LogicalOccurrencesR104.advance position.enclosing position.cursor bit
```

### `follow_erases`

```lean
theorem follow_erases (position : Position) (route : LogicalOccurrencesR104.Route) :
    (follow position route).map erase =
      LogicalOccurrencesR104.follow position.enclosing position.cursor route
```

### `advance_owner`

```lean
theorem advance_owner (position : Position) (bit : Bool) (next : Position)
    (introduction : OriginalSourceEvents.Owner) (step : advance position bit = some next)
    (present : introduction ∈ ownersAt next) : introduction ∈ ownersAt position
```

### `follow_owner`

```lean
theorem follow_owner (position : Position) (route : LogicalOccurrencesR104.Route) (last : Position)
    (introduction : OriginalSourceEvents.Owner) (reached : follow position route = some last)
    (present : introduction ∈ ownersAt last) : introduction ∈ ownersAt position
```

### `app_route_exact`

```lean
theorem app_route_exact (context : Context) (mark : Mark)
    (callee argument : Source .expression) :
    follow (root (sourceRules context (.app mark callee argument)))
      (LogicalOccurrencesR104.annotationRoute mark) = some (appAddress context mark callee argument).position
```

### `app_viewlogic_separate`

```lean
theorem app_viewlogic_separate (context : Context) (mark : Mark)
    (callee argument : Source .expression) :
    OriginalSourceEvents.binderOwner (appAddress context mark callee argument).route
      (appAddress context mark callee argument).telescope
      (appAddress context mark callee argument).binder = []
```

### `app_bridge`

```lean
theorem app_bridge (context : Context) (mark : Mark)
    (callee argument : Source .expression) :
    (LogicalOccurrencesR104.annotationRoute mark,
      (⟨⟨mark.site, .viewLogic, 0⟩, [],
        LogicalOccurrencesR104.appRule context mark callee argument⟩ : LogicalOccurrencesR104.Occurrence)) ∈
      LogicalOccurrencesR104.sourceInventory context (.app mark callee argument) [] ∧
    follow (root (sourceRules context (.app mark callee argument)))
      (LogicalOccurrencesR104.annotationRoute mark) = some (appAddress context mark callee argument).position ∧
    OriginalSourceEvents.binderOwner (appAddress context mark callee argument).route
      (appAddress context mark callee argument).telescope
      (appAddress context mark callee argument).binder = []
```

### `body_telescope_binders`

```lean
theorem body_telescope_binders (mark : Mark) (formal : Formal) :
    (bodyTelescope mark formal).map OriginalSourceEvents.ScopeEntry.binder =
      scopeBinders (LogicalOccurrencesR104.bodyScope [] mark formal)
```

### `lambda_body_route_exact`

```lean
theorem lambda_body_route_exact (context : Context) (mark : Mark) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) :
    follow (root (sourceRules context (.lambda mark formal pattern body)))
      (LogicalOccurrencesR104.bodyRoute mark formal) =
      some (bodyAddress context mark formal pattern body).position
```

### `lambda_body_owner`

```lean
theorem lambda_body_owner (context : Context) (mark : Mark) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) :
    bodyOwner mark formal body ∈ OriginalSourceEvents.sourceOwners context (.lambda mark formal pattern body)
```

### `body_key_coordinates`

```lean
theorem body_key_coordinates {s : OriginalSourceInterpretation.Sorts} {View : Type}
    (mark : Mark) (formal : Formal) (body : Source .expression) (origin : Declaration)
    (parents : List (EventStep (OriginalSourceEnvironment.Runtime s View)))
    (occurrence : Nat) (raw : OriginalSourceEnvironment.Runtime s View) :
    (OriginalSourceEvents.actualKey (bodyOwner mark formal body) origin parents occurrence raw).route = bodyRoute mark formal ∧
    (OriginalSourceEvents.actualKey (bodyOwner mark formal body) origin parents occurrence raw).binder =
      ⟨body.site, .eventProof, 0⟩ ∧
    (OriginalSourceEvents.actualKey (bodyOwner mark formal body) origin parents occurrence raw).parents = parents ∧
    (OriginalSourceEvents.actualKey (bodyOwner mark formal body) origin parents occurrence raw).occurrence = occurrence ∧
    (OriginalSourceEvents.actualKey (bodyOwner mark formal body) origin parents occurrence raw).raw = raw
```

### `lambda_body_bridge`

```lean
theorem lambda_body_bridge (context : Context) (mark : Mark) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) :
    (LogicalOccurrencesR104.bodyRoute mark formal,
      (⟨⟨body.site, .eventProof, 0⟩, LogicalOccurrencesR104.bodyScope [] mark formal,
        LogicalOccurrencesR104.bodyRule context mark formal pattern body⟩ : LogicalOccurrencesR104.Occurrence)) ∈
      LogicalOccurrencesR104.sourceInventory context (.lambda mark formal pattern body) [] ∧
    bodyOwner mark formal body ∈ OriginalSourceEvents.sourceOwners context (.lambda mark formal pattern body) ∧
    follow (root (sourceRules context (.lambda mark formal pattern body)))
      (LogicalOccurrencesR104.bodyRoute mark formal) =
      some (bodyAddress context mark formal pattern body).position
```

## Parent application, coverage and first remaining premise

Conditional on successful kernel/type/axiom acceptance and independent review,
app_bridge and lambda_body_bridge locate R104 logical occurrences in the same
original generated tree, exact Nat owner routes and binder telescopes. Generic
advance/follow cover all ten RuleTree and both RuleForest constructors. App
covers either annotation and arbitrary complete callee/argument; Lambda covers
both annotation cases × both Value/Computation entry modes, arbitrary formal
annotation, pattern and body. App ViewLogic has no runtime Owner; Lambda's
bodyOwner is descriptionProof. body_key_coordinates is readout of data, not
actualEvent admission. No semantic theorem for every other source constructor
is claimed; all original source constructors remain accepted inputs.

First semantic premise remains deriving actual original logical admission and
formal descriptor/interface readout at those exact occurrences, not assuming
LocalAdmissions.logical or whole Build satisfaction. Then construct one lawful
joint equality lift through publication and independent use with the same
Shared witness, followed by source-generated native realization. Owner: Luna
source/proof intake, stable request `R105-LOGICAL-ADMISSION-1`.
InferenceSoundness/SourceScopedCoverage/PrincipalCoverage definitions and
LocalLaws parameters do not discharge this premise. Complete Call/effects,
hygiene, A/B, source/native correspondence and production remain OPEN.

Stable execution request `R108-MODULE-VALIDATION-1`: Luna obtains fresh review
of exact runner bytes and this guard's observational limits, launches at most
this new 13-call batch after PASS, stops at its first failure, preserves full
receipts and obtains fresh post-execution review. Falsifiers are first failing
module, drift, stale import, unfamiliar output, missing theorem/axiom output,
resource breach, uncertain cessation or cleanup. The R106 batch is consumed.

## Material failures and actual work

Inherited R105 flattening failure: exit 1, 17.643051 seconds, 972920-KiB RSS;
NativeDictionaryDenotation line 29 resolved an unqualified Step against the
previous concatenated Contracts namespace; the 100-error limit was reached
before any R105 audit. Module-faithful checks preserve namespace boundaries.
Inherited R106 first-module failure: exit -9, wall 5.918905 seconds, sampled
819956-KiB group peak, empty stdout/stderr; first error was the guard's
`UNEXPECTED_OUTPUT YulangClosure/OriginalSourceSyntax.olean.tmp.7`, not a Lean
proof diagnostic. Remaining group `[[7,0]]` left cessation unconfirmed and
root quarantined. Later root/process disappearance has unknown cause; no
retrospective successful cleanup or theorem acceptance is inferred.

Actual commands by this leaf: bounded cat/sed/rg/readlink/readelf reads,
Python3 SHA-256/import/theorem-header extraction, and writing only this handoff.
All tool commands returned exit 0; some initial combined output was truncated,
then relevant definitions and runner sections were reread narrowly. The source
scan found only prose occurrences of `axiom` in R104 and Interpretation;
no sorry/admit/project axiom/bypass declaration was found. This is static
inspection, not an indirect axiom audit. Readelf inspected ELF metadata only.
Actual version/Lean/Lake/checker/compiler/build/test invocations: **0**.
All 15 actual printed types and axiom results: **NOT RUN**.

300-second author bound; no renewal, no children/Astra/heavy process, no
network/install/Git operation, no generated/scratch/cache bytes. Clock sampled
2026-10-31 19:31:24 UTC; exact elapsed/RSS is not measured by this leaf and
remains primary runtime accounting. Source files, root imports, compiler,
tests/expectations, rules/config, dependencies/toolchain/manifests and shared
state/index/other workers' paths were not edited. **All writes STOPPED at
revision 1**; no background process, descendant or generated-output lease.
Independent pre-execution review and primary intake remain pending.
