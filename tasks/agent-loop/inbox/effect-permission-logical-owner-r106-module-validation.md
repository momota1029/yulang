# R106 module-faithful validation plan — revision 1

Status: **PLAN / UNEXECUTED / FROZEN / WRITES STOPPED**.
Assignment `/root/r106_module_validation_plan`, registered `lean_prover` leaf;
sole author this leaf, no descendants. Requested/effective model and effort:
UNKNOWN to this leaf. Actual parent NEW_TASK and this handoff establish session
activity. Sole write lease: this handoff. No Lean source, scratch, generated
output, cache, configuration, dependency, Git or central-state write occurred.

Sprint `EFFECT-PERMISSION-SOURCE-ADMISSION/20261101-R106`; corrected contract
`tasks/agent-loop/sprints/effect-permission-source-admission-20261101-r106.md`,
SHA-256 `4ba4111669f060e9df96ce68b112a8a1d63320dc5857f5e8b65fdcf2113792f5`.
Baseline supplied by primary: `80d34e645`. The initial contract counted 13
dependencies plus bridge; actual closure is **12 dependencies plus bridge**.
Luna acknowledged and corrected the contract before this freeze. Exactly 13
Lean calls are proposed, never 14; no extra version/audit/checker call.

## Original obligation and scope

Read root AGENTS.md/AGENTS.pre-sprint.md, goal-driven-sprints, compact state,
assignment protocol, selected contract, yulang-lean-proofs and its source and
execution references. Semantic selection is source-Generalize decision §§2–3,
selecting construction §§3–5, particularly §3.3's ViewLogic before challenges,
once-retained Shared, and description-owned EventProof under actual telescopes.
The source manuscript's opening correction distinguishes fixed old evidence
from the executing owner and leaves general source/native correspondence open;
it is an unreviewed research manuscript, not added semantic authority.

Original parent: `2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5:
for every supported original source, lawful finite construction history and
actual retained qualified extrusion, preserve source conclusions and required
coverage at original lexical/type/event scopes, with one lawful joint strategy
and unchanged fixed fields. Apply immutable birth-level induced-SCC correction
§§2–6. No quantifier, constructor, optional record, method selection, complete
Call/effect requirement, scope, provider or shared witness is removed here.
The cited external Simple-sub PDF was not needed/read for this execution plan;
no new claim about its proof is made.

| Source | SHA-256 |
| --- | --- |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `docs/yulang-source-type-safety-ja.tex` | `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166` |
| `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| `notes/design/2026-10-24-birth-level-scc-intrusion.md` | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |
| `tasks/agent-loop/inbox/effect-permission-logical-owner-r105-proof.md` | `32f3fcf62b5fbc14eb040d570e0752e0ab8a8ad65e44f5f6c2f7b65f14baf422` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |

## Exact direct-import DAG and frozen order

Every short name below denotes `YulangClosure.<name>` and the unchanged file
`notes/theory/lean/YulangClosure/<name>.lean`. Init/Std are pinned distribution
modules. Implicit Init is also supplied by that distribution. This is the full
project import closure, obtained by recursive reading of actual import lines;
all project edges point to earlier rows. The byte hashes are in the executable
plan below, avoiding two divergent hash inventories.

| Call | Module | Exact explicit direct imports |
| --- | --- | --- |
| 1 | OriginalSourceSyntax | Std |
| 2 | OriginalSourceGeneration | OriginalSourceSyntax |
| 3 | SourceLogicalOccurrencesR104 | OriginalSourceGeneration |
| 4 | NativeClosureEnvironment | Init |
| 5 | Contracts | Init |
| 6 | SourceIdentityWorld | NativeClosureEnvironment; Contracts |
| 7 | SourceFunctionMembership | SourceIdentityWorld |
| 8 | NativeDictionaryDenotation | Init |
| 9 | OriginalSourceInterpretation | OriginalSourceGeneration; SourceFunctionMembership; NativeDictionaryDenotation |
| 10 | OriginalSourceEnvironment | OriginalSourceInterpretation |
| 11 | SourceSignatureConstruction | OriginalSourceSyntax |
| 12 | OriginalSourceEvents | OriginalSourceEnvironment; SourceSignatureConstruction |
| 13 | SourceLogicalOwnerBridgeR105 | SourceLogicalOccurrencesR104; OriginalSourceEvents |

The bridge is 19,998 bytes with its original hash below. No source-copy,
concatenation, import stripping, alpha-renaming or declaration edit occurs.
Each process starts a fresh command environment. In particular,
NativeDictionaryDenotation imports Init alone; Contracts.Step cannot enter its
command scope from a previous process. OriginalSourceInterpretation then
imports both compiled modules normally. This removes the observed flattening
artifact without claiming that any source theorem will pass.

Pinned source inspection: installed distribution
`src/lean/Lean/Util/Path.lean:95–110` appends the builtin library after LEAN_PATH;
`:146–159` derives the true module name from --root and the input filename.
`src/lean/Lean/Shell.lean:150–156` specifies -o and --root.
`src/lean/Lean/Environment.lean:1902–1918` writes one .olean for these legacy
files (none has a `module` header); the new module syntax can write sidecars.
No new-module flag, sidecar suppression, trust override or compiler option is
introduced. The file-size guard below is conservative even if five normal
sidecars per module were produced: 65 * 16 MiB = 1,040 MiB < 2 GiB. Unexpected
files stop the batch. No project .olean is read outside the unique output root.
Init/Std and their distribution dependencies are necessarily read from the
pinned standard library; they are not project cache reuse.

## Executable, import resolution and resources

Native executable (read/hash only, not invoked):
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`,
9,024 bytes, SHA-256
`bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.
Actual version invocation: **NOT RUN**. Project pin is
`leanprover/lean4:v4.35.0`, no external packages. The earlier R105 actual
execution identifies this executable as the pinned distribution; this plan
rechecks its bytes, not a new version receipt. Distribution direct Lean
shared-library hashes are pinned in the runner. This does not claim to hash
the entire standard-library transitive artifact closure or OS runtime.

The one primary-owned batch must be serialized with Cargo and independently
reviewed before execution. No Lake/helper/default build is authorized. The
skill's helper would add builds/audits and use a cache, so is inapplicable to
this packet. Existing bridge #check/#print commands supply its sole audit.

CPU affinity is exactly CPU 0; -j1 and LEAN_NUM_THREADS=1 are retained. Each
native Lean call has GNU timeout's SIGKILL deadline at 60 seconds. Sequential
per-call wall charge conservatively bounds aggregate active Lean time; stop at
1,200 seconds, and 13 * 60 = 780 seconds already lies below that ceiling.
There is no reset/retry allowance. Time/timeout/taskset are wrappers, not extra
Lean calls. Keep the whole batch within the remaining 2,400-second sprint budget.

- Lean allocator policy: -M1024, unchanged.
- Additional conservative RSS acceptance/abort threshold: 1 GiB for sampled
  process-group total and GNU time's completed-call maximum RSS. Polling may
  overshoot between samples; it is not a cgroup hard memory limit. No hard
  OS RSS guarantee is asserted. Any threshold breach is failure, not a retry.
- Generated root: exactly
  `/dev/shm/yulang-source-owner-module-validation-20261101-r106`, initially
  absent. Never reuse/delete an existing root. Each output file has inherited
  RLIMIT_FSIZE=16 MiB; at most 65 allowed artifacts, hence structural file-data
  bound 1,040 MiB plus small directory metadata, with a separate 2-GiB
  allocated/logical-size check before/after calls and during monitoring.
- No disk logs/scratch. stdout/stderr stay in a bounded 8-MiB per-call pipe
  collection and are printed in full to the primary tool receipt. A log-size
  breach stops the process; retain captured failure and identify incomplete
  output. This is not a successful audit. Primary owns durable receipt paths.
- Finally kill/reap the active group, verify group absence, hash/list generated
  artifacts, delete only the newly owned exact root, then print an explicit
  lexists=false cleanup receipt. Cleanup/group-cessation failure blocks further
  execution and integration. A preflight-existing root is preserved untouched.

Read-only preparation observed CPU 0 in allowed affinity, root absent, and
16,751,607,808 free bytes in /dev/shm. These observations must be revalidated;
they are not execution/cleanup receipts.

## Exact proposed command list and bounded runner (NOT EXECUTED)

Luna may run the following Python here-document once only after fresh review.
It materializes no script. For every ordered row the sole subprocess argv is:

```text
/usr/bin/timeout --signal=KILL 60s /usr/bin/taskset -c 0 /usr/bin/time -v /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 --root=/home/momota1029/rust/yulang/notes/theory/lean -o /dev/shm/yulang-source-owner-module-validation-20261101-r106/YulangClosure/<name>.olean /home/momota1029/rust/yulang/notes/theory/lean/YulangClosure/<name>.lean
```

The 13 concrete `<name>` substitutions, ordered hashes, and expected imports
are the literal rows below. No --stdin, --version, --run, --trust, alternate
Lean executable or extra audit call occurs. An empty inherited environment is
rebuilt explicitly; LEAN_PATH contains only the fresh root, with no empty
element/current directory/.lake. The builtin library is checked for absence
of a shadow YulangClosure package.

```sh
python3 - <<'PY'
import hashlib, json, os, re, resource, selectors, shutil, signal
import subprocess, sys, time
from pathlib import Path

REPO = Path('/home/momota1029/rust/yulang')
PROJECT = REPO / 'notes/theory/lean'
DIST = Path('/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0')
LEAN = DIST / 'bin/lean'
ROOT = Path('/dev/shm/yulang-source-owner-module-validation-20261101-r106')
MIB = 1024 * 1024
ROWS = [
 ('OriginalSourceSyntax', '3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1', ['Std']),
 ('OriginalSourceGeneration', '126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef', ['YulangClosure.OriginalSourceSyntax']),
 ('SourceLogicalOccurrencesR104', '0e7a42d66578388585a5abd1da12c77a9d7d46823687ed511d26e359b3078f39', ['YulangClosure.OriginalSourceGeneration']),
 ('NativeClosureEnvironment', '39aa5cefa078dd423e54f0d9790f9a48e136326742e01f65149f317c907be957', ['Init']),
 ('Contracts', '2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e', ['Init']),
 ('SourceIdentityWorld', '6019fd9d57cde50183e016bd0c72de2c6eee72009065d85119fb0348dbcf0168', ['YulangClosure.NativeClosureEnvironment', 'YulangClosure.Contracts']),
 ('SourceFunctionMembership', '8d370ee57e486ae48607d1bab493ae5135f28bf8a5a7ff1b0ef240fc0247e424', ['YulangClosure.SourceIdentityWorld']),
 ('NativeDictionaryDenotation', 'd44a78f08970a09ca4c3e99a1d8dea846286a299d1a2bc91ec3b5e0eabea9070', ['Init']),
 ('OriginalSourceInterpretation', 'feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef', ['YulangClosure.OriginalSourceGeneration', 'YulangClosure.SourceFunctionMembership', 'YulangClosure.NativeDictionaryDenotation']),
 ('OriginalSourceEnvironment', '0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132', ['YulangClosure.OriginalSourceInterpretation']),
 ('SourceSignatureConstruction', 'ed07890e29b4dcb38cabd18ec0e196efde9e95c64902942a9906a470b38c3311', ['YulangClosure.OriginalSourceSyntax']),
 ('OriginalSourceEvents', 'cfd5f502a1e68a97e27e11a75400fae8789f167c92596aedb08ef7dfbb724342', ['YulangClosure.OriginalSourceEnvironment', 'YulangClosure.SourceSignatureConstruction']),
 ('SourceLogicalOwnerBridgeR105', '6fecc134ac2009392f043331eb4d1a3dd479668208991e60c8a5d339e69b45b4', ['YulangClosure.SourceLogicalOccurrencesR104', 'YulangClosure.OriginalSourceEvents']),
]
PINS = {
 REPO / 'tasks/agent-loop/sprints/effect-permission-source-admission-20261101-r106.md': '4ba4111669f060e9df96ce68b112a8a1d63320dc5857f5e8b65fdcf2113792f5',
 REPO / 'tasks/agent-loop/inbox/effect-permission-logical-owner-r105-proof.md': '32f3fcf62b5fbc14eb040d570e0752e0ab8a8ad65e44f5f6c2f7b65f14baf422',
 PROJECT / 'lean-toolchain': 'ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c',
 PROJECT / 'lakefile.toml': '212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4',
 PROJECT / 'lake-manifest.json': '058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3',
 LEAN: 'bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38',
 DIST / 'lib/lean/libInit_shared.so': '7831b707e868cee76c353d26649fbd8981b2f4d7e0329af55bbf4fa9e0c69350',
 DIST / 'lib/lean/libleanshared.so': 'efef27df56f2197139afe12f1a2b63913a05f1aba81ce88824c44100431ed8c4',
 DIST / 'lib/lean/libleanshared_1.so': '691bf49d9e542a15808fad9d1f8c5df45860166f77efa57961b5335e65a3a0ed',
 DIST / 'lib/lean/libleanshared_2.so': '141cbfdb3bc2016cd68e0bebc2e5494818213b462ed985afa6d975d4872fb8ec',
 DIST / 'lib/lean/Init.olean': '84ffd94782b2f2f65408dee401a4332bfa7c3274abc7b1040cea7d7a307314f5',
 DIST / 'lib/lean/Std.olean': '81655926012444f214099f1ed6610ed63ade63f9e91b2e5af6689acd9cf1b400',
 Path('/usr/bin/time'): '3b11dec50514a8473e9f6efa7a34d584d0657538c09988f61b72d38ad4991a10',
 Path('/usr/bin/timeout'): '12690a043dfd555a6c14ccc1564f5649c18f1762c0d6ff66729948130898ec52',
 Path('/usr/bin/taskset'): 'a431738fadddc2e2326c8ab81843e72f4011658379381aef1502a6ddb1c1115b',
}
for name, digest, _ in ROWS:
    PINS[PROJECT / 'YulangClosure' / (name + '.lean')] = digest

def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(MIB), b''):
            h.update(block)
    return h.hexdigest()

def freeze_check():
    for path, digest in PINS.items():
        if not path.is_file() or sha(path) != digest:
            raise RuntimeError('PIN_MISMATCH ' + str(path))

def group_members(pgid):
    found = []
    for entry in Path('/proc').iterdir():
        if not entry.name.isdigit():
            continue
        try:
            fields = (entry / 'stat').read_text().rsplit(')', 1)[1].split()
            if int(fields[2]) == pgid and fields[0] != 'Z':
                status = (entry / 'status').read_text()
                rss = re.search(r'^VmRSS:\s+(\d+) kB$', status, re.M)
                found.append((int(entry.name), int(rss[1]) if rss else 0))
        except (FileNotFoundError, ProcessLookupError):
            pass
    return found

def kill_group(pgid):
    try:
        os.killpg(pgid, signal.SIGKILL)
    except ProcessLookupError:
        pass

def files_and_size():
    files = []
    logical = allocated = 0
    allowed = set()
    for name, _, _ in ROWS:
        for suffix in ('.olean', '.olean.server', '.olean.private', '.ir', '.ir.sig'):
            allowed.add('YulangClosure/' + name + suffix)
    for path in ROOT.rglob('*'):
        if path.is_symlink():
            raise RuntimeError('UNEXPECTED_SYMLINK ' + str(path))
        if path.is_file():
            rel = path.relative_to(ROOT).as_posix()
            if rel not in allowed:
                raise RuntimeError('UNEXPECTED_OUTPUT ' + rel)
            st = path.stat()
            logical += st.st_size
            allocated += st.st_blocks * 512
            files.append(path)
    if len(files) > 65 or max(logical, allocated) > 2 * 1024**3:
        raise RuntimeError('OUTPUT_CAP ' + repr((len(files), logical, allocated)))
    return files, logical, allocated

def child_limits():
    resource.setrlimit(resource.RLIMIT_FSIZE, (16 * MIB, 16 * MIB))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

ENV = {'PATH': '/usr/bin:/bin', 'LC_ALL': 'C',
       'LEAN_PATH': str(ROOT), 'LEAN_NUM_THREADS': '1'}
owned = False
active = None
active_pgid = None
charged = 0.0
completed = 0
failed = None
try:
    freeze_check()
    if os.path.lexists(ROOT):
        raise RuntimeError('PREEXISTING_ROOT_PRESERVED')
    if 0 not in os.sched_getaffinity(0):
        raise RuntimeError('CPU_0_UNAVAILABLE')
    if (DIST / 'lib/lean/YulangClosure').exists() or (DIST / 'lib/lean/YulangClosure.olean').exists():
        raise RuntimeError('BUILTIN_PROJECT_SHADOW')
    disk = os.statvfs(ROOT.parent)
    if disk.f_bavail * disk.f_frsize < 2 * 1024**3:
        raise RuntimeError('INSUFFICIENT_SHM')
    seen = set()
    for name, _, imports in ROWS:
        text = (PROJECT / 'YulangClosure' / (name + '.lean')).read_text()
        actual = [word for line in re.findall(r'^import\s+([^\n]+)', text, re.M) for word in line.split()]
        if actual != imports or re.search(r'^\s*module\b', text, re.M):
            raise RuntimeError('IMPORT_OR_HEADER_CHANGED ' + name)
        for dep in imports:
            if dep.startswith('YulangClosure.') and dep not in seen:
                raise RuntimeError('NON_TOPOLOGICAL ' + name)
        seen.add('YulangClosure.' + name)
    ROOT.mkdir(mode=0o700)
    owned = True
    (ROOT / 'YulangClosure').mkdir(mode=0o700)
    for index, (name, _, imports) in enumerate(ROWS, 1):
        freeze_check()
        files_and_size()
        if charged + 60 > 1200:
            raise RuntimeError('AGGREGATE_BUDGET')
        for dep in imports:
            if dep.startswith('YulangClosure.'):
                if not (ROOT / (dep.replace('.', '/') + '.olean')).is_file():
                    raise RuntimeError('FRESH_IMPORT_MISSING ' + dep)
        output = ROOT / 'YulangClosure' / (name + '.olean')
        if output.exists():
            raise RuntimeError('OUTPUT_REUSE ' + name)
        cmd = ['/usr/bin/timeout', '--signal=KILL', '60s',
               '/usr/bin/taskset', '-c', '0', '/usr/bin/time', '-v', str(LEAN),
               '-j1', '-M1024', '--root=' + str(PROJECT), '-o', str(output),
               str(PROJECT / 'YulangClosure' / (name + '.lean'))]
        print('CALL', index, json.dumps(cmd), flush=True)
        started = time.monotonic()
        active = subprocess.Popen(cmd, cwd=PROJECT, env=ENV, stdin=subprocess.DEVNULL,
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                    start_new_session=True, preexec_fn=child_limits)
        active_pgid = active.pid
        collected = {'stdout': bytearray(), 'stderr': bytearray()}
        monitored_peak = 0
        reason = None
        selector = selectors.DefaultSelector()
        for stream, label in ((active.stdout, 'stdout'), (active.stderr, 'stderr')):
            os.set_blocking(stream.fileno(), False)
            selector.register(stream, selectors.EVENT_READ, label)
        while selector.get_map() or active.poll() is None:
            elapsed = time.monotonic() - started
            members = group_members(active_pgid)
            monitored_peak = max(monitored_peak, sum(rss for _, rss in members))
            try:
                files_and_size()
            except Exception as exc:
                reason = reason or str(exc)
            if monitored_peak > 1024 * 1024:
                reason = reason or 'RSS_CAP'
            if elapsed > 60.1:
                reason = reason or 'WALL_DEADLINE_BACKSTOP'
            if charged + elapsed > 1200:
                reason = reason or 'AGGREGATE_BUDGET'
            if reason:
                kill_group(active_pgid)
            for key, _ in selector.select(0.02):
                block = os.read(key.fileobj.fileno(), 65536)
                if not block:
                    selector.unregister(key.fileobj)
                    key.fileobj.close()
                else:
                    remaining = 8 * MIB - sum(map(len, collected.values()))
                    collected[key.data].extend(block[:max(0, remaining)])
                    if len(block) > remaining:
                        reason = reason or 'LOG_CAP_OUTPUT_INCOMPLETE'
                        kill_group(active_pgid)
            if elapsed > 65:
                reason = reason or 'CESSATION_OR_PIPE_TIMEOUT'
                kill_group(active_pgid)
                break
        selector.close()
        rc = active.wait(timeout=2)
        elapsed = time.monotonic() - started
        charged += elapsed
        leftovers = group_members(active_pgid)
        if leftovers:
            kill_group(active_pgid)
            reason = reason or ('GROUP_NOT_EMPTY ' + repr(leftovers))
        print('STDOUT_BEGIN', name, flush=True)
        sys.stdout.buffer.write(collected['stdout']); sys.stdout.buffer.flush()
        print('\nSTDOUT_END', name, flush=True)
        print('STDERR_BEGIN', name, flush=True)
        sys.stdout.buffer.write(collected['stderr']); sys.stdout.buffer.flush()
        print('\nSTDERR_END', name, flush=True)
        matches = re.findall(rb'Maximum resident set size \(kbytes\):\s*(\d+)', collected['stderr'])
        peak = int(matches[-1]) if matches else None
        print('RESULT', json.dumps({'call': index, 'name': name, 'exit': rc,
              'wall_seconds': elapsed, 'aggregate_charge_seconds': charged,
              'sampled_group_peak_kib': monitored_peak, 'time_peak_kib': peak,
              'abort_reason': reason, 'remaining_members': leftovers}), flush=True)
        active = None
        if leftovers:
            raise RuntimeError('GROUP_CESSATION_FAILURE')
        active_pgid = None
        if reason or rc != 0 or peak is None or peak > 1024 * 1024 or not output.is_file():
            raise RuntimeError('CALL_FAILED ' + name)
        files_and_size()
        freeze_check()
        completed += 1
    print('BATCH_COMPILE_EXIT_0', completed, 'AUDIT_REQUIRES_RECEIPT_REVIEW', flush=True)
except BaseException as exc:
    failed = repr(exc)
    print('BATCH_FAILURE', failed, flush=True)
finally:
    cleanup_safe = True
    if active_pgid is not None:
        kill_group(active_pgid)
        if active is not None:
            try:
                active.wait(timeout=2)
            except subprocess.TimeoutExpired:
                print('REAP_FAILURE', active_pgid, flush=True)
                failed = failed or 'REAP_FAILURE'
        leftovers = group_members(active_pgid)
        print('FINAL_GROUP_MEMBERS', leftovers, flush=True)
        if leftovers:
            failed = failed or 'GROUP_CESSATION_FAILURE'
            cleanup_safe = False
    if owned and cleanup_safe:
        try:
            for path in sorted(ROOT.rglob('*')):
                if path.is_file() and not path.is_symlink():
                    print('ARTIFACT', str(path.relative_to(ROOT)), path.stat().st_size, sha(path), flush=True)
            shutil.rmtree(ROOT)
        except BaseException as exc:
            failed = failed or ('CLEANUP_EXCEPTION ' + repr(exc))
        present = os.path.lexists(ROOT)
        print('CLEANUP', json.dumps({'root': str(ROOT), 'lexists': present,
              'completed_calls': completed, 'aggregate_charge_seconds': charged}), flush=True)
        if present:
            failed = failed or 'CLEANUP_FAILURE'
    elif owned:
        print('ROOT_QUARANTINED_GROUP_CESSATION_UNCONFIRMED', str(ROOT), flush=True)
    else:
        print('NO_ROOT_OWNERSHIP_NO_CLEANUP', flush=True)
sys.exit(1 if failed else 0)
PY
```

The runner is constructed and **not run or self-certified**. Only a fresh
review may authorize its exact bytes. An inability to enforce/observe these
limits, an unfamiliar output, a hash drift, or a runner exception returns the
failure to Luna without another Lean invocation. No installation is allowed.

## Declaration audit and application to the parent

All 15 bridge theorem declarations already have adjacent, fully qualified
`#check @...` and `#print axioms ...` commands in unchanged lines 330–359.
Every name has prefix `YulangClosure.OriginalSource.LogicalOwnerBridgeR105.`:

```text
forest_head_route
forest_sibling_route
choice_right_route
advance_erases
follow_erases
advance_owner
follow_owner
app_route_exact
app_viewlogic_separate
app_bridge
lambda_body_route_exact
body_telescope_binders
lambda_body_owner
body_key_coordinates
lambda_body_bridge
```

Actual printed theorem types: **NOT RUN, all 15**. Actual complete axiom
reports: **NOT RUN, all 15**. The primary must retain every printed type and
complete axiom line; only propext, Classical.choice and Quot.sound are allowed.
Missing/truncated output, sorryAx, project axioms or an unknown declaration is
a failed audit even if the process exits zero. These are source `theorem`
declarations, not Prop definitions. The runner's final compile message does
not inspect/adjudicate theorem output; receipt review is a separate gate.

Represented: unrestricted Position/Bool steps and finite routes over every
current RuleTree/RuleForest constructor; owner-catalogue membership preservation;
exact App ViewLogic and Lambda EventProof at original annotation positions,
both formal entry modes, arbitrary formal annotation/pattern/body/context and
repeated sites; full logical anchors and native binder telescope projections;
body key's original route/binder/parents/occurrence/raw coordinates. ViewLogic
has empty binderOwner; bodyOwner is descriptionProof, not actualEvent.

Omitted from the claim (not removed from the parent language): concrete
LocalAdmissions.logical inhabitants, source judgment admissibility, interpreted
formal/header laws, semantic App/Lambda witness satisfaction, runtime event
admission, native generation/solver/consumer realization, A/B, full effect
hygiene and production. Existing source syntax includes record spread, method
selection, handlers/operation arms and constructor patterns; this plan neither
narrows that syntax nor claims new semantic proofs for those forms.

If accepted, `app_bridge` and `lambda_body_bridge` tie R104's syntactic
occurrence to the original owner catalogue and exact combined traversal.
They do not yield the source-admissible joint strategy required by parent §5.
First remaining semantic premise: construct actual logical witness admission
at these exact scoped occurrences, using
`YulangClosure.OriginalSourceEnvironment.LocalAdmissions.logical` and
`DataAdmitted` (not assuming their concrete instances), then prove the lawful
joint equality lift through publication/use for actual source-generated native
demands. Owner: Luna's source/proof intake. `YulangClosure.SourceProblem.`
`InferenceSoundness`, `SourceScopedCoverage` and `PrincipalCoverage` remain
proposition definitions with the same-source-scope/shared-witness requirements;
the mere presence of these definitions or `LocalLaws` closes nothing.

Stable handoff request `R106-MODULE-VALIDATION-1`: primary obtains independent
review of this frozen plan, executes its sole batch only after PASS, freezes
all exact commands/exits/complete outputs/resource and cleanup receipts, then
obtains fresh receipt review. Falsifiers: first failing module, absent fresh
import, source/runtime hash drift, resource breach, incomplete theorem output,
unapproved axiom, or cleanup/group-cessation failure. Stop immediately; leave
all later modules and all parent obligations open.

## Failure evidence, actual work and stop receipt

Material inherited failure is preserved in R105 outcome §§Lean execution and
review: flattened invocation exited 1 in 17.643051 seconds, maximum RSS 972,920
KiB, no swap; first error stdin line 3274 = NativeDictionaryDenotation line 29,
where unqualified auto-implicit Step resolved to earlier YulangClosure.Step.
100-error limit was reached before the R105 declarations at stdin line 8491.
No R105 theorem type or axiom report was produced. This plan is not a repair
receipt or a reinterpretation of that failure as bridge rejection/success.

Actual leaf commands: read-only cat/sed/rg, Python recursive import/hash/stat
inspection, readelf dynamic-section inspection; apply_patch to this one handoff.
All productive reads/hash inspections exited 0. One search glob for an R104
history path exited 2 (no such path); its relevant R105 outcome search completed.
One optional installed C++ serializer locator was absent; Lean's actual installed
Environment.lean supplied the writeModule definition instead. Broad rg output
included prose uses of "admitted"; these were inspected rather than treated as
proof holes. No sorry/admit/project axiom/bypass declaration was found in the
13-file cone; indirect axiom acceptance remains NOT RUN. The actual checker,
build, version, test and Lean/Lake invocation counts are all **zero**.

Resources spent: one leaf, read/hash work, zero heavy processes, zero Lean
seconds, zero Cargo calls, zero generated bytes, zero Astra, no descendants.
No accurate assignment wall timer was supplied; elapsed leaf wall is UNKNOWN,
not zero. Remaining authorized Lean execution belongs entirely to Luna, at
most the single 13-call batch and original sprint envelope. No scratch or
generated path is held by this leaf. **All writes STOPPED at this frozen
revision; no descendants or background process remain.** This is a candidate
execution plan pending independent review and primary intake, not theorem
closure, source/native correspondence or production authority.
