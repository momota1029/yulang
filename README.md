# Yulang

Yulang is an experimental programming language that makes algebraic effects
and handlers feel like ordinary control flow.

The surface looks like a small expression-oriented scripting language: it has
method syntax, compact block notation, structs, enums, roles, user-defined
operators, loops, early return, and references. The unusual part is that many
features usually fixed in the core language are expressed through effects,
handlers, roles, and standard-library code.

Yulang is alpha-stage research software. The interpreter, playground, standard
library, and language server are usable enough to try real examples, but syntax,
type display, effect semantics, native lowering, and library APIs may still
change.

Japanese: [README.ja.md](README.ja.md)

## Try It

The fastest way to try Yulang is the browser playground:

<https://yulang.momota.pw>

To use the CLI locally, install the binary and the embedded standard library:

```bash
cargo install yulang
yulang install std
```

Run a file with the interpreter:

```bash
yulang run examples/06_undet_once.yu
```

The smallest complete program prints a user-facing string with `say`:

```yulang
say "Hello, World"
```

`run` executes the program and only prints output produced by the program
itself, such as `say` / `println`. To inspect root expression values while
experimenting, add `--print-roots`.

Check a file and print inferred public types:

```bash
yulang check examples/08_types.yu
```

Try the native backend:

```bash
yulang run --native examples/06_undet_once.yu
yulang run --mmtk examples/01_hello.yu
```

The standard library is normally installed to
`~/.yulang/lib/yulang-0.1.0/std`. `yulang run`, `yulang check`, and
`yulang server` can also install the embedded standard library automatically
on first use when neither `YULANG_STD` nor a nearby `lib/std` is available.

To use a different standard-library checkout:

```bash
export YULANG_STD=/path/to/yulang/lib/std
```

## A First Look

```yulang
use std::undet::*

struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

if all [1, 2, 3] < any [2, 3, 4]:
    point { x: 3, y: 4 } .norm2
else:
    0
```

The condition `all [1, 2, 3] < any [2, 3, 4]` is not special syntax.
`all` and `any` are ordinary library functions that produce nondeterministic
values. Lowering inserts `junction::junction` so the surrounding `if` receives
a real `bool`.

Mutable state, early return, loops, and effectful conditions use the same
basic idea: familiar notation on the surface, typed effects and small library
abstractions underneath.

## Where To Read Next

- [docs/language/overview.md](docs/language/overview.md):
  the main language overview.
- [docs/language/overview.ja.md](docs/language/overview.ja.md):
  Japanese language overview.
- [docs/status.md](docs/status.md):
  support status across parser, inference, interpreter, playground, and native
  backend.
- [docs/native-backend.md](docs/native-backend.md):
  native backend support, CLI notes, and current limits.
- [docs/native-experimental-release.md](docs/native-experimental-release.md):
  release-gate notes for the current opt-in native subset.
- [web/docs/reference/type-theory.md](web/docs/reference/type-theory.md):
  public reference for effect rows, handler hygiene, and hidden handler
  evidence.
- [docs/hidden-effect-evidence.ja.md](docs/hidden-effect-evidence.ja.md):
  implementation notes for hidden effect evidence.
- [examples/](examples):
  runnable Yulang examples.
- [lib/std/](lib/std):
  the standard library written in Yulang.

Good first examples:

- `examples/showcase.yu`: broad syntax and library tour.
- `examples/06_undet_once.yu`: nondeterminism through library effects.
- `examples/10_effect_handler.yu`: algebraic effect handlers.
- `examples/04_sub_return.yu`: local early return through `sub:`.
- `examples/11_attached_impl.yu`: attached role implementations.

## Language Server

Start the language server with:

```bash
yulang server
```

Current language-server support includes:

- hover for inferred values, locals, methods, and many type references;
- semantic tokens;
- document symbols;
- parser, lowering, and type diagnostics;
- `relatedInformation` on many type errors.

Zed support lives in [yulang-zed/](yulang-zed). The extension is not published
through the Zed extension registry yet; install it as a dev extension and
select the `yulang-zed` directory. When a `yulang` binary is available in the
worktree environment or in `~/.cargo/bin`, the extension starts
`yulang server` automatically.

The old `yulang-ls` binary is a deprecated stub that delegates to
`yulang server`.

## Native Backend

Native execution is an experimental backend with an explicit subset. The normal
user-facing entrypoint is:

```bash
yulang run --native path/to/file.yu
```

`yulang native` remains available for artifact generation and backend
debugging. The interpreter is still the semantic reference; the native backend
is an opt-in execution path rather than a replacement. See
[docs/native-backend.md](docs/native-backend.md) for the supported programs,
CLI details, and known limits. The current release-gate checklist and suggested
release note live in
[docs/native-experimental-release.md](docs/native-experimental-release.md).
The current native effects path covers string/list/bytes/path/range primitives via
runtime helper symbols. CPS repr native also preserves handler prompt exits across
effectful call return frames, so `Display`/`Debug` list construction, `loop with`
if results, `for` body `if` var writes, and range iteration with console effects
match the interpreter in the covered regression cases. Captured resumptions also
rebase handler return-frame thresholds, covering indexed ref update continuations
in CPS repr native. Unit-typed scalar roots display as `()` in the JIT display
helper even though the scalar ABI carries them as `0`. Effectful thunk forcing in
the JIT also preserves the pushed post-continuation frame while the thunk body is
evaluated, so recursive handler/resumption flows can return heap values such as
tuples without leaking visible thunk handles. Scoped routed jumps only leave the
current native activation when they need to restore an outer return-frame prefix,
which keeps open-range `for`/`last` exits from continuing recursive folds while
still allowing root value arms and nondeterministic list collection to run their
local continuations. Recursive tuple-returning handlers, block-tail loop
control, native root pretty-print for unit/bool values, open-range nondet
`.once`, and combined junction + finite nondet + method-call roots are covered
by regressions. Native remains experimental and opt-in, but the current release
gate for the documented effects subset is clear.
The shared CPS optimizer now also inlines local direct-style closure
applications, so small captured closure bodies that are constructed and applied
in the same continuation can avoid heap closure construction. It also folds
local one-shot thunk forces whose bodies are pure value computations, turning
the force into a direct resume continuation and avoiding the native
return-frame/thunk-helper path for that shape. It also collapses consecutive
deep `ForceThunk` chains, since CPS `ForceThunk` already peels nested thunks
until a non-thunk value is reached, and removes forces of structurally known
non-thunk values when their uses stay in the local continuation tail. Primitive
results are included only when the operation constructs or returns a scalar /
container value itself; `ListIndex` is intentionally excluded because it can
surface a stored thunk handle. On the 20x20 nondeterministic `.list.say`
benchmark this removes 70 redundant force statements and cuts native
`force_thunk` helper calls from 37368 to 23266. A generated-executable
`hyperfine --warmup 2 --runs 10` comparison measured 662.4ms -> 652.4ms in the
latest run, with runtime counters showing the clearer reduction. A read-only algebraic-effect
region analysis now classifies `Perform` / handler arm / `Resume` structure
without special-casing std paths. It also reports dynamic-handler candidates
where an installed handler at an effectful boundary can catch dynamic
`Perform` sites in a callee or forced thunk body; in the 20x20 nondeterministic
list benchmark this exposes the `list` handler's `branch` arm as a finite
multi-resume region through its local resume thunks. The analysis also links
local thunk arguments at direct call sites to these dynamic handler regions and
marks the 20x20 outer `list(thunk)` plus the two recursive `list(thunk)` calls
inside the handler arm as ready finite specialization seeds. A rewrite-plan
view classifies all three as `DefunctionalizeFiniteHandler`, with ordinary
callee body cloning blocked by the remaining thunk-surface / handler-boundary
protocol. This is instrumentation for later handler defunctionalization rather
than a destructive rewrite.
The next runtime-layout plan is to replace prototype heap handles with a
native `YValue` word and MMTk-backed heap, using `i63` immediates for small
integers and heap `BigInt` objects on overflow. This is a post-prototype plan,
not part of the current supported native subset. An isolated `gc_runtime`
module now pins down the first value-word/object-header/root-stack/allocator
boundary spike, including allocation helpers for the first heap object set and
red-black-tree string/list rope shapes. It also sketches monomorphic native layouts
and heap blocks with interned layout handles, raw payload buffers, field
offsets, and trace bitmaps, so `i64`/`u64` fields can stay unboxed after type
monomorphization. Static paths and atom-style symbol strings can be interned
into compact native symbols for ADT tags and symbol payload lanes, then frozen
into a collision-checked hash lookup. Native variant layouts store the tag as a
symbol field in the raw payload; the default native path still uses the
prototype helpers. The crate now depends on MMTk directly and has a thin MMTk
configuration boundary; the first configured spike uses a single-threaded
`NoGC` plan. A Yulang MMTk VM binding skeleton now compiles, with a native
object header and `YValue` slot scanner. The first
`MmtkHeap` prototype allocates the header, trace slots, and current semantic
`YObject` payload through MMTk. It can also allocate compact raw-payload
objects, compact structural `NativeHeapBlock` payloads, and compact
closure/thunk/resumption/env/frame payloads that keep tracing/stats on the MMTk
header/slot path while field reads use native layout offsets. Compact tuple and
variant values now use fixed raw-payload metadata plus trace slots instead of
the native-layout projection, avoiding layout interning on hot `list.view_raw`
node construction. Compact record values now store field-name metadata in raw
payload bytes and field values in trace slots. Compact string/list rope node
metadata is also encoded in raw payloads and read through the header/payload
path, so hot rope operations no longer need semantic object projection. Compact
list `len`/index/view/debug paths now read metadata and trace slots directly
instead of flattening or rebuilding trees on the hot path.
The MMTk lane can materialize captured native CPS control-stack
snapshots as compact `ControlStack` heap objects with trace slots for reachable
MMTk `YValue` children; pointer-shaped prototype values are filtered before
object-table lookup when they are outside the tracked MMTk heap range. That
mirror is opt-in with `YULANG_MMTK_CPS_CONTROL_STACK_SNAPSHOTS=1`, because the
default `NoGC` benchmark lane should not pay for a GC root mirror while
collection is still unwired. The
MMTk runtime also has a dedicated compact CPS control helper module that can
allocate closure/thunk/resumption bodies as fixed raw-payload MMTk objects and
read code/env slots without native-layout projection. The helper payload now
stores its own env length and the helper context uses a raw thread-local context
pointer instead of a `RefCell<Option<_>>` borrow on every call. That path is
covered by direct helper tests and is now used by the stable `--mmtk` lane for
guarded compact closure/thunk control bodies. `YULANG_MMTK_CPS_CONTROL_OBJECTS=0`
opts back out to the prototype native control helpers. The compact control
object path is still guarded because it does not yet store non-empty native
handler/guard snapshots directly: compact thunks are created only when the
native control capture context is empty, and effect-boundary conversion rebuilds
those thunks with an explicit empty prototype snapshot instead of accidentally
capturing the boundary-time handler/guard context. Control objects with
non-empty captured snapshots still fall back to the prototype helper path.
There is a narrower helper-level experiment behind
`YULANG_MMTK_CPS_CONTROL_THUNK_SIDECARS=unsafe` that allocates a compact thunk
surface while storing its creation-time native thunk snapshot in a side table;
direct helper tests cover that bridge, and the native force helper now delegates
back to MMTk force when a mixed native path receives a compact thunk. The native
CPS runtime now exposes compact-control capture requirements as a bitmask, and
the MMTk control helper treats abort/scope-return state as non-local flow that
must stay on the prototype thunk path even when the sidecar experiment is
enabled. Full lowering keeps the sidecar bridge disabled until non-local flow
through compact apply/force is completed.
The remaining migration is to replace more transitional
semantic payload users with these compact paths; the heap read API is already
split into header and trace-child projection so tracing no longer depends on
reading the full semantic payload. A
small MMTk-backed native context now exposes raw `YValue` word helpers for unit,
bool, int arithmetic/compare, int/bool/float string conversion, red-black-tree
string construction/concat/index/range/splice/length/equality, compact
bytes/path conversion helpers, and compact tuple/record/variant plus chunked
red-black list construction/access/view,
including record default/has/without and list range/splice. The runtime also
registers a parallel `yulang_mmtk_cps_*` helper symbol set for a future
all-`YValue` CPS lane; the current `yulang_cps_*` symbols still use the
prototype scalar/handle ABI. A minimal JIT smoke now calls the
MMTk CPS helper symbols directly and passes `YValue` strings, bytes, and tuples
through Cranelift. The CPS repr Cranelift path also has an opt-in
`CpsReprCraneliftOptions::mmtk_yvalue_primitives()` mode that routes the current
runtime primitive family and tuple/record/variant structural statements through
the MMTk helper set where the ABI already uses `YValue` payloads. In that
opt-in lane, Yulang `int`, bool, and unit values are carried as tagged
`YValue` words, while float operations still use unboxed `f64` inputs and box
their boolean results back into `YValue`. Fixed-width `i64`/`u64` lanes are
available in the native layout spike, but they are not source-level Yulang
types yet. `yulang run --mmtk` exposes this lane for benchmark work; the
default CPS path remains on the prototype scalar/handle ABI. The native CPS
runtime keeps handler, guard, and return-frame stacks as mutable vectors with
cached snapshots. The first snapshot after mutation still clones the active
stack; attempts to replace that with `Rc<Vec>` copy-on-write or `im::Vector`
made the nondeterminism benchmark slower, so a real capture optimization still
needs a dedicated stack representation. Under the MMTk lane those snapshots
can receive compact GC heap mirrors for root tracking when the snapshot mirror
env flag is enabled.

The current MMTk benchmark lane has been brought back into the default native
effects lane's band for the small nondeterminism list benchmarks, but it is not
yet a general win. Compact control entries are cached at allocation time so
force/apply no longer project the MMTk object table and raw payload on every
hot control call. A generated-executable `hyperfine` run on 2026-05-18 shows
that this brings `(each 1..20 + each 1..20).list.len` back into the native band:
native 372.1ms / MMTk opt-out 375.3ms / MMTk guarded 370.9ms. `.list.say` still
has a native lead at native 639.7ms / MMTk opt-out 688.3ms / MMTk guarded
678.7ms, and `examples/showcase.yu` remains native 5.3ms / MMTk opt-out 6.1ms /
MMTk guarded 6.5ms. Later snapshot-sharing work gives control snapshots an
append node and moves the active guard stack to a `base snapshot + mutable tail`
representation, so thunk/closure/resumption capture no longer clones the full
guard stack after every guard push. On `.list.say`, measured guard snapshot
clones drop from 410,671 items to zero, and a direct generated-executable
comparison against the older guarded binary improves MMTk from 758.9ms to
677.9ms. Native still leads around 641.1ms on the same benchmark, so this is
not yet the Python/JS-class target. Later GC-side probes kept only small safe
runtime reductions: compact-list `len`/`get`/merge no longer reread the same
list metadata on their entry path, the thunk-sidecar env flag is cached after
the first read, and an unsafe thunk-context experiment can keep the compact
thunk body while storing only the captured native handler/guard context in a
small opaque side table. A direct-mapped compact-control entry cache, unsafe
thunk sidecars, thunk-context side tables, and compacting closures with pending
handler envs were measured and not adopted as the default: they reduce some
counters but lose on wall-clock time for the 20x20 list benches or still hit the
known full-lowering non-local-flow hole. The partial integration boundary is
still visible: compact control objects still fall back to the prototype helper
path whenever a non-empty native capture context must be preserved by the stable
lane, boundary thunks cross back through a prototype thunk, some runtime values
still cross helper/prototype boundaries, and captured control snapshots still
clone on first snapshot after mutation. The next runtime shape has a first
isolated payload model: `ControlState` is now a distinct GC object kind, and a
separate GC-control thunk payload stores `{ code, context, env }` with normal
MMTk trace edges from thunk to control state and captured heap values. This is
not yet connected to CPS lowering; it is the side-by-side runtime nucleus for a
future ctx-passing control ABI. The first ctx-style helper surface is also in
place for guards: `gc_control_empty_state`, `gc_control_push_guard`,
`gc_control_find_guard`, and `gc_control_peek_guard` operate on an explicit
control-state word instead of the native TLS guard stack. For GC tuning probes,
generated MMTk executables also understand `YULANG_MMTK_CPS_HEAP_STATS=1`,
which prints allocation totals by object kind and compact storage shape after
each root.
Beating the default native path consistently requires finishing non-local-flow
aware, snapshot-carrying compact control objects, moving remaining hot metadata
into object headers or raw payloads, removing prototype fallback from hot runtime
values, and replacing clone-on-capture control snapshots with a dedicated
snapshot-sharing stack.

## Development

Run representative Rust test suites:

```bash
cargo test -p yulang-runtime -p yulang-infer --lib
```

Build the playground locally:

```bash
cd web/playground
npm ci
npm run build
```

Run an inline Yulang program:

```bash
yulang run --print-roots <<'YU'
use std::undet::*

(each [1, 2, 3] + each [4, 5, 6]).once
YU
```

## Repository Layout

- `crates/yulang`: CLI.
- `crates/yulang-parser`: parser and syntax tree support.
- `crates/yulang-sources`: source sets, realms, compilation units, and syntax artifacts.
- `crates/yulang-typed-ir`: typed intermediate representation and principal-type evidence.
- `crates/yulang-infer`: type inference and principal-type export.
- `crates/yulang-runtime`: runtime IR, monomorphization, and interpreter.
- `crates/yulang-native`: native backend.
- `crates/yulang-wasm`: WebAssembly API used by the playground.
- `examples`: executable examples for the current language implementation.
- `lib/std`: standard library written in Yulang.
- `web/playground`: Vite-based browser playground.
- `web/docs`: reference documentation.
- `notes`: bug, refactor, and progress notes.

## Status

Yulang is pre-release research software. Syntax, type output, runtime IR, the
interpreter, and the standard library may change without compatibility
promises. [docs/status.md](docs/status.md) describes the current support
matrix; broader limitations are noted there and in
[docs/native-backend.md](docs/native-backend.md).

## License

Licensed under either of:

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
- MIT License ([LICENSE-MIT](LICENSE-MIT))

at your option.
