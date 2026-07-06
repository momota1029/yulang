# Yulang

**Control flow your type system can actually see — in a language that still
feels like a script.**

Yulang is an expression-oriented language built on algebraic effects and full
type inference. The things most languages weld into the core — early return,
loops, mutable state, exceptions, even nondeterministic search — are ordinary
typed effects here, mostly defined in the standard library. That buys you two
things at once: control flow you normally can't have, and a compiler that
tells you exactly where any of it is being used.

**[Try it in your browser](https://yulang.momota.pw/)** — no install needed.
Japanese: [README.ja.md](README.ja.md)

```yulang
// every Pythagorean triple under 15 — an ordinary expression
{
    my a = each 1..15
    my b = each a..15
    my c = each b..15
    guard: a * a + b * b == c * c
    (a, b, c)
}.list  // => [(3, 4, 5), (5, 12, 13), (6, 8, 10), (9, 12, 15)]
```

`each` picks one element, `guard:` prunes failing branches, and `.list`
collects every result. No macro, no query DSL: the block is a plain expression
carrying the `undet` effect, and the type system tracks it like any other.

Yulang is alpha-stage research software — syntax, type display, effect
semantics, and library APIs may still change. It is, however, already at the
"install it and play for an evening" stage, and the rest of this page tries to
show why that evening is worth it.

## The fun part: effects are ordinary code

An effect call looks like a normal function call. What makes it an effect is
that *somebody up the stack decides what it means*:

```yulang
act flip:
    our coin: () -> bool

our all_paths(action: [flip] _) = catch action:
    flip::coin(), k -> all_paths(k true) + all_paths(k false)
    v -> [v]

all_paths:
    my a = if flip::coin(): 1 else: 0
    my b = if flip::coin(): 10 else: 0
    my c = if flip::coin(): 100 else: 0
    a + b + c
// => [111, 11, 101, 1, 110, 10, 100, 0]
```

The handler calls the continuation `k` twice — once with `true`, once with
`false` — so a single run of straight-line code explores all eight paths.
Writing this in most languages means CPS-transforming your program by hand;
here it is eight lines, and the `[flip]` in the type says exactly which code
can flip coins.

The standard library builds its own features from the same machinery:

- `sub:` + `return` — early return is a library effect, not a keyword welded
  into functions;
- `for` with `last` / `next` / `redo` — loops lower to the `Fold` role plus
  loop effects;
- `my $x` / `&x = v` — mutable references compile to a local `var` effect;
- `all` / `any` — an `if` condition can quantify over many values at once:

```yulang
if all [1, 2, 3] < any [3, 4, 5]:
    "every left dominated"
else:
    "no"
```

If you have met Raku's junctions: yes, that — except here `all` and `any` are
plain library functions producing nondeterministic values, and the surrounding
`if` receives a real `bool` once every left/right pair has been considered.

## The safety part: types tell the whole truth

Every expression has a value type *and* an effect row. If a function can
fail, mutate, or search, its type says so — and if the row is empty, it can't.

```yulang
pub error fs_err:
    not_found str
    denied str

our read_config(path: str): [fs_err] str =
    if path == "/etc/app.conf": "port = 8080"
    else: fail fs_err::not_found path
```

Errors are algebraic effects with concrete types, and you handle them by
naming them:

```yulang
catch read_config "/missing":
    fs_err::not_found p, _ -> "(missing) %{p}"
    fs_err::denied p, _ -> "(denied) %{p}"
    value -> value
// => "(missing) /missing"
```

What this buys you in practice:

- **No invisible exceptions.** There is deliberately no `anyhow`-style
  type-erased catch-all. Every error keeps its concrete type in the effect
  row, so the origin and the handler of each error are readable from types
  alone. Wider error families are built explicitly with `from` entries such as
  `fs from fs_err`; an `error E:` declaration generates `fail` support,
  `E::wrap`, explicit `E::up`, `from` casts, and `Display` output.
- **State cannot leak.** `my $x` opens a read/write port scoped to its
  binder. Because it is an effect, not a heap cell, a reference escaping its
  scope is a type error rather than a heisenbug.
- **Conversions stay declared and local.** Ordinary value conversions use
  explicit `cast(x: user_id): int = x.raw`. The generated exception is error
  upcasting: at a declared or annotated effect boundary, a concrete `fs_err`
  effect can satisfy concrete `io_err` only if `io_err` declared
  `fs from fs_err`. Row variables and row tails pass through unchanged, a
  missing `from` remains an effect mismatch, and this is not global effect-row
  unification.
- **Handlers are scoped by the program you wrote.** Effect propagation is
  statically scoped, and handler hygiene keeps library handlers from
  capturing operations they were never given. The
  [type-theory notes](web/docs/reference/type-theory.md) spell out the rules.

And you rarely write a type. Inference is Simple-sub-inspired, with subtyping,
structural records and tuples, effect rows, and role constraints:

```yulang
pub role Add 'a:
    pub a.add: 'a -> 'a

impl int: Add:
    our x.add y = std::int::add x y
```

Public types print role requirements as trailing `where` clauses:

```text
'a -> ('b -> [std::control::flow::loop; 'c] any) -> ['c] () where 'a: std::data::fold::Fold(item = 'b)
```

`+` is not welded to `int`; it resolves through the `Add` role. Other standard
library APIs use the same role machinery, such as `Fold` for `for` loops.

## The everyday part: it stays light

All of that machinery is invisible until you ask for it. Day-to-day Yulang
reads like a compact script language:

```yulang
say "Hello, World"
```

Methods attach right where the type is declared, and chain:

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2  // => 25
```

Record patterns with defaults give you named optional arguments for free:

```yulang
my area {width = 1, height = 2} = width * height

area { width: 3 }   // => 6
area {}             // => 2
```

Symbols give you tagged unions without declaring an enum, and each payload
keeps its own type:

```yulang
my describe x = case x:
    :hello name -> "Hello, " + name
    :bye n -> "Bye %{n}"
// describe : :{ hello str, bye int } -> str
```

The CLI is comfortable for one-liners and pipes:

```bash
yulang run -e "(each 1..20 + each 1..20).list.say"
echo "(each 1..3 + each 1..3).list.say" | yulang run
```

And performance is in "fine for daily scripting" territory rather than a
research-prototype trap: with a warm cache, the effect-heavy
`examples/showcase.yu` executes in roughly 25 ms on the default evidence VM,
and std-library `for` loops and nondeterministic search stay within an order
of magnitude of direct recursion even though both run through the full
effect machinery.

The everyday chores — read a config, patch a file, sum a log — write like a quick script and type-check like a real program. See [examples/config-file-text/](examples/config-file-text) for the cookbook.

## Try It

The fastest route is the browser playground at
**https://yulang.momota.pw/** — it runs the real compiler and evidence VM
compiled to WebAssembly.

To install the CLI on Linux or macOS (the binary embeds the standard library
and places it under `~/.yulang` on first use):

```bash
curl -fsSL https://yulang.momota.pw/install.sh | sh -s -- --version v0.1.0-alpha.8
```

The installer adds `~/.yulang/bin` to your shell profile when it is not
already on `PATH` (pass `--no-modify-path` to skip that); restart the
terminal, or call `~/.yulang/bin/yulang` directly in the current one.

On Windows:

```powershell
Invoke-WebRequest https://yulang.momota.pw/install.ps1 -OutFile install.ps1
powershell -ExecutionPolicy Bypass -File .\install.ps1 -Version v0.1.0-alpha.8
```

Then run a file, or type-check it:

```bash
yulang run examples/06_undet_once.yu
yulang check examples/08_types.yu
```

`run` executes through the evidence VM and prints only program output such as
`say` / `println`; add `--print-roots` to also see the values of top-level
expressions while experimenting. Compiled artifacts are cached under the user
cache root (`yulang cache path|stats|clear`, `--no-cache` to bypass once);
[docs/cache.md](docs/cache.md) describes the cache architecture. To use a
different standard-library checkout, set `YULANG_STD=/path/to/lib/std`.

To uninstall a release install:

```bash
curl -fsSL https://yulang.momota.pw/uninstall.sh | sh
```

```powershell
Invoke-WebRequest https://yulang.momota.pw/uninstall.ps1 -OutFile uninstall.ps1
powershell -ExecutionPolicy Bypass -File .\uninstall.ps1
```

From a repository checkout:

```bash
cargo build -p yulang
./target/debug/yulang run examples/06_undet_once.yu
```

## Learn More

- [web/docs/guide/tour.md](web/docs/guide/tour.md): a guided tour — every
  example runs in the playground as-is.
- [docs/language/overview.md](docs/language/overview.md): the main language
  overview ([Japanese](docs/language/overview.ja.md)).
- [web/docs/reference/type-theory.md](web/docs/reference/type-theory.md):
  effect rows, handler hygiene, and hidden handler evidence.
- [docs/status.md](docs/status.md): support status and the public contract
  spine across inference, runtime, diagnostics, and release artifacts.
- [examples/](examples): runnable examples; [lib/std/](lib/std): the standard
  library, itself written in Yulang.

Good first examples:

- `examples/showcase.yu`: broad syntax and library tour.
- `examples/config-file-text/config_read.yu`: config parsing with typed values.
- `examples/config-file-text/file_edit.yu`: durable text-file line editing.
- `examples/06_undet_once.yu`: nondeterminism through library effects.
- `examples/10_effect_handler.yu`: algebraic effect handlers.
- `examples/04_sub_return.yu`: local early return through `sub:`.
- `examples/11_attached_impl.yu`: attached role implementations.

Parser-combinator helpers and parser-sugar syntax such as `rule { ... }` and
`~"..."` are experimental: useful for trying the direction of the language,
but not a compatibility promise.

## Tooling

`yulang server` starts the language server (semantic tokens, full-document
sync, current lowering diagnostics). Zed support lives in
[yulang-zed/](yulang-zed); the extension launches `yulang server` from the
installed binary, so the release archive and the editor integration share one
executable. The source copy here is kept in sync with the separate
`momota1029/yulang-zed` extension repository.

## Under the Hood

Yulang currently has two user-facing execution routes: the evidence VM (the
default `run` route, and the fastest on effect-heavy programs) and the mono
runtime, a simple interpreter kept as an oracle via `run --interpreter` and the
lower-level `run-mono` commands. The browser playground uses the evidence VM
through the wasm crate. The evidence VM debug route can be checked against mono:

```bash
target/release/yulang --std-root lib debug evidence-vm-run --compare-mono examples/showcase.yu
```

The evidence VM uses permission-native handler visibility for certified
direct-tail handler paths and keeps the generic request machinery as the
fallback surface. An earlier Cranelift/MMTk native backend was explored in the
old implementation and retired; notes remain in
[docs/native-backend.md](docs/native-backend.md) and
[docs/native-experimental-release.md](docs/native-experimental-release.md).

## Development

Run the representative Rust test suites:

```bash
cargo test -p sources -p infer -p poly -p specialize -p yulang
```

Before pushing a release-like change, run the local release gate — it covers
formatting, the test suites, the release build, hardening smoke tests, and the
docs build (see the script for its environment switches):

```bash
scripts/release-gate.sh
```

The public contract manifest lives at `tests/yulang/cases.toml` and is
exercised through the public `yulang` CLI tests.

Repository layout:

- `crates/yulang`: CLI and language-server entry point.
- `crates/sources`: source collection, CST input, std install, realm freeze.
- `crates/infer`: CST → `poly` lowering and type inference.
- `crates/poly`: inferred polymorphic program representation.
- `crates/specialize`: principal monomorphization.
- `crates/mono` / `crates/mono-runtime`: monomorphic IR and oracle interpreter.
- `crates/control-ir`: lightweight control IR, lowering, and evidence summaries
  consumed by the evidence VM.
- `crates/evidence-vm`: the default evidence VM runtime.
- `crates/parser`: parser and syntax tree support.
- `lib/std`: standard library written in Yulang.
- `examples`, `web/`, `docs/`, `notes/`: examples, playground/docs sources,
  documentation, and working notes.
- `archive/crates`: the old implementation, reference-only.

## Status

Yulang is pre-release research software. Syntax, type output, runtime IR, the
VM, and the standard library may change without compatibility promises.
[docs/status.md](docs/status.md) describes the current support matrix.

## License

Licensed under either of:

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
- MIT License ([LICENSE-MIT](LICENSE-MIT))

at your option.
