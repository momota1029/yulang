# CLI reference

The `yulang` CLI checks, builds, runs, tests, and inspects Yulang programs.
This page covers the supported command surface and its options.

## Invocation and help

The general form is `yulang [common options] <command> [command options]`.
Common options may appear before or after the command.

The current CLI has no `--help` or `--version` option and no per-command help.
Running `yulang` or `yulang --help` prints the usage summary to standard error
and exits with status 2.
Command failures normally exit with status 1.

## Common options

Common options apply only to the commands named in the last column.

| Option | Effect | Commands |
| --- | --- | --- |
| `--std-root <path>` | Use `<path>` as the standard-library root | `check`, `contract`, `test`, `build`, `run`, `dump`, `install std`, `server` |
| `--no-prelude` | Do not add the implicit prelude | `check`, `test`, `build`, `run`, `dump` |
| `--cst` | Print the concrete syntax tree before the command result | `check`, `build`, `run`, `dump` |
| `--no-cache` | Disable compiler cache reads and writes | `test`, `build`, `run`, `dump` |
| `--infer-phase-timings` | Print inference phases and statistics | `check` |
| `--runtime-phase-timings` | Print compilation, cache-route, and runtime phases and statistics | `run` |

`YULANG_LIB_DIR` changes the user library root used by `install std` and local
realm installation.
`YULANG_CACHE_DIR` changes the compiler cache root used by compilation and the
`cache` command.

## Check source

`check <path>` parses and type-checks an entry file.
A successful check is silent unless `--cst` or `--infer-phase-timings` is
present.
Diagnostics are printed when checking fails.

```sh
yulang check hello.yu
```

## Run programs

`run` uses the evidence VM by default.
It accepts one file path, source text through `-e` or `--eval`, explicit
standard input through `-`, or implicit standard input when the process is not
attached to an interactive terminal.
An interactive `yulang run` with no input prints usage instead of waiting.

```sh
yulang run hello.yu
yulang run --print-roots hello.yu
yulang run -e "1 + 2" --print-roots
echo "1 + 2" | yulang run --print-roots
```

Program output from `say`, `println`, and other host operations is always
printed.
Root expression values are printed only with `--print-roots`.

| Option | Effect |
| --- | --- |
| `-e <source>`, `--eval <source>` | Run source text supplied on the command line |
| `--evidence-vm` | Select the default evidence VM backend |
| `--interpreter` | Select the monomorphic interpreter oracle |
| `--host <native\|unsupported\|mock-server>` | Select native host capabilities, no host capabilities, or the in-process server host |
| `--print-roots` | Print root expression values after program output |
| `--print-nth` | Prefix each output result with `Out N:` and drive unhandled nondeterministic branches |
| `--runtime-evidence-profile-deep` | Collect deeper runtime-evidence profiling counters |

`--print-nth` shows each result produced by an unhandled nondeterministic
branch:

```sh
yulang run --print-nth -e '(each [1, 2]).say'
```

This prints `Out 1: 1` and `Out 2: 2`.
`--print-nth` requires the evidence VM.
The interpreter also requires the native host mode.

## Build artifacts

`build <path>` compiles an entry file to an encoded control-IR artifact.
Without `--out`, the output path is
`target/yulang/yuir/<entry-stem>.yuir`.

| Option | Effect |
| --- | --- |
| `--out <path>` | Write the artifact to `<path>` |

```sh
yulang build --out app.yuir hello.yu
```

## Run tests

`test <path>` discovers bindings in `mod test` modules and documentation
tests.
It reports the pass/fail total and exits with status 1 if any selected test
fails.

| Option | Effect |
| --- | --- |
| `--module <name>` | Run tests from a named test module; may be repeated |
| `--binding <name>` | Run tests with a named binding; may be repeated |
| `--show-passes` | Print one `PASS` line for each successful test |

Module and binding filters are combined: a module test must match both sets
when both kinds are present.

```sh
yulang test --show-passes tests.yu
```

## Run contract manifests

`contract <cases.toml>` runs the cases in an executable-contract manifest.
The command is intended for project and release validation.

| Option | Effect |
| --- | --- |
| `--repo-root <path>` | Resolve manifest case paths from `<path>` |
| `--case <name>` | Run a named case; may be repeated |
| `--contract <tag>` | Run cases carrying a contract tag; may be repeated |

Case and contract filters are combined.
The command exits with status 1 if no case matches or a selected case fails.

## Inspect compiler output

The supported inspection commands expose compiler IR and parser event trees.
Their output format is diagnostic and may change with the compiler.

### Dump IR

`dump <path> <selector>...` prints one or more compiler representations.
At least one selector is required, and multiple selectors print their results
in the order below.

| Selector | Output |
| --- | --- |
| `--core-ir`, `--poly` | Principal polymorphic IR |
| `--poly-raw` | Raw polymorphic IR |
| `--runtime-ir`, `--mono`, `--runtime-finalize-ir`, `--finalized-ir` | Specialized monomorphic IR |
| `--control-evidence`, `--evidence-ir` | Control evidence followed by the runtime-evidence surface |

```sh
yulang dump hello.yu --core-ir --runtime-ir
```

### Parse syntax

`parse [path] --as <mode>` prints the parser event tree for a file.
Without a path, it reads standard input.

| Mode | Input |
| --- | --- |
| `expr` | Expression |
| `pat` | Pattern |
| `stmt` | Statement sequence |
| `type` | Type expression |
| `mark` | Yumark document |

```sh
echo "1 + 2" | yulang parse --as expr
```

## Install the standard library

`install std` writes the embedded standard library to the versioned user
library directory.
`--std-root <path>` writes it to an explicit root instead.
The command prints the installed root to standard error.

```sh
yulang install std
```

## Manage the cache

`cache` inspects or removes the compiler cache selected by
`YULANG_CACHE_DIR`, `XDG_CACHE_HOME`, or the platform default.

```sh
yulang cache path
yulang cache stats
yulang cache clear
```

`path` prints the cache root.
`stats` counts artifacts by compiler stage and realm-resolution records.
`clear` removes the entire selected cache root; it succeeds when the root is
already absent.

## Manage realms

Realm commands operate on editable realms described by `realm.toml`.
The optional path defaults to the current directory.

### Freeze a realm

`realm freeze [path] --version <version>` creates an immutable snapshot under
`<path>/.yulang/versions/<version>`.
If `realm.toml` declares a version, the requested version must match it.

```sh
yulang realm freeze . --version 1.0.0
```

### Install a local realm

`realm install [path] [--version <version>]` freezes an editable realm and
installs the snapshot under the user library root.
The manifest must declare a local realm name.
The version may come from `--version` or `realm.toml`.

```sh
yulang realm install .
```

## Start the language server

`server` starts the language server over standard input and standard output.
Editor integrations normally start and supervise this process.

```sh
yulang server
```

## Unsupported and internal surface

Commands under `debug`, the hidden test worker, standalone IR compatibility
commands, and the low-level `*-std` spellings are compiler-development or
compatibility surfaces.
They are intentionally excluded from the supported CLI reference.
Use `run`, `dump`, `install std`, and their documented options instead.
