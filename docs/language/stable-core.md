# Yulang Stable Core

This page defines **Yulang Contract v0**: the current stable language core that
is executable, documented, diagnosable, and suitable for release gating.

Yulang is still alpha software. Syntax, type display, effect semantics, runtime
IR, and standard-library APIs can still move. Contract v0 is narrower than "all
implemented features": it names the surface that should not change by accident.

The executable source of truth is [`tests/yulang/cases.toml`](../../tests/yulang/cases.toml).
Cases tagged `stable-core` are the conformance floor for this page.
[`contract-v0-evidence.md`](contract-v0-evidence.md) records the current
completion evidence for that floor.

## Contract v0 Rule

A feature belongs to the stable core only when it has all of these:

- a small `.yu` fixture or public example;
- a manifest case in `tests/yulang/cases.toml`;
- a compact expectation for runtime output, public signature, or diagnostic
  payload;
- a contract tag that identifies the protected language area.

Do not add placeholders to the manifest. Future APIs and unimplemented
capability policies belong in specs or TODO notes until they are observable
through the public CLI.

## Included Surface

Contract v0 covers these current language promises:

- expression-oriented blocks, local bindings, functions, records, tuples, lists,
  structs, enums, and pattern matching;
- roles, companion methods, attached impls, user-defined operators, and method
  selection;
- `sub:` / `return`, `for`, `last`, `next`, `redo`, local references, and list
  update behavior;
- algebraic effects, handlers, nondeterminism, junction-style effectful boolean
  conditions, and deep-handler public signatures;
- public type projection that does not leak private stack evidence such as
  `#...`, `AllExcept(...)`, private tails, `Unknown`, or placeholder-like `Any`;
- structured diagnostics for parser, name, type, role/method, and handler syntax
  failures, with stable code, severity, primary range, and related-count
  contracts;
- stable standard API slices for `std::data::result`, generated `error` helpers,
  and `std::text::path` byte/display behavior.

## Completed Slices

These Contract v0 slices are already executable through the manifest:

- runtime fixtures and public examples for nondeterminism, records, refs, roles,
  effects, casts, list update, result/error helpers, and path display;
- `kind = "check"` diagnostics for parser, name, type, role/method, binding,
  record, and handler syntax failures;
- `unresolved_method_diagnostic` and `ambiguous_method_diagnostic` as structured
  role/method `SourceDiagnostic` cases;
- public-signature exact-type canaries for effect hygiene, `ref.update`,
  parser `choice`, `for_in`, nondet `.once` / `.list`, stable result/path/error
  APIs, and file API migration canaries;
- `yulang contract --contract stable-core` tag filtering, including unknown tag
  rejection;
- hardening and release archive smoke paths that run representative
  `stable-core` contract cases through the release binary surface.

The current manifest has 56 `stable-core` cases: 25 `run`, 16 `check`, and
15 `public-signature`. Treat requests to "finish Contract v0" as requests to
name a missing fixture or gate in that manifest. Work on file transactions,
server resources, host act FFI, and other preview surfaces belongs to the next
contract slice, not to reopening Contract v0 generically.

## Not Contract v0

These surfaces are implemented, designed, or previewed, but are not part of the
stable core yet:

- archived native backend behavior;
- direct native ABI FFI;
- remote package registry workflows;
- full parser DSL runtime exposure;
- Yumark value model;
- server resource APIs;
- filesystem metadata beyond the current `file_meta { kind, readonly }`
  migration canary, directory listing, locking, scope-exit write-back, and
  unsupported-host behavior;
- file helper spellings tagged `migration-canary`.

## Conformance

Use the manifest runner for the executable conformance suite:

```bash
cargo run -q -p yulang -- --std-root lib contract --contract stable-core tests/yulang/cases.toml
```

Focused Rust gates also read the same manifest:

```bash
timeout 240s cargo test -q -p yulang --test cli public_contract_manifest -- --test-threads=1
timeout 240s cargo test -q -p yulang public -- --test-threads=1
```

Release gates should run the manifest through the packaged binary and bundled
standard library. A release is not a Contract v0 release unless the
manifest, public signatures, diagnostics, and release smoke agree.
