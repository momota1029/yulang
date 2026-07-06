# Yulang Contract v0 Evidence

This page records the completion evidence for **Yulang Contract v0**. It is not
a roadmap and not a wishlist. It answers: "what is already closed as the
current stable language core, and which remaining work belongs to the next
contract slice instead?"

## Verdict

As of 2026-07-06, the **Contract v0 executable spine is complete for the
`stable-core` subset**.

That does not mean every designed Yulang surface is stable. It means the current
stable core has a manifest owner, compact expectations, diagnostic/public-type
coverage, and release-facing gates. Work on file transactions, server resources,
host act FFI, package workflows, parser DSL runtime exposure, and Yumark expands
the next contract slice; it is not missing evidence for Contract v0.

## Executable Source

The source of truth is:

```text
tests/yulang/cases.toml
```

Current `stable-core` manifest coverage:

| kind | count | contract role |
| --- | ---: | --- |
| `run` | 32 | runtime behavior and public examples |
| `check` | 18 | structured source diagnostics |
| `public-signature` | 15 | exact public type projection |
| total | 65 | Contract v0 executable floor |

The conformance command is:

```bash
cargo run -q -p yulang -- --std-root lib contract --contract stable-core tests/yulang/cases.toml
```

Last recorded local validation on 2026-07-06:

```text
contract cases ok: 65
```

## Closed Slices

Contract v0 currently protects these closed slices:

- runtime fixtures and public examples for records, refs, loops, `sub`/`return`,
  nondeterminism, junctions, handlers, roles, casts, list update, result/error
  helpers, and path display;
- structured `check` diagnostics for parser, name, type, role/method, binding,
  record, and handler syntax failures;
- role/method failures as structured `SourceDiagnostic` cases
  (`unresolved_method_diagnostic`, `ambiguous_method_diagnostic`);
- exact public-signature canaries for effect hygiene, `ref.update`, parser
  `choice`, `for_in`, nondet `.once` / `.list`, stable result/path/error APIs,
  and callback/ref residual preservation;
- public-signature rejection of private evidence and placeholder-like fragments
  such as `#...`, `AllExcept(...)`, `Unknown`, and accidental `Any`;
- manifest schema checks: unique names, known tag spelling, exact public
  signature expectations, required diagnostic count/severity/code/range/related
  assertions, and `stable-core` not mixing with `preview`, `migration-canary`,
  or `compile-error`;
- release-facing smoke paths that exercise representative stable-core contract
  cases through the public binary surface.

## Standard API Boundary

Contract v0 includes stable standard API slices for:

- `std::data::result`;
- generated `error` helpers: `fail`, `wrap`, `from`, `up`, and generated
  `Display E`;
- `std::text::path` byte conversion and display behavior.

The current `std::io::file` helper/text-ref/metadata surface is intentionally
covered as `migration-canary`, not as `stable-api`. It proves the native host
bridge and public signatures exist. It does not yet close the file resource
transaction contract.

## Not Contract v0 Blockers

The following are real work, but they are not missing Contract v0 evidence:

- file managed-lens commit / rollback / multi-shot transaction execution;
- unsupported-host filesystem behavior;
- server resource APIs;
- host act FFI manifest / registry;
- direct native ABI FFI;
- remote package registry workflows;
- full parser DSL runtime exposure;
- Yumark value model;
- archived native backend behavior.

These belong to later contract slices, such as "file resource contract",
"host act FFI contract", or "server resource contract".

## Reviewer Rule

If a future review says "make Contract v0 real" without naming a missing
`stable-core` fixture, public signature, structured diagnostic, or release gate,
the correct response is to point at this page and the manifest run above.

New work should name the next contract slice it expands instead of reopening
Contract v0 generically.
