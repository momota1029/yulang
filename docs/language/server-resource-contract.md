# Server Resource Contract

This page defines the current server resource contract slice after
[Contract v1: File Resource](file-resource-contract.md).

The executable source of truth is
[`tests/yulang/cases.toml`](../../tests/yulang/cases.toml). Cases tagged
`server-resource` are the first server resource contract subset.
[`contract-v1-server-evidence.md`](contract-v1-server-evidence.md) records the
current evidence for that subset.

## Scope

The current contract is the **mock-server first slice**. It proves the resource
shape through the public CLI and in-process request driver. It does not yet
claim native socket adapter behavior or unsupported-host failure behavior.

Unsupported hosts must not fake success. That rule is part of the server
resource direction, but executable denial cases for native/unsupported hosts are
a later slice.

## Core Promise

The first server resource slice fixes this shape:

```text
host act + manifest tier + multi-shot accept + one-shot response capability
```

The current public API surface is under `std::io::net`:

- `net.listen` is the host operation that creates a listener;
- `listen` is the throwing public wrapper over `net.listen`;
- `server.accept` is a suspend multi-shot host operation;
- `server.respond` consumes a request response slot once;
- `serve` listens on a port and returns requests from `server.accept`.

The unscoped spelling is part of the contract:

```yu
my req = net::serve 8080
```

Prelude module aliasing must keep this path pointed at the high-level
`std::io::net` module rather than the companion host-act module.

## Manifest And Tier Policy

The compiler-produced host act manifest is part of the observable contract for
this slice. Server operations must carry the correct tier:

- `std.io.net.net.listen`: `sync`;
- `std.io.net.server.accept`: `suspend-multi-shot`;
- `std.io.net.server.respond`: `sync`.

`accept` resumes create structured child branches under the serving handler
extent. They are not detached tasks and not fake synchronous calls.

## Request / Response Policy

Each accepted request carries a payload and response slot. `respond` consumes
that slot. A second response to the same slot must return the typed domain
failure `net_err::closed`; it must not silently succeed, panic, or report an
untyped host failure.

The mock-server driver currently emits two request resumes and records compact
response output. That is the first executable adapter, not the final network
adapter.

## Manifest Tags

Server resource cases use these contract tags:

- `server-resource` for this contract slice;
- `standard-api`, `stable-api`, `network`, and `server` for the API surface;
- `host-act` when the case observes the host act boundary or exact public
  operation signature;
- `mock-host` and `host.mock-server` for the in-process driver;
- `typed-failure` when the case observes `net_err::closed`;
- `public-signature` for exact exported type projection.

Do not combine `server-resource` with `stable-core`. Contract v0 remains closed.

## Out Of Scope

These are not part of the current server resource contract slice:

- native socket adapter success or failure behavior;
- unsupported-host denial diagnostics;
- HTTP, WebSocket, or stdin/stdout adapters;
- wire codec negotiation;
- request metadata beyond the current payload / response-slot shape;
- cancellation and backpressure beyond the structured child branch shape already
  needed by mock-server accept resumes.
