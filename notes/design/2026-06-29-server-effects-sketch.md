# Server effects sketch

## Goal

Yulang should be able to express a long-lived server without making the VM special-case a web
framework. The runtime should provide a handler that supplies incoming values, sends responses, and
keeps compiled code / std / realm cache warm.

The design should start with local runtime effects, then grow adapters for HTTP, WebSocket, CLI
stdin, or test drivers.

## Minimal effect families

A small channel-like effect is the lowest-risk core:

```yu
pub act channel 'a:
    pub recv: () -> 'a
    pub send: 'a -> ()
```

A request/response server can be layered on top:

```yu
pub act server 'req 'res:
    pub accept: () -> 'req
    pub respond: 'res -> ()
```

For event streams, the server loop can be ordinary Yulang code:

```yu
our loop(handle) =
    my req = server::accept()
    server::respond(handle req)
    loop handle
```

The important point is that `accept` / `recv` are effect operations. They can suspend the current
continuation until the host runtime has a value.

## Handler model

The host runtime provides a server handler:

```text
serve(action):
  run action under a server effect handler
  when action performs accept/recv:
    store the continuation in the scheduler
    return to the host event loop
  when an external value arrives:
    resume the stored continuation with that value
```

This is naturally resumptive. It should reuse the evidence VM's continuation machinery rather than
introducing an unrelated callback system.

For early implementation, keep it single-process and single-runtime:

```text
external event -> RuntimeEvidenceValue -> resume continuation
```

Network / process boundaries can come later.

## Serialization boundary

Values crossing the server boundary need a clear contract.

Safe initial rule:

```text
Only data values with an explicit wire codec may cross the host boundary.
```

Do not silently serialize closures, refs, thunks, or effectful continuations. If these are ever
allowed, they need separate capabilities.

Possible surface:

```yu
pub trait Wire 'a:
    pub encode: 'a -> text
    pub decode: text -> option 'a
```

or a built-in `wire` derivation later.

## Hygiene and capabilities

Server effects should follow the same contract discipline as handlers:

```text
The server handler grants the ability to handle `server::accept` / `channel::recv`
only at the explicit server boundary.
```

External events must not accidentally expose unrelated inner handlers. In evidence VM terms, the
server handler should be a provider grant / capability source, not a global ambient operation.

This matters for code like:

```yu
serve:
    my local = catch some_action:
        ...
    server::accept()
```

The local handler should not become visible to host events unless the function's effect contract
explicitly routes through it.

## Server mode as performance feature

A server runtime is also a compilation cache boundary.

The daemon can keep:

```text
- parsed std
- compiled unit cache
- realm/band resolution cache
- lowered evidence VM plans
- loaded source roots
```

Then `yulang run -e` / playground / LSP can send snippets or files to the daemon instead of paying
startup + std load + dependency resolution every time.

This is likely a larger user-visible speedup than shaving another 1ms from clean VM execution.

## First implementation slice

Do not start with HTTP.

Start with a local in-process event driver:

```text
1. Define host-side ServerRuntime queue.
2. Add a debug command that runs a Yulang action until it performs `server::accept`.
3. Feed a prebuilt RuntimeEvidenceValue into the suspended continuation.
4. Compare the result with a control run.
5. Only data values cross the boundary.
```

The first public adapter can be stdin/stdout or an in-memory test driver. HTTP/WebSocket should be a
thin adapter on top of the same `accept/respond` effect.

## Open questions

- Should `server::accept` be multi-shot? Probably no; each external event should resume a stored
  continuation at most once.
- Should handlers be allowed to store continuations for later? Yes for the server runtime, but this
  should be an explicit host capability.
- Should `respond` return acknowledgement / backpressure? Probably eventually:

```yu
pub respond: 'res -> result () server_error
```

- How should cancellation be represented? Likely a separate effect:

```yu
pub act cancel:
    pub cancelled: () -> bool
```

or a host-side abort signal that resumes with an error value.

## Relationship to native / evidence runtime

Server effects make the ResumePlan work more valuable. A long-lived server will repeatedly resume
similar continuations. If the evidence VM can turn resumptive paths into scoped resume plans, the
server runtime can cache those plans across events.

So the order should be:

```text
local server effect semantics
  + evidence VM scoped ResumePlan
  -> cached server event continuation
  -> host adapters
```
