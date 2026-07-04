# Contract v1 Server Evidence

This page records evidence for
[Server Resource Contract](server-resource-contract.md). It is a ledger of
current executable evidence, not a roadmap.

## Executable Source

The source of truth is:

```text
tests/yulang/cases.toml
```

Current `server-resource` manifest coverage:

| kind | count | contract role |
| --- | ---: | --- |
| `run` | 4 | mock-server request/response behavior |
| `public-signature` | 5 | exact server/net public type projection |
| total | 9 | mock-server first slice |

The conformance command is:

```bash
cargo run -q -p yulang -- --std-root lib contract --contract server-resource tests/yulang/cases.toml
```

Last recorded local validation on 2026-07-04:

```text
contract cases ok: 9
```

## Closed Slice

The mock-server first slice currently protects:

- the compiler-produced host manifest tier vocabulary for server operations:
  `net.listen` is `sync`, `server.accept` is `suspend-multi-shot`, and
  `server.respond` is `sync`;
- exact public signatures for `std::io::net::server.accept`,
  `std::io::net::server.respond`, `std::io::net::net.listen`,
  `std::io::net.listen`, and `std::io::net.serve`;
- multi-shot `accept` resumes as structured child branches under the serving
  handler extent, exercised by the in-process mock-server driver;
- one-shot response consumption through `server.respond`;
- double response typed failure as `net_err::closed`;
- the high-level unscoped spellings `my req = net::serve 8080` and
  `net::listen 8080` followed by `listener.accept()`.

## Evidence Cases

`tests/yulang/cases.toml` includes these `server-resource` runtime cases:

- `server_serve_echo_mock_server`;
- `server_unscoped_serve_echo_mock_server`;
- `server_unscoped_listen_accept_echo_mock_server`;
- `server_double_respond_typed_failure`.

It also includes these `server-resource` public signature cases:

- `std_io_net_server_accept_public_signature`;
- `std_io_net_server_respond_public_signature`;
- `std_io_net_net_listen_public_signature`;
- `std_io_net_listen_public_signature`;
- `std_io_net_serve_public_signature`.

The runtime cases all run with `host = "mock-server"`. Native socket behavior
and unsupported-host denial are not covered by this evidence. The important
negative rule still applies: future host slices must report real capability or
domain failures and must not fake success to make server examples pass.
