# R261 — Y2/Y3 parser boundary for imported roots

The repository's bundled standard library is byte-authentic to the pinned
Y2 closure, but the current `yu_syntax::parse_file` is not a Y2 parser. A
primary-only temporary probe parsed all 40 bundled files and preserved their
bytes, yet interpreted English text on Y2 `--` comment lines in `text/config.yu`
as direct `OperatorChain` nodes. The Y3 line-comment lexer recognizes `//`.

The probe's counts (318 direct `BindingStatement`, 39 direct `OperatorChain`)
therefore cannot establish Y2 root forms. Some `OperatorChain` nodes are actual
operator-definition bodies, while the three text/config examples are comment
content. Byte round-trip is not syntax correspondence.

R260's source-line census remains conditional. No exact Y2 per-module parsed
root vector, ModuleMap publication vector, or imported initializer set has
been observed here. Next evidence must use an authentic Y2 parser/registration
interface or a source projection with a proved root/order/binding-body
correspondence over the entire pinned 40-file closure. R149's Types/Console
requirements and all parent proof/production gates remain open.

The temporary test was removed after the probe; this note records the result,
not a durable parser test. See
`tasks/agent-loop/sprints/yulang2-y3-parser-root-witness-boundary-20261021-r261.md`.
