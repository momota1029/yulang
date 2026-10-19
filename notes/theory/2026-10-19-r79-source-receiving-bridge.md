# R79 three-fixture source receiving bridge: exact read-boundary obstruction

Date: 2026-10-19. Revision: 1. Sole author: `/root/r79_proof`.
Assignment: `R79-SOURCE-HIR-1`. Claim class: **candidate source-native evidence; incomplete source derivation**.
Status: **OPEN / UNFINISHED**. No independent certification is claimed.
Contract: `tasks/agent-loop/sprints/effect-hygiene-role-call-20261019-r79.md`,
revision 1, SHA-256 `0ad36f8f9efb6e9fab326cd7df35e553c6baa9b1dd721e277a8ac184c774e479`.
Contract baseline: `af3ccf2d63ba7f87e0359e183568db548ea53307`; not independently observed through Git.

## 1. Parent application and stop condition

The original effect-hygiene/source-native parent retains its original scope:
source-owned annotation permission, actual received computation and request,
receiver and selection evidence, independent outward contributions and residual
and witness lineages must correspond without collapsing providers or witnesses.
Simple-sub generation, accumulation, propagation, levels, extrusion, qualifying
intrusion and generalization remain unchanged. Original evaluator/A-B, F1/FK1
and other independent universal obligations remain OPEN 0→0; R50 remains
NOT_ADOPTED. Three ground discard examples cannot replace those obligations.

This assignment attempts only the authentic raw-source→LocalSource premises
needed by the frozen R78 receiving trace. It reaches an **input-authority
obstruction before proving raw parser emission**. This is neither a parser bug
nor a source counterexample. `parse_file` is pinned, but the actual root parser
to which it delegates is not. The contract prohibits reading unpinned owners
and requires stopping at the first unsupported premise. That stop condition
has been reached; no wider search or source execution follows.

Consequently, none of the three raw-source→LocalSource projections is closed.
The parent gains the precise first dependency and the authentic downstream
constructor facts in §3; the R78 conditional runtime conclusion is not promoted.
No native K/D, residual typing, arbitrary continuation, storage or fiber claim
is attempted here.

## 2. Occurrence-indexed first obstruction

The exact fixture bytes and hashes are those in the frozen R78 certificate §2.
Offsets below are byte anchors from that certificate, not allocated HIR IDs.
Programs U/O/S have separate parses, owners, occurrences and dynamic events.

| Fixture | Literal identity | First root and later required source anchors | Unproved first join |
| --- | --- | --- | --- |
| U | 139 bytes; `d9f97c3a73925e86e1220011adbfd961679a786b0eec6cd39abc12163e761ed4` | `act signal:` at 0; formal `thunk:` at 46; consumed `thunk` at 74; `my main` at 107 | The raw prefix must produce a direct-root `ActDeclaration`, followed by the relay and main `BindingStatement` nodes, with the declared member and binding bodies under their actual owners. |
| O | 174 bytes; `31adb9c858d845582fda0005437821af6d67ede26b824b1e0d089d4baebbcb1b` | `act io:` at 0; formal `thunk:` at 69; consumed `thunk` at 93; `my main` at 146 | The root dispatcher must select Act then two bindings and preserve the relay Catch body. Its first other arm and second tick arm must remain ordered. |
| S | 184 bytes; `e0a1037879571d4360201fb66289b60102e3ef3aaf37719ee1ace9b14df939cb` | `act io:` at 0; formal `thunk:` at 69; consumed `thunk` at 93; `my main` at 156 | The root dispatcher must select Act then two bindings and preserve the first tick arm's `io::other p` body and later other arm. |

For **each** of these rows, `full_parse.rs:317–342` establishes the following
wrapper fact. `parse_file` checks shared source/header allocation, obtains the
effective operator table and calls
`crate::cursor::parse_root(source.as_ref(), &operators)` at line 331. It retains
the returned green tree and creates a fresh parse brand. It contains no root
statement dispatch implementation and no derivation that any of the above
literal prefixes invokes the pinned Act or Binding constructor.

`ParsedFile::source_root`, `SourceNode::children` and `SourceNode::key` in the
same pinned file retain parse branding, tree allocation identity and start
position when walking an already returned tree. Those wrappers do not prove
which tree `parse_root` returns for U/O/S.

**First exact missing owner/rule:** `yu_syntax::cursor::parse_root`, specifically
its raw-source root-item dispatch and progression over these three declarations.
The file implementing that symbol is not a contract pin and was not located
by a wider search. Luna must resolve and freeze that owner before extending
the audit. Pinned helper constructors do not establish that a caller actually
selects them. Test assertions and parser comments do not supply this join.

## 3. Authentic downstream facts already inspected

These are code implications with explicit inputs. They are useful owner
locators, not an occurrence derivation for the missing raw trees. No allocated
parameter, operation or expression ordinal is fabricated.

* `module.rs:1141–1189`, `lower_module_with_local_source`, creates the source
  identity context, enables the local-source flag, obtains the parsed green
  tree, projects effect declarations and enumerates actual direct-root children
  into plans. Thus root enumeration consumes the missing tree; it does not
  prove its emission. Source-key production also visibly delegates to
  `crate::source_identity::source_keys`; that dependency was not inspected and
  its constructor correctness is not silently assumed as an established fact.
* `plan_root` in `module.rs` admits a binding only from a
  `SyntaxKind::BindingStatement` with a supported plain header. The
  `plain_binding_header` branch at lines 2974–3003 accepts a single
  `PatternCallTail` containing one `Pattern`, whose identifier may be followed
  by one `PatternTypeAnnotation`. It retains the original identifier source
  key and annotation node. It does not establish that the bytes
  `(thunk:[signal] int)` or `(thunk:[io] int)` produce that node shape.
* `lower_plan`, `module.rs:2085–2189`, allocates each admitted formal's
  `HirParameterId` under the actual definition root, records its source key,
  calls `local_source::form`, and wraps the ordinary value in Lambdas using
  those formal IDs. `local_source.rs:553–643` independently retains that same
  formal ID, original parameter source/range and annotation; parses the
  annotation under the source-root owner; pushes a
  `LocalSourceResolution::Parameter` lexical binding; and constructs a
  `LocalSourceForm::Lambda` with its allocated body slot. This is a concrete
  original-formal-to-local-Lambda join conditional on authentic admission.
  The whole source projection, expression Name/operation resolution and Catch
  pattern correspondence are not certified by this partial join.
* Directly audited `receiving.rs:21–43`, `RootCompSchema::from_parameter`,
  accepts a formal only when annotation and formal share the Lambda's source
  root, the annotation has explicit outer effects, and its value is a ground
  Unit/Int/Bool/Str tag. A spelling such as `thunk` is insufficient. Since the
  authentic annotation projection for U/O/S is not established, this audit
  does not assert that their runtime schemas are actually constructed.
* Directly audited `Receiving::enter` retains the received value and inherited
  image while allocating a boundary with the actual receiver and schema.
  `Receiving::local_grant` requires an active matching invocation, that
  receiver's boundary, the annotation's resolved concrete family, authentic
  event/execution observation and a genuine matching candidate-owner receipt
  of the exact view/formal route. It returns positive evidence only on reaching
  that receiver through the image chain. Thus family spelling or annotation
  permission alone cannot discharge the missing source-to-event premise.

The direct receiving audit corroborates the kind of evidence R78 requires;
it does not independently certify its complete machine trace. R78 remains an
unreviewed conditional derivation, not accepted theorem evidence. In particular,
the empty-call payload projection, distinct resolved tick/other IDs, arm order,
wildcard continuation discard and outward event in S remain conditional on
their actual producer and consumer joins.

## 4. Prior work and original-parent limits

Reused: R78 §2 supplies the exact three immutable input identities and its
explicit first-missing-source question. Its conditional runtime account is the
target to which a future source derivation must be applied. Its historical
proof citations were not read or adopted as direct theorem inputs here.

Rejected: treating the fixture helper's written successful assertions as
constructor evidence; treating a pinned callee's implementation as proof of
uninspected dispatch; giving invented HIR IDs to source anchors; counting a
shared effect family as operation identity; treating wildcard discard as
continuation resumption; deriving static residual typing from runtime return.
No withdrawn inference bypass, source-law proposal or earlier storage/fiber
attempt is used.

The directly pinned top-level principles require ordinary mathematical
Simple-sub inference and constructor/consumer correspondence at its actual
owner. This finding proposes no constraint shortcut, execution prerequisite
for inference or semantic restriction. Parent application remains partial:
the original source premise is still open, now at a precise raw parser owner.
Even after this owner is audited, the unchanged native and universal parent
premises require their own evidence; they are outside this assignment.

## 5. Mutual TODO and discriminating evidence

`R79-SOURCE-HIR-1 / ROOT-DISPATCH` — Luna owns the authority boundary.
Required input: a frozen exact pin for the implementation of
`yu_syntax::cursor::parse_root` and the actual dispatch owners it uses for the
three fixture prefixes. Required output: an occurrence-indexed derivation that
these exact raw strings construct the specified direct-root Act and binding
nodes, preserving byte/source ownership and subsequent declaration boundaries;
or a concrete source-qualified counterexample. Falsifier: root dispatch selects
a different owner, recovery changes the claimed shape, progression consumes a
later declaration, or the proof assumes dispatch solely from a helper name.

Any subsequent expression/type/source-identity dependency must similarly be
frozen by Luna before it is read. This is a request for a changed read envelope,
not permission to start another attempt. No source edit or provisional runtime
instrument is presently necessary: the immediate missing evidence is static
producer code. No in-envelope successor remains after the mandated stop.

## 6. Frozen input receipt and resources

The contract hash and every Lane A direct pin below were recomputed from actual
file bytes before source use; all matched. No tests, probes, builds, runtime CLI,
Git operation or source/expectation edits occurred. Filesystem reads, byte
hashing and the two leased artifact writes are the only operations. No scratch
file, descendant or additional output exists.

| Direct dependency | SHA-256 |
| --- | --- |
| `crates/yu-syntax/src/full_parse.rs` | `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8` |
| `crates/yu-syntax/src/declaration/binding.rs` | `eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544` |
| `crates/yu-syntax/src/declaration/act_decl.rs` | `f1af95a12df81900564c83d0aad541064eb2fff21ca41259b7a943ae3ad4fd74` |
| `crates/yu-syntax/src/expression/case_like.rs` | `6e306bc420e4084832008b64cf39c790648fc1510ba3f1de2876590f79ebe961` |
| `crates/yu-syntax/src/pattern/mod.rs` | `1b608422c93ce0f6947125a9b1ea88314a48b3a5e45030ed23e5154492ad7883` |
| `crates/yu-hir/src/module.rs` | `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a` |
| `crates/yu-hir/src/module/local_source.rs` | `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5` |
| `crates/yu-hir/src/module/source_annotation.rs` | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| `tools/inference-playground/src/runtime/program.rs` | `484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11` |
| `tools/inference-playground/src/runtime/machine.rs` | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| `tools/inference-playground/src/runtime/receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| `tools/inference-playground/tests/runtime_receiving.rs` | `f82399766a012383f12e7190744c397ce10d11b9730241d6f724fa254c9d06bf` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/theory/2026-10-19-r78-receiving-selection-certificate.md` | `a6fcf5c95169f7b71932476a5fff915e1ac450b7859755c595bf6d73a30af31c` |

Requested model/effort: Sol/high. Effective observed model/effort: UNKNOWN;
no runtime settings metadata was returned. The first UTC clock observation was
2026-10-19 01:28:23; exact final clock and elapsed observed window are recorded
in the frozen handoff. Startup before that clock is UNKNOWN, so charge the full
issued 900-second allocation without refund. No claim of using all 900 seconds
is made. This bounded attempt ends at the unsupported root-dispatch premise.

Writer status at freeze: **STOPPED; writes cease after the one exact handoff**.
Only the theory note and assigned handoff are outputs. No descendants or leases
need reconciliation. Fresh review, grant changes, integration and parent status
remain Luna's duties.
