# Authentic lexical LBracket: bounded identity bridge

Status: FROZEN research-only source evidence and conditional derivation; independent review NOT_RUN.
Author: /root/npair_lexer_bracket_identity.
Sprint: npair-operation-contract-and-lexer-identity-20261018, revision 1.
Baseline: b3a9b1739b59d8c7991b5f798e98f71f96904b19.
Parent: CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017; original theorem,
source domain, quantifiers and adopted semantics unchanged; parent closure0.

## Objective, authority and method

Trace a real lexical opening bracket through current-item construction and
emission, and determine whether this discharges the frozen conditional
root-row cache-address result. Static source audit only, limited to the four
contract-pinned lexical files and that frozen address artifact. This packet
introduces no language meaning, semantic incidence or implementation authority.
The sprint contract's “Actual LBracket identity” lane is the exact governing
scope. Its “Frozen authorities and inputs” and “Resources” sections fix the
baseline, dependencies, 180-second cap, Astra0 and children0. The address
artifact's “Derivation and exact premises” supplies the conditional consumer;
its key-distinctness premise remains unproved here.

## Claim class and explicit hypotheses

Established source facts in the inspected files: the punctuation scanner's
LBracket branch tests one `next()` result for '['; token/Item constructors move
the returned kind and text without rewriting them; canonical token emission
maps LBracket to SyntaxKind::LBracket; Error recovery emits payload bytes as
SyntaxKind::Error; Missing recovery creates an empty Missing node.

Conditional lexical lemma: assume (H1) LexIn::next advances through real source
characters, with_str returns exactly the consumed source slice, and lexical
transactions commit successful scans and roll back failed scans; (H2) the
accepted Type item actually uses scan_type_nud_payload/scan_type_payload through
current_item, with truthful source coordinates and without later replacement;
(H3) output-builder emission appends exactly the supplied bytes in order. Then
an LBracket returned by that scanner has spelling "[", byte length 1, and its
payload bytes survive current_item and either canonical or raw Error emission.
Canonical emission retains bracket kind; raw Error emission deliberately does
not retain bracket kind. This is byte/spelling identity, not pointer identity
or a retained unique source-token ID.

H1, complete H2 parser reachability, and H3 builder semantics are external
owner premises: none of their implementations is in the four-file read lease.
They are explicit hypotheses, not established by their method names. Generic
Token/Item construction supplies no authenticity theorem.

## Derivation from the pinned sources

1. lexer.rs:293–328 routes the Type NUD fallback and successor vocabulary to
   scan_type_payload, whose choices include scan_punctuation. Its token_payload
   helper (367–372) moves Token into CurrentPayload::Token. Other vocabulary
   choices may reject or accept another kind; that does not manufacture a
   LBracket through this branch. The only LBracket occurrence in this pinned
   lexer file is the punctuation arm (937).
2. scan_punctuation (933–955) invokes with_str around a closure whose first
   operation is punctuation.next()?. Only the '[' result selects LBracket;
   that arm performs no further read. It constructs Token { kind: kind?,
   text: text.into() }. Under H1, the accepted text is exactly the one ASCII
   source byte '['. EOF or another character does not select this arm. This
   conclusion depends on H1 rather than proving with_str/next from this file.
3. current_item.rs:159–176 computes the payload origin, invokes the supplied
   payload closure, moves CurrentPayload::Token(token) into Payload::Token(token),
   and passes that unchanged payload to Item::plain or Item::finish. EOF and
   fence boundaries have separate payload variants (149–156,179–198), so those
   branches do not synthesize brackets. current_item is generic over the
   closure; using it alone does not certify that the closure used the scanner.
4. item.rs:290–293 makes both Token fields crate-visible, with no nonempty-text
   invariant. PayloadView::token_kind/spelling (325–345) borrow these fields.
   Item::plain/finish (683–714) retain the payload. finish checks lengths and
   fragment placement, not that LBracket text is nonempty or equals "[".
   Thus Token { kind: LBracket, text: "".into() } is a smallest structural
   countermodel to an unconditional Token-kind-implies-positive-width claim.
   It is not an executed witness or evidence of parser reachability; no source
   mutation was performed. This boundary prevents treating synthetic carriers
   as counterexamples to the conditional authentic-scanner lemma.
5. Item::extent (733–771) derives payload width from stored text.len(). Under
   the lemma, payload range is successor_origin-1..successor_origin. It does
   not independently authenticate the supplied successor coordinate.
6. Canonical emit_token_item (emit.rs:240–252) selects token_syntax_kind and
   calls emit_remaining. token_syntax_kind maps LBracket to SyntaxKind::LBracket
   (305). emit_remaining/emit_payload_with_cursor (item.rs:916–930,1040–1049)
   emit remaining leading parts followed by the stored payload text. The
   ordinary fragment emitter emits that text directly; the segmented emitter
   partitions by existing foreign splits (item.rs:1206 onward). Under the
   authentic Type route, scan_type_payload ignores its foreign-split argument;
   current_item's splits arise from accepted leading trivia before payload.
   Validated splits cannot cross a constituent boundary. Thus the '[' payload
   has no foreign split introduced by this route. Arbitrary caller-supplied
   closures/Items are outside that statement.
7. ErrorRunOutput::emit_item_as (emit.rs:44–48) derives an extent and consumes
   the same Item through emit_remaining_error (item.rs:939–948), which uses
   the same payload text with SyntaxKind::Error. It does not return a new
   LBracket token. Retry-leading seal methods borrow the Item and advance only
   leading emission state; they do not replace the payload. emit_recovery_missing
   (146–151) and required-slot emission (154–175) emit empty Missing nodes,
   without a synthetic LBracket in these functions. This is a bounded audit of
   these emitters, not a survey of every recovery producer in the compiler.

## Application to the address lemma and exact remaining gate

The frozen address artifact needs earlier cache-seeding explicit rows to have
keys different from the root result row. Its traversal/cache proof is taken as
an input conditional derivation, not re-proved or independently reviewed here.
Positive bracket width by itself supplies no relation between row keys or
node starts. In particular, these four files never construct BracketRow nodes,
choose where their Rowan nodes start relative to leading trivia, assign
SourceNodeKeys, or prove that two accepted rows consume different opening
brackets without replay/reuse.

Therefore the conditional root-row cache-miss lemma cannot yet be applied
unconditionally. The exact remaining source gate is: for every earlier explicit
row that can seed this same Operation cache and the root result row, their
actual parser-owned BracketRow starts map to distinct keys. Required owner
evidence is the BracketRow/Type parser's current_item callback wiring and node
start/ownership placement, together with LexIn's with_str/next/transaction
implementation and the established node-start-to-key transport. The first two
owners are outside this lease; the last transport must be supplied by the
primary's reviewed prior evidence. This audit claims no global key injectivity.

A discriminating next packet should read those exact producer/coordinate owners
and compose their result with prior key transport. Another synthetic empty
Token or transition-model probe would leave the same authentic-source premise
untouched. Parent closure remains 0 even if that address sublemma later closes;
Operation semantic self-leaf incidence and other parent premises remain open.

## Frozen dependency manifest and checks

All SHA-256 values below were read from the working files and matched the
primary's contract pins. The baseline SHA is primary-supplied; no Git command
was run to independently resolve it. Other authority bundle hashes in the
contract were not revalidated or consumed as new semantic premises.

| Dependency | SHA-256 |
|---|---|
| Sprint contract rev1 | 67ff7aefe2b696db00433305f42774aca02c53253d877ac1ffc6035c81dbc631 |
| lexical/current_item.rs | 41efcce2b737a0362484e854a8549bda5f7bf0d2b911499553f1e449c6782a84 |
| lexical/lexer.rs | 97c69c86888784ee4b3eb04d8e4685f6370dbf451631c83ec1838fe7abfc36e1 |
| lexical/item.rs | 0a1dcbd84874f6abd571e0ce7035b9ba7682ebdf7c2348c030a1ba77deabcd25 |
| cursor/recovery/emit.rs | de091c117486f7990dc6872bf2ee7659c0e3e7e148e255f47b56b7836fe7c59d |
| Frozen explicit-row-address artifact | 2796562ac2e359933ff5ac8ec58352a5b61b83264b5b88baa7ef8ce0065382ac |

Commands: cat, targeted rg -n, sed -n, sha256sum, and two leased Markdown writes.
Some broad initial read output truncated; decisive source branches were reread
in targeted output. No test, build, probe, Cargo, network, Git, compiler edit,
child launch or reviewer appointment. No executable oracle; this source audit
shares H1–H3 with the intended runtime route and cannot independently validate
them. Seeds/ranges: not applicable; no exhaustive input search or mutation run.
Failure conditions include false source-slice/transaction semantics, synthetic
payload replacement, untruthful coordinates, noncanonical grammar wiring,
foreign payload splitting outside the authentic route, or node-start/key
collisions. Runtime recovery integration, other parser producers, builder
internals and semantic incidence remain unverified.

## Resource and STOP receipt

Requested Sol/researcher/high, cap180s; effective model/effort UNKNOWN from
runtime metadata. Astra0; children0; no heavyweight processes. Reads used short
shell commands, sometimes two independent read calls concurrently. Exact CPU,
peak RSS and wall duration were not instrumented; charge the full 180s reserved
cap. This submission ends writes to both leased paths before independent
review. No shared-record or Git mutation was performed.

Commit packet: exact leased paths are this note and
`tasks/agent-loop/inbox/20261018-npair-lexer-bracket-identity.md`; baseline
`b3a9b1739b59d8c7991b5f798e98f71f96904b19`; changed dependency hashes: none.
Review NOT_RUN; checks above. Proposed checkpoint message:
`research: bound authentic lexer bracket identity and remaining row-start gate`.
Primary/curator deltas intentionally deferred: mark this worker STOPPED, retain
parent closure0, record the conditional lexical lemma and the exact remaining
parser/cursor producer gate, and assign fresh review without adopting semantics.
