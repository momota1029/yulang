# Recovery token width: frozen rev2 delta

Status: source evidence, conditional; independent review NOT_RUN.
Author `/root/npair_parser_row_key_separation`; no coauthors or descendants.
Sprint `npair-parser-row-key-separation-20261018`, contract rev2 SHA-256
`4de607f76986b6f97e11e1fcaebca8a32cc8e46c8d2d758458ba7333301e3798`.
Baseline `515b705f6879bd8fd4a57fd1f6732e11ea9c0a29`.
Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, original claim,
quantifiers/source domain unchanged, closure **0**, OPEN.

## Result and parent application

The newly pinned emitter preserves the owned Item payload bytes and consumes
the Item once. It does **not** establish positive width of an LBracket payload.
`Token` at item.rs:290–293 has crate-visible independent `kind` and `text`
fields. `Payload::Token` and `Item::plain` permit empty text without validation;
`Item::finish` validates fragment layout but imposes no nonempty-token condition.
An LBracket enum observation therefore cannot establish nonempty payload text
at this owner. This is an allowed synthetic carrier shape, **not** authentic
parser reachability or a source-qualified collision. Contract stop condition
reached: empty/synthetic payload is possible at the pinned carrier boundary.

The remaining exact premise is now upstream: every actual Item passed as
`open` to `type_bracket_row_normalized` must carry nonempty text at its lexical
producer. The earlier cache lemma consequently remains conditional; no parent
condition, semantic projection, `At`, native or production gate closes.

## Established local emission facts

1. `emit::emit_token_item` observes the payload and selects the syntax kind,
   mapping TokenKind::LBracket to SyntaxKind::LBracket. It then calls
   `item.emit_remaining` once. There is no branch that retries or duplicates
   this call inside that emitter.
2. Item owns its private payload (item.rs:622–627), does not implement Clone,
   and is consumed by `emit_remaining(self, ...)` (916 onward). The payload
   is not replaced while emitting leading trivia; the leading cursor records
   only how many leading parts have already been emitted. The subsequent
   `emit_payload_with_cursor` forwards exactly `payload_text(&self.payload)`.
3. With no fragments, `emit_physical_text` calls `output.token(kind, text)`
   once using the original payload string. With fragments, it partitions that
   string into nonoverlapping ordinary/foreign pieces; its loop has increasing
   cursor positions, and only emits ordinary pieces when they have positive
   length. A payload can therefore produce several physical tokens rather
   than literally one token; foreign spans use their own syntax kind.
   It still preserves the original nonempty payload's total bytes under the
   validated fragment layout. Nonempty fragment lengths are checked locally.
4. There is no local unconditional positive-width guarantee: unfragmented
   empty text is forwarded as empty text, while fragmented empty text yields
   no payload pieces. `emit_remaining` asserts only that payload_text is Some,
   which holds for a Token with empty text. TokenKind and spelling are separate.
5. `emit_recovery_missing` explicitly creates an empty Missing node. This
   confirms that zero-width recovery children exist, without showing a
   zero-width BracketRow: the row's earlier opening emission remains the
   decisive premise. The rev1 ordinary/recovery branches share that same
   opening call. These later missing nodes do not themselves remove already
   emitted opening bytes in the inspected functions.

Thus, conditional on a positive opening Item, its bytes survive these inspected
emitter paths and make the enclosing row positive width despite zero-width
recovery children. This is a local source correspondence result applied to
rev1's precise width premise; it is not a proof that actual lexical production
satisfies that premise. No tests of assumed transitions were used.

## Missing owner and next action

`ROW-OPEN-PAYLOAD-2`: Luna must identify/pin the real LBracket token producer
reached through `scan_type_nud_payload` / `scan_type_payload` and the Item
assembly at `current_item`, if continuing this proof. Their names/imports were
already exposed by the frozen parser evidence, but their implementations were
not read. Required fact: each actual row-opening Item has nonempty physical
payload text and is retained through lexical handoff. Exact further owner
symbols and files require Luna's next lease; this worker grants none.
Falsifier: an authentic parser path yielding an empty opening payload, or an
authentic earlier cache row/root row equal-key pair. A carrier assembled with
empty `Token.text` is insufficient to refute authentic-source separation.

No implementation TODO is justified: the carrier's generality is not a
demonstrated defect in the lexical producer. No narrowing to syntax-clean
inputs, no admission assumption, no new semantics. Retain rev1's additional
root-delegation/actual recovery-admission coverage boundaries if needed.
Fresh independent review and integration belong to Luna, not this author.

## Frozen evidence, checks and cessation

- rev1 artifact SHA-256 `51e756e4ae4cea61688553ee89bd1e7ec10a178d33e127c13946cf1a8189f222`, same author; its unconditional conclusions were not enlarged.
- emit.rs SHA-256 `de091c117486f7990dc6872bf2ee7659c0e3e7e148e255f47b56b7836fe7c59d`.
- item.rs SHA-256 `0a1dcbd84874f6abd571e0ce7035b9ba7682ebdf7c2348c030a1ba77deabcd25`.
- Contract rev2 bytes match the assignment hash. Its historical rev1-hash line
  says `e1725b...`, whereas this worker's original verified rev1 contract pin
  was `f9e0c7...`. No authority was inferred from that historical line; Luna
  should reconcile it without changing frozen evidence.

Checks: static reads/rg and sha256sum only. Broad initial output truncated;
key constructors/emission paths received targeted reads. No tests, probes,
builds, Cargo/compiler execution, Git, network, code or shared-record writes.
Requested Sol/high; observed model/effort UNKNOWN. Exactly 60s granted, no
extension; exact runtime/CPU/RAM UNKNOWN, charge full 60s. Astra0, children0.
Only this delta and its exact assigned inbox written; no scratch paths.
Writer STOPPED at frozen handoff; no descendants or unresolved child leases.
