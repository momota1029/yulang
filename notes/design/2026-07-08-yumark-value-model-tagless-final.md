# Yumark value model: tagless-final-flavored design (2026-07-08, Claude 署名・authoritative)

Status: design decisions from an extended design session, empirically verified via
PoCs in `examples/`. This is the authoritative record of *why* the shape below was
chosen and what alternatives were rejected and why. Implementation of the real
Yumark parser/lowering/stdlib surface has not started; this covers the value model
only. **Revised same day**: the original "Tree representation" (a single flat
`enum yumark_node` with homogeneous `list yumark_node` children) was superseded
by a typed cons-chain, once the user pointed out it dropped the actual point of
reaching for tagless-final in the first place — see "Tree representation,
revised" below. The flat-enum section is kept for its still-valid sub-findings
(role mechanics, Candidate A/B) but its structural choice is no longer adopted.

## Summary

Yumark documents are represented as a **typed cons-chain** — a hand-rolled
generic `cons_cell 'head 'tail` / `nil_cell` pair, so each concrete document's
own shape is reflected in its own nested type (not erased into one flat sum
type). Rendering to a target format (HTML, Markdown, ...) uses a role-based
interpreter layer, tagless-final-*flavored* (extensible per-backend dispatch,
inductive instance derivation) but not pure tagless-final (no dictionary-passing
term, no rank-2 storage — construction stays inert). Injection (the
`\func(){}[]` / `[text]:func {}` macro mechanism) produces genuinely
backend-native typed content by bundling one monomorphic thunk per supported
format inside a leaf, not by storing a polymorphic function as data. See "Tree
representation, revised" for the current design; the rest of this document's
role-shape, injection, effect, and state findings still apply unchanged.

## Tree representation, revised: typed cons-chain (2026-07-08, supersedes flat enum)

The document's own type reflects its structure, using hand-rolled generic
types (empirically verified in `examples/yumark_typed_structure_poc.yu`,
commit `8bd02dec`):

```yu
struct nil_cell { marker: str }
struct cons_cell 'head 'tail { head: 'head, tail: 'tail }
```

A document is built by nesting `cons`, e.g. `cons(text_leaf {...}, cons(strong_leaf
{...}, cons(injected_leaf {...}, nil())))` — every distinct document shape is its
own concrete type (`cons_cell text_leaf (cons_cell strong_leaf (cons_cell
injected_leaf nil_cell))` for the example above), not a value of one shared
`yumark_node` type.

Role instances are derived **inductively**, reusing the `YumarkRender 'node
'format` role shape from "Render role shape" below (`type repr` per format,
methods return `['e] repr`):

```yu
impl nil_cell: YumarkRender html_format:
    type repr = html_node
    our cell.render_yumark _ = html_node { tag: "empty", body: "" }

impl (cons_cell 'head 'tail): YumarkRender html_format:
    where 'head: YumarkRender html_format
    where 'tail: YumarkRender html_format
    type repr = html_node
    our cell.render_yumark _ =
        my head = render_html_doc cell.head
        my tail = render_html_doc cell.tail
        html_fragment head tail
```

Each leaf type (`text_leaf`, `strong_leaf`, `code_leaf`, `injected_leaf`, ...)
gets its own base-case instance. A composite `cons_cell` implements
`YumarkRender <format>` **only if both its head and tail already do** — this is
the same "prerequisite recursion, same role" mechanism found earlier in the
role-system investigation (`impl (mylist 'a): Display` requiring a same-role
`Display 'a` prerequisite; stdlib `Display`/`Debug` recursive-looking impls for
`list`/`opt`/`result`). It generalizes cleanly to a hand-rolled two-parameter
generic type, even though genuinely generic arbitrary-arity tuple decomposition
does **not** exist (see "Related findings" below, still accurate for real
tuples) — the hand-rolled cons-chain sidesteps that limitation entirely by
being an ordinary two-parameter generic type with a real recursive instance,
not a fixed-arity tuple.

Empirically confirmed, all three properties the design needs simultaneously:

1. **Positive case**: a 4-leaf nested chain renders correctly through
   `render_html_doc` with **no bespoke instance written for that specific
   shape** — the composite instance is derived for free from the leaf
   instances plus the two inductive rules above.
2. **Negative case**: a chain containing one leaf that does *not* implement
   `YumarkRender html_format` (only `markdown_format`) correctly **fails to
   compile** when rendered as HTML:
   `unresolved typeclass method ... for receiver markdown_only_leaf ->
   render_yumark(html_format, html_node) -> html_node`. Malformed/
   format-incompatible documents are caught by the type system, not silently
   broken or discovered at runtime.
3. **Compatibility with Candidate B injection**: a leaf can itself be an
   `injected_leaf { payload: injection_payload }` (the same per-format
   monomorphic-closure struct from "Injection mechanism" below) — nesting it
   inside a cons-chain position doesn't force evaluation any earlier;
   `clock::now` still only fires at render time, confirmed by a
   construction-only run producing no clock output. The typed-structure
   design and the deferred-effect design are not in tension — Candidate B
   lives at the leaf level of the cons-chain.

Two implementation caveats found along the way (workarounds, not blockers):

- `where` clauses don't appear to support spelling an associated-type equality
  directly, so pinning `repr` (e.g. to `html_node`) goes through a small typed
  "command" helper function whose own return-type annotation fixes it:
  `my html_render_command(): render_yumark html_format html_node = ...`.
- Using `+` for string concatenation inside a generic (inductive) impl body
  introduced extra role-solving ambiguity; calling `std::text::str::concat`
  directly avoided it.

This changes what "Parser/lowering integration" (see Open items) needs to
target: lowering must produce cons-chain values whose *type* reflects the
parsed document's actual shape, not values of one shared `yumark_node` type.

### Static vocabulary ported to the typed cons-chain (2026-07-08)

The node-kind vocabulary from the (now-historical) flat-enum static-vocab PoC
— heading, blank line, list/list item, code fence, block quote, emphasis,
strong, section close, paragraph, doc — is re-expressed and confirmed working
in `examples/yumark_typed_static_vocab_poc.yu` (commit `af4cebc6`). Every
container node kind follows the same generic-over-children pattern as
`cons_cell` itself, e.g.:

```yu
struct heading_leaf 'children { marker: str, level: int, children: 'children }

impl (heading_leaf 'children): YumarkRender html_format:
    where 'children: YumarkRender html_format
    type repr = html_node
    our node.render_yumark _ = ...
```

`code_fence_info`/`code_fence_text` (previously two separate enum variants)
collapsed into one `code_fence_leaf { info: str, body: str }` — under typed
nodes there was no longer a reason to keep them as separate walkable pieces.
A representative document (heading, paragraph with emphasis/strong, blank
line, unordered list, code fence, block quote containing an injection,
section close) renders correctly and richly in both HTML and Markdown, with
no bespoke per-document-shape instance anywhere — confirming the inductive
pattern generalizes across the whole vocabulary, not just the minimal
`cons_cell`/`nil_cell` base case.

**Performance risk found, precisely characterized (2026-07-08 follow-up)**:
initially reported as "named functions time out," but isolated to something
much narrower. Measured (`--runtime-phase-timings`, `YULANG_ANALYSIS_TIMING=1`):

| shape | time |
|---|---|
| top-level tuple root (no named function), both formats | 6.6s |
| zero-arg named function (`my proof() = ...` calling `build_demo_doc()` internally), both formats | 63.5s |
| zero-arg named function, HTML only | 6.5s |
| zero-arg named function, Markdown only | 60.5s |
| named function taking the doc as an **explicit parameter** (`my proof(doc: 'doc) = ...`), both formats | 6.6s |
| named function taking the doc as an explicit parameter, Markdown only | 6.4s |

The trigger is not "named function" and not "rendering both formats" — it's
specifically **rendering to Markdown inside a zero-argument named binding that
builds the document itself**. `YULANG_ANALYSIS_TIMING=1` shows the extra cost
lands almost entirely in generalization of that binding (a `quantify
generalize` phase for it costing ~58s, dominated by `generalize resolve
roles` sub-phases) — i.e. Hindley-Milner generalization of a zero-arg let
binding whose body needs the Markdown inductive role chain resolved is
expensive; HTML's chain apparently isn't (not yet explained why the two
formats differ this much). Passing the already-built document as an explicit
parameter instead of calling `build_demo_doc()` inside a zero-arg function
body sidesteps the expensive generalization path entirely and is fast either
way. **Practical takeaway**: write rendering functions as `render(doc: 'doc)`
(parameter), not `render() = ...; build the doc inside ...` (zero-arg) —
ordinary, idiomatic style anyway, so this is not expected to constrain real
usage. Still open: why Markdown's role chain triggers expensive generalization
and HTML's doesn't; not investigated further.

## Render role shape

The core role shape below (tag parameter + associated `repr` + effect-row-
polymorphic methods) is unchanged and still the mechanism used in the revised
cons-chain design above. What *does* change under the cons-chain: instead of
one role implemented once per backend with fixed `render_text`/
`render_paragraph`/... methods dispatched via pattern-matching inside a `walk`
function, each **node/leaf type** gets its own `impl <leaf_type>: YumarkRender
<format>` with a single generic method (e.g. `render_yumark`), and composite
`cons_cell`/`nil_cell` instances are derived inductively (see above) instead of
a hand-written `walk` doing the pattern-match/recursion itself.

```yu
role YumarkRender 'backend 'format:
    type repr
    our backend.render_text: render_text 'format -> ['e] repr
    our backend.render_paragraph: render_paragraph 'format repr -> ['e] repr
```

- `'format` is a phantom/marker type (`HTML`, `Markdown`, ...) used purely to
  tag which flavor a given backend implements — confirmed to work as an ordinary
  multi-parameter role, same shape as the pre-existing `Index 'container 'key`.
- `repr` is an **associated type** of the role (`type repr`), not hardcoded to
  `str`. Each backend struct picks its own concrete repr — e.g. the HTML backend
  can use a real structured type (`html_node { tag: str, body: str }`), the
  Markdown backend can just use `str`. This was the first PoC's mistake: it
  hardcoded `repr = str` for both backends and never actually exercised
  type-level divergence, which is the entire point of reaching for tagless-final
  in the first place.
- Render methods return `['e] repr` — ordinary effect-row polymorphism, not a
  bespoke wrapper effect. See "No custom Yumark effect" below.

## Injection mechanism: Candidate A rejected, Candidate B adopted

Still current under the revised cons-chain tree: Candidate B is what an
`injected_leaf` node holds, one leaf among many in the chain (confirmed
directly in `examples/yumark_typed_structure_poc.yu`, see "Tree
representation, revised" above).

Two candidates were tested empirically (`examples/yumark_value_model_poc2.yu`,
`examples/yumark_effectful_injection_capstone.yu`):

- **Candidate A** (rejected): the injection node holds a single role-bounded
  generic function value — something like `('a) -> ['e] 'a.repr where 'a:
  YumarkRender(HTML)` — called later once `walk` has a concrete backend in
  hand. This type-checks and runs fine as a **direct, top-level call**, but
  **fails once stored inside data** (an enum/struct field): the role resolver
  falls back to `unit` placeholders or reports conflicting candidates. Storing
  a role-bounded-polymorphic function as a value is not currently supported —
  this is effectively the same wall as "no first-class existential/rank-2
  storage" noted elsewhere in project memory (`\my &x ->` binder notes).
- **Candidate B** (adopted): the injection node holds one **monomorphic**
  closure per supported format, bundled in an ordinary struct:
  ```yu
  struct injection_payload:
      html: () -> [std::time::clock] html_node
      markdown: () -> [std::time::clock] str
  ```
  Each field is ordinary data — no generic storage needed. `walk` picks the
  right field for whichever backend it's currently rendering with. Trade-off:
  adding a new backend format requires updating every injection site's payload
  shape (no add-a-backend-without-touching-existing-injections extensibility).
  Given the PoC evidence, this trade-off is accepted for now; revisit only if/
  when Yulang gets first-class existential types (see project memory on the
  `\my &x ->` binder and deferred existential-types work).

Both candidates preserve inertness: constructing the payload only stores
function *references* (`html: html_injection`), never calls them. Forcing
happens only when `walk` actually invokes `payload.html()` / `payload.markdown()`.

## No custom `Yumark` wrapper effect

An earlier iteration wrapped injection side-observations in a bespoke `Yumark`
effect (`note: str -> ()`), reasoning that it would let backends respond
differently to "the same operation." This conflated three distinct concerns:

1. Proving effect-timing control (construction inert, walk forces) — any real
   effect demonstrates this; no need for a custom one.
2. Backend-specific behavior for the same abstract operation — this is just
   ordinary role method dispatch (`backend.render_text`, `backend.render_paragraph`),
   requires no effect system involvement at all.
3. A *capability boundary* — "what operations are legal inside injected
   content, checked uniformly before backend selection" — this was the
   original motivating idea (from the `[\each(...)]:list` postfix-method
   discussion) and might still be worth pursuing, but is a genuinely separate,
   harder, and still-unaddressed design question. Not resolved by this
   session's PoCs.

Current position: injection functions should use whatever real effects they
actually need (`std::time::clock`, `nondet`, etc.), with render role methods
being effect-row-polymorphic. The capability-boundary idea (point 3) is parked,
not adopted or rejected.

## State/variables: explicitly out of scope

Considered and rejected for the *document* value model. Reasoning (user's own,
2026-07-08): a Yumark document should stay declarative; mutating state inside
the document representation was never really this layer's problem. If Yumark
is used to build something with real interactivity (e.g. web pages), that need
is expected to be met by *component + effect composition* techniques layered
on top of `inject`, not by the document tree carrying mutable state — a
separate, heavier future topic, not needed for the current value model.

### Why the naive approach would have failed anyway (empirically confirmed)

Bringing a `my &x = ...` state variable "out" together with its handler (e.g.
returning a handler closure that references it) type-checks but fails at
**runtime** with an unhandled private-state-effect error
(`examples/state_handler_escape_repro.yu`). Root cause: `my &x = ...` desugars
into a compiler-generated private effect plus an auto-generated `run` handler
wrapping *the rest of the enclosing block* — the handler exists only for that
block's dynamic extent. A returned closure invoked later runs outside that
extent, so there's no live handler for the private state effect to route to.

This is **not** a hygiene check that could be "loosened" — there is no
alternate handler to fall back to; the danger is dynamic handler/continuation
validity, not mutable-cell aliasing (Yulang's state has no real mutable cell in
the first place — pure continuation threading, no write barrier). If
cross-boundary document state is ever needed later, the proven fix (already
used for the file-buffer-boundary problem, `2026-07-02-file-session-boundary-plan.md`)
is explicit state-passing: thread the state value through ordinary parameters
and return values instead of relying on the `my &x` idiom's implicit handler.

## Related findings from this session

- **No `Error` role exists.** The relevant mechanism is `Throw 'e` (`pub
  e.throw: [throws] never` — genuinely performs an effect, return type
  `never`) plus the `error E:` declaration sugar that generates a `Throw E`
  impl. This is distinct from `ParseError 'err`, which is a *pure*
  construction/formatting role (no effect) — `expected: str -> pos -> 'err`
  etc. Both were candidate models for "Error trait that can return an effect";
  they turned out to be two separate existing mechanisms, not one.
- **Tuples are fixed-arity products, not nested-pair sugar.** `(A, B, C)` is
  not equivalent to `(A, (B, C))` anywhere in the type IR. Role/subtype
  matching requires exact arity. There is no generic "N = head + tail"
  instance mechanism *for real tuples* today (confirmed by the stdlib's
  manual per-arity Display/Debug impls for tuples 2..5) — a decomposable
  type-level list built on the actual tuple type would need new infer/poly
  work. **Correction (later same day): this finding is still true for real
  tuples, but Yumark does need a type-level list, and gets one via a
  hand-rolled two-parameter generic `cons_cell`/`nil_cell` pair instead of
  real tuples** — see "Tree representation, revised." The `list repr`
  suffices claim below was wrong; it silently erased the document's structure
  into one flat sum type, which is not what was wanted.

## Bug found and fixed as a byproduct

Testing Candidate B with a real effect (`std::time::clock::now`) inside a
struct field surfaced a genuine runtime bug, not a design gap: in
`crates/evidence-vm/src/runtime.rs`, `adapt_value_result` adapted function-type
record fields via `FunctionAdapter` but returned record-to-record boundaries
*unchanged*, without recursively adapting fields — even though
`value_boundary_supported` claimed the nested boundary (including thunk/
function differences) was supported. An effectful function stored in a struct
field would silently lose its thunk-wrapping, then crash downstream
(`expected a delayed computation, got "..."`) when called. Fixed in
`41873245` (`fix(evidence-vm): adapt record boundary fields`) by making record
adaptation recurse per-field through the same `adapt_value_result` dispatch,
with explicit CPS suspend/resume support (new `AdaptRecordFields` continuation
frame) and a deliberate defer-don't-force rule for fields whose source type is
already a thunk. Verified against the full contract corpus (225/225 green) and
the direct-vs-field-storage contrast repros
(`examples/clock_effect_direct_repro.yu`, `examples/clock_effect_field_repro.yu`).

## Surface syntax: block-position grouped commands (implemented 2026-07-08)

The `\func(){}[]` prefix syntax is now real, for block position only. Finalized
grammar:

```text
block_command := "\" ident command_group* command_terminator?
command_group := "(" yulang_expr ")" | "{" yumark_block "}" | "[" yumark_inline "]"
command_terminator := ";"
```

Key corrections from the first-pass plan — worth recording, since the initial
plan was wrong twice before landing here:

1. **Groups are repeatable, any order, any count** — not "each appears at most
   once in a fixed `()`→`{}`→`[]` order" as first proposed. `\cmd()()()[][][][][]{}{}{}`
   must parse, and `\link[](url_expr)` (inline body before expr group) must
   parse. The parser does not validate arity/order/shape against what a
   specific command expects — that's deferred to a later semantic/lowering
   stage, the same way ordinary function-call arity isn't checked by the
   parser. Modeled as a Pratt-tail-style loop (`(`/`{`/`[` lookahead, dispatch,
   repeat) — the same architectural shape as the pre-existing curried-call
   support (`f(a)(b)`, real precedent in `lib/std/text/parse.yu`), not the
   delimited-list machinery.
2. **Named parameters need no dedicated syntax** — `()` already holds an
   arbitrary Yulang expression, so a record literal works directly:
   `\thm({ title: '[...] }) { block }`. Quoted Yumark (`'[...]`) nests inside
   the record field value and parses correctly (see evidence trail).
3. **`;` explicitly terminates a zero-group command** (reusing the previously
   dead `SyntaxKind::YmSemi`). Motivation: Japanese has no whitespace between
   words, so `\mycommand` immediately followed by more prose with no space
   cannot rely on whitespace to mark where the command ends. Without `;`, a
   zero-group command falls through to the existing legacy behavior
   (rest-of-line becomes the command's own inline content) — correct for
   `\cmd trailing text`, wrong if the author meant "no arguments, unrelated
   prose continues immediately." `\cmd;tail` parses `tail` as a separate,
   following paragraph, not as content of `\cmd`. A trailing `;` after
   one-or-more groups is accepted but optional (redundant, harmless) — once
   groups are present the command is already unambiguously bounded by the
   last group's closing delimiter.
4. No whitespace is permitted between the identifier and the first group, or
   between adjacent groups — implemented by checking trailing trivia on each
   group's closing delimiter, not a separate whitespace-scanning pass.
   Whitespace where a group would start simply ends the group-reading loop
   (falls through to the zero-group/legacy path); it is not an error.
5. First slice is **block position only**. Inline `\func(...)`/`[...]` (the
   `YmBackslash` inline TODO) and postfix `[text]:func {}` remain deferred.

Implemented in `a7928657` (`parser: parse grouped Yumark block commands`),
`crates/parser/src/mark/parse.rs`. Six new targeted tests in
`crates/parser/tests/mark_grammar.rs` cover: repeated/mixed-order groups,
inline-before-expr reordering, `;` termination without legacy-body
fallthrough, legacy fallback preserved unchanged, the named-parameter-via-
record-in-parens pattern with nested quoted Yumark, and malformed/unclosed-
group recovery (`InvalidToken`, not a panic or silent fallback). Full existing
parser suite (259 tests across mark/expr/stmt grammar) and the full contract
corpus (225 cases) both green — no regressions.

This grammar work does not yet connect to lowering or the `yumark_node` value
model from earlier sections — see "Parser/lowering integration" below.

### Command name resolution: ordinary functions/variables, no special mechanism (decided 2026-07-08, not yet implemented)

`\ident(...)` should resolve `ident` via ordinary name lookup — no dedicated
"this is a Yumark command" declaration or registration mechanism. Whether a
given `ident` is usable as a command is gated entirely by ordinary
type-checking: does `ident` (applied to whatever groups are present) produce
something that fits into the Yumark tree/injection shape? If the types line
up, it works; if not, a normal compile error, same as any other misapplied
function call.

- A bare variable (zero groups) works the same way — `\myconst` just
  references an existing binding, as long as its type already matches. This
  gives macro-like reuse via ordinary `my` bindings, no special "define a
  macro" ceremony needed.
- Consistent with this session's repeated pattern of reusing existing
  mechanisms rather than inventing new ones (named params via record
  literals, `Throw`/`ParseError` roles reused rather than a new `Error` role,
  etc.).
- Not yet implemented — this is a decision for when lowering work starts (see
  "Parser/lowering integration" in Open items), recorded now so it doesn't
  need re-deciding.

## Open items / not addressed this session

- The capability-boundary idea for injected content (point 3 under "No custom
  Yumark effect") — whether/how to statically bound what operations are legal
  inside a Yumark document before backend selection.
- Inline-position `\func(...)`/`[...]` and postfix `[text]:func {}` surface
  syntax — only block-position grouped commands are implemented so far (see
  "Surface syntax" above).
- Whether/how the `[\each(...)]:list` postfix-method-with-embedded-effect
  syntax could work at all, given effect legality would need to be checked
  before backend/tagless-final selection.
- Parser/lowering integration — turning the real `crates/parser/src/mark/` CST
  (including the new grouped-command nodes) into typed cons-chain values — has
  not been attempted; every PoC (see evidence trail) only proves the
  value-model shape in isolation, disconnected from the real parser. Likely
  harder now than it would have been for the flat-enum design, since lowering
  must produce a value whose *type* encodes the parsed shape — worth its own
  design pass before starting.
- ~~What the node/leaf vocabulary should look like under the cons-chain
  design~~ — done: see "Static vocabulary ported to the typed cons-chain"
  above.
- ~~Solver performance for named rendering functions~~ — precisely
  characterized, see "Performance risk found, precisely characterized" above:
  narrowly a zero-argument named binding rendering Markdown internally, not
  named functions in general. Still genuinely open: *why* Markdown's
  inductive role chain triggers expensive generalization and HTML's doesn't.

### `yulang`-tagged code fences: two independent consumers, not one (2026-07-08 clarification)

A `yulang` fenced block in a doc comment is source for **two separate,
decoupled features**, not one:

1. **Document rendering** (this value model, `yulang doc`): always treated as
   plain source text, same as any other fence — never executed, never treated
   specially. For HTML output, syntax highlighting is a nice-to-have that can
   be derived from the real, already-parsed Yulang AST (precise token/span
   classification for free) rather than a heuristic highlighter — but it's
   still just displaying code, not running it.
2. **Test execution** (a future, separate doctest-style test runner — not yet
   built, not part of `doc`): extracts and *runs* `yulang`-tagged fences as
   tests. This is the reason the parser parses `yulang` fences as embedded
   statements at all.

The value model only needs to serve (1); it should keep treating `yulang`
fences the same as any other `code_fence_info`/`code_fence_text` pair (as the
static-vocab PoC already does) and never special-case the language tag.

## Evidence trail

`examples/yumark_typed_structure_poc.yu` (below) is the only PoC using the
*adopted* tree representation. The four PoCs before it all used the flat-enum
`yumark_node` tree that was superseded same-day — kept here because their
sub-findings about role mechanics, Candidate A/B, and associated types are
still correct and still relied upon; only their tree-structure choice was
wrong.

- `examples/yumark_value_model_poc.yu` — first PoC: effect-timing control,
  role-requires-role (`YumarkRender` requiring `YumarkHandle`), confirmed
  working directly at role-declaration level (no `where`-clause fallback
  needed). Did not test type-level divergence (repr hardcoded to `str`). Flat
  enum, superseded structurally.
- `examples/yumark_value_model_poc2.yu` — second PoC: genuine backend-typed
  divergence (`html_node` vs `str`), Candidate A failure / Candidate B success,
  tag-parametrized role + associated `repr` + effect-row-polymorphic methods
  all confirmed working together. No real effects used (plain value returns).
  Flat enum, superseded structurally.
- `examples/state_handler_escape_repro.yu` — state/handler dynamic-extent
  escape, diagnostic only. Independent of tree representation, still accurate.
- `examples/clock_effect_direct_repro.yu`, `examples/clock_effect_field_repro.yu`
  — minimal isolation of the evidence-vm record-boundary bug. Independent of
  tree representation, still accurate.
- `examples/yumark_effectful_injection_capstone.yu` — capstone: Candidate B
  with a real effect (`clock::now`) inside struct-field-stored closures,
  producing genuinely backend-native typed output end to end. Flat enum,
  superseded structurally; the Candidate B mechanism itself is reused as-is.
- `examples/yumark_static_vocab_poc.yu` — extends the value model with the
  parser's static/structural CST vocabulary (heading, blank line, list/list
  item, code fence, block quote, emphasis, strong, section close, doc),
  following the same role/injection pattern. Both backends render the full
  expanded vocabulary, including an injection nested inside a block quote.
  Macro/injection-related CST nodes (command, inline bracket expression, link
  destination, image-like inline) are intentionally deferred to the
  `\func(){}[]` / `[text]:func {}` work. Flat enum, superseded structurally —
  vocabulary re-ported under the cons-chain design in
  `yumark_typed_static_vocab_poc.yu` below.
- `examples/yumark_typed_structure_poc.yu` — **adopted design**: hand-rolled
  `cons_cell`/`nil_cell` generic types, inductive `YumarkRender` instance
  derivation, positive case (4-leaf chain renders via a derived instance, no
  bespoke instance written), negative case (a non-implementing leaf correctly
  fails to compile), and confirmed compatibility with Candidate B injection
  leaves and inert construction. Commit `8bd02dec`.
- `examples/yumark_typed_static_vocab_poc.yu` — **adopted design**, full
  vocabulary: ports every static-vocab node kind (heading, blank line,
  list/list item, code fence, block quote, emphasis, strong, section close,
  paragraph, doc) to the typed cons-chain, each container generic over its
  children's type with an inductive `YumarkRender` instance mirroring
  `cons_cell`'s own. `code_fence_info`/`code_fence_text` collapsed into one
  `code_fence_leaf`. A representative multi-node document (including a
  block-quoted injection) renders correctly in both formats with zero
  bespoke per-shape instances. Commit `af4cebc6`. Follow-up same day
  precisely isolated a solver-performance finding from this file (see
  "Performance risk found, precisely characterized" under "Tree
  representation, revised"): narrowly, a zero-argument named binding
  rendering Markdown internally, not named functions in general — passing
  the document as an explicit parameter avoids it entirely.
