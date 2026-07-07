# Yumark value model: tagless-final-flavored design (2026-07-08, Claude 署名・authoritative)

Status: design decisions from an extended design session, empirically verified via
PoCs in `examples/`. This is the authoritative record of *why* the shape below was
chosen and what alternatives were rejected and why. Implementation of the real
Yumark parser/lowering/stdlib surface has not started; this covers the value model
only.

## Summary

Yumark documents are represented as a concrete, inert tree (initial encoding), and
rendered to a target format (HTML, Markdown, ...) via a role-based interpreter
layer that is tagless-final-*flavored* (extensible per-backend dispatch) but not
pure tagless-final (no dictionary-passing term, no rank-2 storage). Injection
(the `\func(){}[]` / `[text]:func {}` macro mechanism) produces genuinely
backend-native typed content by bundling one monomorphic thunk per supported
format inside the injection node, not by storing a polymorphic function as data.

## Tree representation

`yumark_node` is a plain recursive `enum` (text / inject / paragraph, extendable
with more node kinds later): inert data, building it never forces anything.
Injection payloads carry per-format closures (see below), never a materialized
`yumark_node` for "what a macro can produce" — the tree's own node kinds are for
the backend-agnostic common vocabulary (text, paragraph, headings, lists, ...);
injected macro output is not required to be expressible in that vocabulary.

Rationale for *not* using pure tagless-final (a `forall repr. Algebra repr =>
repr` term with no intermediate structure): Yulang is eager, not lazy. A pure
dictionary-passing term would force construction to commit to a concrete `repr`
immediately (building a `list repr` argument requires evaluating each element),
which both (a) defeats "same document, multiple backends" and (b) fires embedded
effects at construction time instead of at a controlled, deliberate walk step.
The concrete tree defers everything: effects inside injected content fire only
when a `walk` function forces that specific node, in tree-structural order,
which coincides with strict-evaluation order — deferred, but not reordered.

## Render role shape

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
  instance mechanism today (confirmed by the stdlib's manual per-arity
  Display/Debug impls for tuples 2..5) — a true type-level list with
  array-like decomposition would need new infer/poly work. Not needed for
  Yumark: once content flows through a render role, everything is already
  uniformly `repr`-typed, so ordinary `list repr` suffices for children.

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

## Open items / not addressed this session

- The capability-boundary idea for injected content (point 3 under "No custom
  Yumark effect") — whether/how to statically bound what operations are legal
  inside a Yumark document before backend selection.
- `\func(){}[]` prefix and `[text]:func {}` postfix surface syntax — parser
  support exists only for a bare `\cmd` block command
  (`crates/parser/src/mark/`); the bracket-group semantics (args vs body vs
  extra group) are still unspecified.
- Whether/how the `[\each(...)]:list` postfix-method-with-embedded-effect
  syntax could work at all, given effect legality would need to be checked
  before backend/tagless-final selection.
- Parser/lowering integration — turning the real `crates/parser/src/mark/` CST
  into `yumark_node` values — has not been attempted; the static-vocab PoC
  (see evidence trail) only proves the value-model shape in isolation.

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

- `examples/yumark_value_model_poc.yu` — first PoC: effect-timing control,
  role-requires-role (`YumarkRender` requiring `YumarkHandle`), confirmed
  working directly at role-declaration level (no `where`-clause fallback
  needed). Did not test type-level divergence (repr hardcoded to `str`).
- `examples/yumark_value_model_poc2.yu` — second PoC: genuine backend-typed
  divergence (`html_node` vs `str`), Candidate A failure / Candidate B success,
  tag-parametrized role + associated `repr` + effect-row-polymorphic methods
  all confirmed working together. No real effects used (plain value returns).
- `examples/state_handler_escape_repro.yu` — state/handler dynamic-extent
  escape, diagnostic only.
- `examples/clock_effect_direct_repro.yu`, `examples/clock_effect_field_repro.yu`
  — minimal isolation of the evidence-vm record-boundary bug.
- `examples/yumark_effectful_injection_capstone.yu` — capstone: Candidate B
  with a real effect (`clock::now`) inside struct-field-stored closures,
  producing genuinely backend-native typed output end to end.
- `examples/yumark_static_vocab_poc.yu` — extends the value model with the
  parser's static/structural CST vocabulary (heading, blank line, list/list
  item, code fence, block quote, emphasis, strong, section close, doc),
  following the same role/injection pattern. Both backends render the full
  expanded vocabulary, including an injection nested inside a block quote.
  Macro/injection-related CST nodes (command, inline bracket expression, link
  destination, image-like inline) are intentionally deferred to the
  `\func(){}[]` / `[text]:func {}` work.
