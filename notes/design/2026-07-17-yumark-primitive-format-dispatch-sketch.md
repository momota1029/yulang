# Yumark primitive format dispatch: first-pass design sketch

Status: **exploratory, not approved, and not implementation-ready**. This note is a starting point
for a design conversation with Yulang's designer. It does not amend the authoritative Yumark value
model in `notes/design/2026-07-08-yumark-value-model-tagless-final.md`, the role-system
specification, or the effect-row specification. No syntax below is settled.

This note uses three labels deliberately:

- **ESTABLISHED FACT** reports the already-characterized current system or cost. These facts are
  inputs to this sketch and are not re-derived here.
- **PROPOSED CHOICE** is a concrete starting position, not a decision.
- **OPEN DECISION** marks a language-design choice that the user needs to approve, refine, or
  redirect. A proposal must not silently turn one of these into a specification.

## 0. Problem boundary and success criterion

**ESTABLISHED FACT:** current Yumark is a first-order typed `cons_cell` / `nil_cell` inductive
tree. `YumarkRender 'node 'format` role implementations interpret that tree and publish the
associated type `repr`. This is tagless-final-*flavored*, but it is not a genuine tagless-final
term encoding: there is no rank-2 or dictionary-passing document term. The same tree can derive
both HTML and Markdown interpretations, and callers explicitly select one through
`render_html_doc` or `render_markdown_doc`.

**ESTABLISHED FACT:** at the expensive `proof` root, there are 71 recursive prerequisite edges:
28 `cons_cell` applications contribute 56 edges and 15 unary containers contribute 15. Each
occurrence scans all 32 candidates in the shared `YumarkRender` bucket (16 node implementations
per format times two formats), so the first full walk performs `71 * 32 = 2,272` candidate scans.
The resulting 72-node resolution tree then publishes its associated-`repr` equalities as invariant
constraints. Of those, 179 upper-bound facts are new and non-subsumed. The next generalization
iteration consequently recomputes 79.7% of variable summaries and 100% of dominance intervals.

**ESTABLISHED FACT:** `CastTable` is relevant as a cost model, not as a claim that cast runs outside
generalization. Its cheapness comes from a flat, non-recursive lookup keyed by the concrete source
and target constructor paths. It does not scan a broad role bucket, recursively prove prerequisite
roles, or compute transitive closure over the cast graph. Cast can still add constraints and cause a
generalization restart.

**ESTABLISHED FACT:** effect rows already have a powerset-lattice-like algebraic core: positive
union, negative intersection, named membership, and open tails. They are nevertheless an unsafe
implementation shortcut for this feature. Their representation and inference are coupled to
effect subtraction, stack weights, and handler hygiene. They have no per-tag representation
function, singleton/exact-one selection rule, or interpreter evidence.

The target is therefore stronger than "index the existing role bucket by format." A successful
design should make format selection a direct, structured lookup; keep the format capability
algebra separate from effect rows; and retain a genuinely interpreter-parametric document term,
including a path to executing a document as a non-string representation.

**OPEN DECISION 0 — meaning of "document value":** is it sufficient that a let-bound document
builder can be generalized and applied at several interpreter types, or must a document also be
storable in a struct, passable as an ordinary function argument, and later interpreted at more
than one representation? The first is expressible with ordinary rank-1 Hindley-Milner
let-polymorphism. The second requires either controlled higher-rank storage or a new primitive that
hides it. This decision changes the project from a moderate extension into a foundational one.

## A. Candidate shapes

### A.1 What "genuine tagless-final" can mean in Yulang

A minimal finally encoded document is a term that consumes an interpreter algebra rather than an
initial tree later visited by a separate renderer. In pseudocode:

```yu
my hello alg =
    alg.cons (alg.text "hello") alg.nil

my html: html_node = hello html_yumark
my markdown: str = hello markdown_yumark
```

Here the structure of `hello` is executed against the supplied algebra. An interpreter's
representation need not be text: it may be `html_node`, a DOM/component program, an evaluator
result, or some other type. This is the semantic property this sketch calls "genuine
tagless-final"; merely adding an extensible visitor over the current cons tree does not meet it.

**ESTABLISHED FACT:** ordinary HM can generalize the let-bound function above roughly as
`forall 'repr. yumark_alg 'repr -> 'repr`. It can instantiate `hello` once for `html_node` and once
for `str` at two use sites. HM does not, however, allow a normal struct field or monomorphic
function parameter to hold that whole polymorphic scheme and instantiate it later. The earlier
Yumark injection Candidate A encountered this boundary; Candidate B worked by storing one
monomorphic thunk per format.

**PROPOSED CHOICE A1:** use explicit algebra-parametric terms as the semantic oracle for all
candidate designs. A primitive is acceptable only if it elaborates to the same discipline: the
document body is checked under an abstract representation and can only construct that
representation through the supplied algebra.

**OPEN DECISION A1.1 — strength of parametricity:** should the new mechanism guarantee this
abstraction through a rigid/skolem representation variable, or is a conventionally typed algebra
record enough? A compiler-enforced abstraction gives a meaningful `Final` guarantee; a plain
record function is smaller but can expose representation-specific operations if inference happens
to learn a concrete type.

**OPEN DECISION A1.2 — direct execution:** must surface syntax support a form such as
`document @browser`, where the selected representation is itself an executable component/effectful
program, or is `run document with browser_interpreter` sufficient? Both are tagless-final in the
term sense; the distinction is ergonomics and whether a global/default interpreter-selection
mechanism belongs in the language.

### A.2 Candidate 1: a dedicated tag-row lattice plus an ordinary HM final builder

One option is to introduce a new type kind for format/tag membership and keep the term encoding as
an ordinary algebra-consuming function. A possible, deliberately unsettled notation is:

```yu
# illustrative only
my hello: final_fn Yumark { html => html_node, markdown => str } =
    \alg -> alg.cons (alg.text "hello") alg.nil
```

The tag row is a finite-map or capability-set view of the formats at which the term may be run.
The algebra function remains the actual term-level interpretation mechanism. Selecting one tag
performs a direct row lookup to obtain its representation and interpreter dictionary; it does not
ask `RoleImplTable` to discover a derivation.

**PROPOSED CHOICE A2:** make this a new `tag row` kind, not an instance of `Pos::Row` / `Neg::Row`
as currently used for effects. It may reuse general algebraic ideas, but it should have its own
IDs, constraints, normal form, diagnostics, and generalization witness. This prevents tag
membership from accidentally acquiring effect-subtraction, stack-lifetime, or handler-hygiene
semantics.

This candidate has a useful low-cost subset. If `hello` remains a let-bound generalized function,
ordinary HM can instantiate it with two explicit algebra values. The compiler needs tag-row
bookkeeping and exact interpreter lookup, but no first-class rank-2 package.

Its limitation is structural: `final_fn ...` cannot honestly be an ordinary first-class field type
if it contains a polymorphic interpreter consumer. Passing `hello` to a function generally
instantiates it once; storing it loses the ability to choose HTML or Markdown later. A tag row
describes supported formats, but a row alone does not manufacture the polymorphic term evidence it
claims to describe.

**OPEN DECISION A2.1 — row contents:** should a row structurally store entries such as
`html => html_node`, or should it store only `html` membership while a family-level functional
dependency `Repr(Yumark, html) = html_node` supplies the representation? The first is visibly
self-contained but risks merging an invariant `repr` argument at every composition node—the shape
most likely to recreate the 179-fact pathology. The second centralizes one representation fact per
`(family, tag)` and is the leading recommendation, but it makes family coherence a language rule.

**OPEN DECISION A2.2 — open tails:** should tag rows support `{html, ..'r}` and future format
extension, or should the first version permit only closed sets? Open tails preserve extensibility
and generic combinators, but add row variables, lacks constraints, quantification, and possible
restart work. Closed rows are much easier to characterize but make "supports any future Yumark
interpreter" impossible to state without a distinguished top element.

**OPEN DECISION A2.3 — lattice orientation:** the membership sets naturally have union, meet, top,
and bottom, but `Final` capability subtyping must still be chosen. A value supporting
`{html, markdown}` can safely be used where only `{html}` is required, suggesting capability
width-subtyping. Composition of two fragments normally supports the intersection of their sets.
The exact positive/negative rules must be derived rather than copied from effect rows.

**Assessment:** promising as type-level bookkeeping and as a Stage-0 rank-1 experiment, but
insufficient by itself if "document value" means reusable first-class polymorphic data.

### A.3 Candidate 2: a flat `(document shape, format tag)` interpreter table

A second option stays closer to the current typed cons tree and replaces role lookup with a
primitive registry. In its workable form, the key would be something like
`(NodeConstructorId, TagId)`, not the complete nested document type: a table cannot pre-register
every possible `cons_cell H T` document shape. The current 32 implementations would become 32
exact entries such as `(cons_cell, html)`, `(cons_cell, markdown)`, `(text_leaf, html)`, and so on.

For Markdown `cons_cell`, resolution would find the single `(cons_cell, markdown)` entry directly,
then recursively select `(HeadConstructor, markdown)` and `(TailConstructor, markdown)`. That is at
most one small exact bucket per visited node rather than 32 scans per prerequisite. A 72-node tree
would therefore perform on the order of 72 exact lookups, not 2,272 candidate scans.

**PROPOSED CHOICE A3:** if this candidate is pursued, keys must use resolved declaration identities
such as `TypeDeclId` / a new `TagId`, never string tests for `cons_cell`, `html`, a module path, or
Yumark. The primitive must be a general declaration mechanism rather than a Yumark-specific branch
inside inference.

The honest weakness is that this remains an initial, typed-tree encoding with an extensible
primitive visitor. Calling `interpret doc @html` directly would be pleasant syntax, but the
document term itself does not consume an abstract algebra. Interpreter evidence is still assembled
recursively over document shape. If each selected entry carries its own associated `repr` equality,
the candidate-scan cost falls while the 72-node equality-publication tree—and therefore a version
of the 179-fact/recompute pathology—can remain.

**OPEN DECISION A3.1 — goal relaxation:** would direct interpretation of a typed initial tree count
as sufficient if it is extensible and cheap, or is interpreter-parametric construction itself
non-negotiable? Under the latter reading, this candidate is a fallback, not a solution.

**OPEN DECISION A3.2 — recursive evidence:** should the exact entry recursively return child
evidence, or should interpretation simply recurse at runtime? Compile-time evidence preserves
static rejection of unsupported leaves but can still build a large proof tree. Runtime recursion is
cheap to infer but either needs a uniform runtime tag/shape representation or moves missing-format
errors to runtime.

**Assessment:** likely the smallest route to eliminate broad candidate scans, probably size M-L,
but it does not independently satisfy genuine tagless-final semantics and may not eliminate the
associated-bound publication burst.

### A.4 Candidate 3 (leading): a primitive `Final` family, a tag-capability lattice, and one flat interpreter lookup

The most promising way to satisfy both halves of the goal is a hybrid:

1. a user-declarable **interpretation family** defines the algebra shared by all of its tags;
2. a primitive `Final<Family, Shape, Tags>` value packages a controlled polymorphic dictionary
   consumer;
3. `Tags` is a separate capability lattice describing where the value can run;
4. each interpreter declaration establishes one functional mapping
   `(FamilyId, TagId) -> (ReprType, Dictionary)` in a flat table; and
5. running a document selects the dictionary once at the root, then threads that same dictionary
   through the finally encoded term.

Illustrative syntax only:

```yu
# all names and delimiters are placeholders
interpretation family Yumark:
    repr
    nil: repr
    cons: repr -> repr -> repr
    text: str -> repr
    heading: int -> repr -> repr

interpreter html for Yumark:
    type repr = html_node
    # implementations of nil/cons/text/heading/...

interpreter markdown for Yumark:
    type repr = str
    # implementations of nil/cons/text/heading/...

my hello: Final Yumark (cons_cell text_leaf nil_cell) <html, markdown> =
    yumark.cons (yumark.text "hello") yumark.nil

my html_value: html_node = hello @html
my markdown_value: str = hello @markdown
```

Conceptually, the primitive package contains a term of this form:

```text
forall tag in Tags.
    YumarkAlgebra(Repr(Yumark, tag)) -> Repr(Yumark, tag)
```

`final` introduction checks the body using a fresh rigid representation type and only the family
algebra. `@html` elimination obtains `html`'s exact dictionary, opens the package at that one
representation, and returns `Repr(Yumark, html)`. This is a deliberately narrow higher-rank feature
behind a primitive boundary rather than general impredicative polymorphism throughout HM.

**PROPOSED CHOICE A4:** make `(FamilyId, TagId) -> ReprType` a functional dependency validated at
interpreter declaration/import time. The tag capability row should store membership and refer to
that mapping, rather than carrying fresh invariant representation variables at every node. This is
the key type-level move intended to avoid reproducing the 179 associated-bound facts.

**PROPOSED CHOICE A5:** organize today's 32 node/format implementations as two interpreter
dictionaries (HTML and Markdown), each with the family algebra's roughly 16 operation slots. The
compiler performs one exact `(YumarkFamilyId, MarkdownTagId)` lookup at a run site. Document
construction and composition do not consult the interpreter table at all.

**OPEN DECISION A4.1 — controlled rank 2:** should `Final` be a first-class primitive package, or
should v0 expose only the ordinary let-generalized function form and postpone storage/passing? The
primitive is the only candidate here that fully answers the strong reading of Decision 0, but it
requires new introduction/elimination, escape checking, serialization, specialization, and runtime
ABI rules.

**OPEN DECISION A4.2 — preserve typed shape:** should `Shape` retain the current nested
`cons_cell H T` / leaf structure as a phantom parameter, or should all documents share
`Final Yumark Tags`? Retaining shape gives migration parity and leaves room for shape-sensitive
static checks, but continues to place large nested types in inference and specialization. Erasing
shape is closer to classic tagless final and gives a much smaller public type, but revises an
authoritative Yumark choice and needs explicit user approval.

**OPEN DECISION A4.3 — algebra extensibility:** a closed family algebra makes adding a new format
easy (one new dictionary) but adding a new node operation requires updating every interpreter. The
current per-node role encoding is open in both dimensions at higher inference cost. Should the
family algebra be closed, row-polymorphic in operations, or versioned? An operation-row design may
recover extensibility but compounds two novel row systems and should not be assumed safe.

**OPEN DECISION A4.4 — global coherence versus explicit values:** should there be exactly one
visible interpreter per `(family, tag)`, or may programs pass several values with the same tag
(for example two HTML policies)? A coherent global table makes `doc @html` a single lookup.
Explicit `run_with doc custom_html` permits configuration without ambiguity. A plausible split is
one optional coherent default plus arbitrary explicit dictionaries, but that is still a user
decision.

**OPEN DECISION A4.5 — effects:** should `Final` track construction effects, interpretation
effects, or both in its type? The current document construction is inert and injected work is
forced at render time. The new tag lattice must not absorb effect-row responsibilities. Any effect
parameter should remain an ordinary Yulang effect row, with a separately stated value-restriction
and package-generalization rule.

**OPEN DECISION A4.6 — unsupported intersection:** composition can yield the bottom capability set
when two fragments share no interpreter. Should constructing that value be legal but impossible to
run, or should the compiler reject the composition immediately? Eager rejection gives clearer
Yumark diagnostics; retaining bottom gives a complete lattice and can preserve principality in
generic code.

**Assessment:** this is the strongest fit for the stated goal and the leading candidate for the
rest of this sketch. It potentially collapses recursive compile-time proof search into capability
row composition plus one root dictionary selection. It is also the largest and highest-risk
candidate because it adds controlled first-class polymorphism, not merely a faster lookup table.

### A.5 Candidate 4: explicit algebra records only (validation oracle, not the stated destination)

The smallest alternative is to use ordinary records/functions and write `hello html_yumark`
directly, without tag rows, a registry, or a `Final` package. This is real finally encoded code for
let-bound builders and should be used to test semantics, effects, and backend-native
representations before inventing a primitive.

It does not meet the full requested shape: there is no primitive lattice, no exact tag selection,
and no first-class polymorphic document. Its value is as a Stage-0 oracle. If even this form cannot
preserve Yumark's construction inertness, injection timing, and two-representation behavior, a
larger primitive will not rescue the underlying term design.

**PROPOSED CHOICE A6:** use the explicit-record form as the semantic and performance control in
Stage 0, while treating Candidate 3 as the leading language direction.

**OPEN DECISION A5.1 — staging:** should the project first ship the rank-1 explicit form and reserve
syntax for a future `Final`, or should no user-facing surface land until the first-class story is
settled? Shipping a subset gives evidence sooner but risks freezing a surface that cannot evolve
cleanly.

### A.6 Candidate comparison

| Candidate | Broad bucket scan removed? | Associated-bound burst removed? | Genuine final term? | First-class multi-run value? | Rough scope |
|---|---:|---:|---:|---:|---:|
| Dedicated tag row + HM builder | yes | plausible, if `repr` is family-level | yes, while let-bound | no | M-L |
| Exact node/tag table | yes | not necessarily | no | tree value only | M-L |
| Primitive `Final` + tag lattice + family/tag table | yes | plausibly yes | yes | yes | XL |
| Explicit records/functions only | roles disappear | yes | yes, while let-bound | no | S-M oracle |

**PROPOSED CHOICE A7:** carry Candidates 3 and 1 into concrete design: Candidate 3 is the target
that fully satisfies the stated goal, while Candidate 1 is its rank-1 staging subset and semantic
fallback. Candidate 2 should be retained only if the user explicitly relaxes genuine tagless-final
construction.

## B. Concrete sketch for the leading candidate

### B.1 Proposed semantic pieces

The leading candidate has four distinct responsibilities. Keeping them separate is important: if
they are all represented as ordinary invariant type bounds, the design can recreate the current
cost under new names.

1. **Family signature:** the operations through which a finally encoded program constructs an
   abstract representation.
2. **Tag capability:** the set/lattice of tags at which one program is runnable.
3. **Representation selection:** a functional type-level lookup from `(family, tag)` to one result
   representation.
4. **Interpreter evidence:** the term-level dictionary used when the program is opened at that tag.

**PROPOSED CHOICE B1:** introduce structured compiler identities resembling
`InterpretationFamilyId` and `InterpretationTagId`. Source names resolve to these IDs before
inference. Tag rows and table keys use the IDs, so renaming a tag or moving a module cannot change
type inference except through ordinary name resolution.

**PROPOSED CHOICE B2:** give each visible `(FamilyId, TagId)` at most one default table entry:

```text
InterpreterKey(FamilyId, TagId)
    -> { repr_scheme, dictionary_def, family_signature_generation }
```

This is closer to `CastTable` than to `RoleImplTable`: lookup addresses one bucket directly, there
are no prerequisite entries, and the table does not compute transitive closure. Declaration-time
checking verifies that the dictionary implements every required family operation. It does not
repeat that conformance proof at each document node or each run site.

**OPEN DECISION B1.1 — generic representation schemes:** may `repr` itself be parameterized (for
example by an environment or error type), or must v0 map a tag to one closed constructor-headed
type? A generic `repr_scheme` is more expressive but makes exact selection and ambiguity closer to
generic impl matching. A closed v0 keeps the table genuinely flat.

**OPEN DECISION B1.2 — visibility and duplicate keys:** should duplicate defaults be rejected
globally, rejected only when simultaneously visible, or treated as an ambiguity at `run`? Early
coherence gives the strongest constant-cost guarantee. Use-site ambiguity is more modular but may
require buckets larger than one.

### B.2 Illustrative surface and core typing shape

The following is intentionally pseudocode. It is concrete enough to expose typing questions, but
the user should choose all final keywords and delimiters.

```yu
# ILLUSTRATIVE ONLY — not proposed final syntax
interpretation Yumark:
    nil: repr
    cons: repr -> repr -> repr
    doc: repr -> repr
    text: str -> repr
    paragraph: repr -> repr
    heading: int -> repr -> repr
    # ...the remaining Yumark vocabulary...

interpreter html for Yumark:
    repr = html_node
    nil = html_nil
    cons = html_cons
    doc = html_doc
    text = html_text
    paragraph = html_paragraph
    heading = html_heading

interpreter markdown for Yumark:
    repr = str
    nil = markdown_nil
    cons = std::text::str::concat
    doc = markdown_doc
    text = markdown_text
    paragraph = markdown_paragraph
    heading = markdown_heading
```

One possible type display is:

```text
Final<Yumark, cons_cell<text_leaf, nil_cell>, <html, markdown>>
```

The same information could be displayed as `yumark <html, markdown>` or
`Final Yumark {html => html_node, markdown => str}`. These are presentation alternatives, not
different semantics.

**OPEN DECISION B2.1 — notation:** the user needs to choose whether `Final`, the family, the shape,
and the tag row are explicit in ordinary signatures, inferred and only shown in hover, or partly
surface sugar. In particular, displaying `tag => repr` can be useful even if the internal row only
stores tag membership and obtains `repr` from the family table.

At the core level, the useful constructor types would have this shape:

```text
nil  : Final<F, Nil, TopTags<F>>
text : str -> Final<F, Text, TopTags<F>>

cons : Final<F, H, Rh>
    -> Final<F, T, Rt>
    -> Final<F, Cons<H, T>, Meet<Rh, Rt>>

heading : int
       -> Final<F, Children, Rc>
       -> Final<F, Heading<Children>, Rc>

run<Tag>(Final<F, Shape, R>) : Repr<F, Tag>
    requires Member<Tag, R>
```

`TopTags<F>` means any tag with a conforming interpreter for `F`, not `Any` in Yulang's type
system. `Meet` is capability intersection. Neither is an alias for Yulang `Any`, `Never`, or
`Unknown`.

**PROPOSED CHOICE B3:** keep `Unknown` as the only unresolved placeholder. A not-yet-inferred tag
row uses its own row variable; top and bottom tag capabilities are real lattice elements, not
fallback types. This keeps the new feature aligned with Yulang's existing Top/Bottom/Unknown
distinction.

**OPEN DECISION B2.2 — nominal shape parameter:** the types above retain current document shape as
a phantom parameter. That is the conservative migration sketch, not a settled recommendation.
If shape has no consumer after roles disappear, removing it may materially reduce inference and
monomorphization size. Stage 0 should measure both forms before the authoritative typed-cons choice
is reconsidered.

### B.3 Term representation and controlled polymorphism

A primitive `Final` value can be understood as a closure with an environment and a hidden
dictionary parameter. Introduction checks one program under a fresh abstract representation:

```yu
# ILLUSTRATIVE ONLY
my greeting = final Yumark \alg ->
    alg.cons (alg.text "hello") alg.nil
```

An approximate typing rule is:

```text
under fresh rigid a and alg : Algebra<F, a>,
if body : a and a does not escape,
then final F (\alg -> body) : Final<F, Shape, R>
```

Opening the program at a concrete tag is the dual rule:

```text
doc : Final<F, Shape, R>
Tag in R
InterpreterTable[F, Tag] = (Repr, dict)
------------------------------------------------
doc @Tag : Repr
```

At runtime this can be a closure call with `dict` as a hidden argument. At specialization time a
known tag may permit dictionary-slot calls to become direct calls. Neither optimization is needed
for the type-system argument; the semantic requirement is that the same selected dictionary is
threaded through the whole document program.

**PROPOSED CHOICE B4:** restrict the higher-rank capability to `Final` introduction and
elimination initially. Do not infer arbitrary rank-2 function parameters, impredicative container
fields, or general `forall` values as an accidental side effect of solving Yumark.

**OPEN DECISION B3.1 — explicit core form:** should users write `final` / `run`, or should Yumark
combinators construct the package invisibly while only compiler IR contains the binder? Explicit
forms make the abstraction reusable beyond Yumark and easier to specify. Invisible forms give a
smaller surface but risk a builtin feature whose boundaries are hard to explain.

**OPEN DECISION B3.2 — value restriction:** may an effectful expression be generalized into a
`Final`, or must construction be syntactically/value-semantically inert? Existing Yumark relies on
effects firing during interpretation, not construction. The new rule needs a precise interaction
with HM generalization and ordinary effect rows before it can be sound.

**OPEN DECISION B3.3 — injection:** a backend-native injected value cannot generally be built under
one abstract `repr`. There are at least two honest options: require injection to be expressed only
through family operations (fully parametric), or permit a finite tag-indexed package containing one
monomorphic thunk per supported tag (the current Candidate B behavior). The second preserves
existing expressiveness and timing but introduces a controlled non-parametric branch inside an
otherwise final program. This should be named explicitly rather than described as pure
parametricity.

### B.4 Node-by-node cost walkthrough

The central difference is that format selection no longer happens at each node.

#### Construction/generalization

Consider a representative subtree:

```text
cons(text("a"), paragraph(cons(text("b"), nil)))
```

The proposed inference work is:

1. `text("a")` constructs a `Final` program. Its generic algebra call is checked when the `text`
   combinator is defined, not by selecting an HTML or Markdown candidate at this occurrence.
2. The inner `text("b")` behaves the same way.
3. `nil` has the family's top tag capability.
4. The inner `cons` computes `Meet(R_text_b, R_nil)` and packages a closure which invokes both
   children with the same future algebra argument. It performs no interpreter lookup.
5. `paragraph` carries or restricts its child's capability row according to the declared
   combinator type. It performs no interpreter lookup.
6. The outer `cons` computes one more meet and packages another closure. It performs no
   interpreter lookup.

Applied to the characterized Yumark root:

- the 28 `cons_cell` applications still have 56 structural child inputs, but each application does
  one capability meet and wires two ordinary child program calls;
- the 15 unary containers carry or meet one child capability;
- no occurrence reads the shared 32-candidate `YumarkRender` bucket;
- no occurrence recursively asks for a prerequisite role proof; and
- no occurrence publishes a fresh associated-`repr` equality.

Thus the 71 structural connections do not become `71 * 32` candidate work. With closed or
canonicalized rows, they are set/row operations. With open rows, they are row constraints whose
actual cost must be measured; this sketch does not assume those constraints are free.

#### Interpretation

At `document @markdown`, the compiler:

1. proves or checks direct membership `markdown in R_document`;
2. performs one exact lookup of
   `InterpreterKey(YumarkFamilyId, MarkdownTagId)`;
3. obtains `Repr(Yumark, markdown) = str` and the Markdown dictionary;
4. calls the root `Final` closure with that dictionary; and
5. lets every nested closure call known dictionary slots such as `cons`, `paragraph`, and `text`.

The runtime still visits document operations; rendering inherently does that work. What disappears
is compile-time discovery of a separate role implementation and associated-type proof at every
node. With two run sites, HTML and Markdown cause two exact root selections, not a shared-bucket
scan at all 71 prerequisite occurrences.

| Work item | Current role encoding | Leading sketch |
|---|---:|---:|
| Recursive proof edges at the measured root | 71 | 0 role edges; 71 structural capability inputs remain |
| Candidate scans for the characterized Markdown proof | 2,272 | 0 during construction; 1 exact table lookup per run site |
| Interpreter evidence tree | 72 nodes | 1 root dictionary threaded through the term |
| Per-node associated `repr` equalities | yes | no; one family/tag projection at the run boundary |

**OPEN DECISION B4.1 — when membership is checked:** should a closed tag row reject an unsupported
node at composition time, or should only `run @tag` require membership? Composition-time
diagnostics resemble today's static failure. Use-site-only constraints can infer more general
fragments but may report the error farther from the incompatible leaf.

**OPEN DECISION B4.2 — dictionary dispatch cost:** should specialization monomorphize known
dictionaries, or is one hidden dictionary pointer and indirect slot calls acceptable? This is a
runtime/code-size decision and should not be folded into inference semantics. Stage 0 needs both a
compile-cost target and a runtime budget.

### B.5 Running the document directly

Direct execution is possible because `repr` is not constrained to `str` or even to inert data.
For example, a third tag could select a component program:

```yu
# ILLUSTRATIVE ONLY
interpreter browser for Yumark:
    repr = () -> [dom] component
    # algebra operations compose executable component builders

my page = build_page()
my mounted: [dom] component = (page @browser)()
```

The same `page` can still be opened as `html_node` or `str` if its capability row includes those
tags. This is more than an implicit call to `render_markdown_doc`: the document is a polymorphic
program, and selection chooses what its operations *mean*. A backend may evaluate, mount, analyze,
or render.

An explicit-value form could coexist:

```yu
my preview = run_with page preview_html_dictionary
```

That form avoids global-table selection and permits configured interpreters. The default shorthand
`page @html` would remain the flat `(family, tag)` lookup path.

**OPEN DECISION B5.1 — selection syntax and defaults:** should a tag always be explicit, be inferred
from an expected representation when exact-one selection is possible, or have a family default?
Expected-type selection is ergonomic but can turn result-type constraints into evidence search.
An explicit tag gives the clearest constant-cost rule. A default makes "run this directly" concise
but introduces ambient behavior.

**OPEN DECISION B5.2 — `repr` as computation:** should `repr` itself be allowed to contain an
effectful function/computation as above, or should effects be a separate parameter on the
interpreter/final program? Both can express execution, but their effect inference and ergonomics
differ. This sketch intentionally does not choose.

### B.6 Plausible effect on the 179 facts and pervasive recomputation

The proposal could plausibly remove the characterized burst for a specific structural reason.
Today every solved node role brings an associated `repr` argument, and the completed recursive
evidence tree publishes those equalities together as invariant type constraints. In the leading
sketch, all operations in one execution are checked against one rigid representation supplied by
the root dictionary. `Repr(Family, Tag)` is selected once, not rediscovered for each node.

**PROPOSED CHOICE B5:** keep tag-row membership/meet facts in a dedicated solver domain and publish
at most the run boundary's selected result constraint into the ordinary `ConstraintMachine`. Do
not encode every tag-row entry as an invariant `Neu` argument that compact merge expands into
ordinary upper and lower facts.

Under that choice, the particular batch of 179 new upper-bound facts has no producer: there is no
72-node associated-type resolution tree to flatten. The resulting 79.7% variable-summary and 100%
dominance-interval recomputation should therefore not be triggered *by format dispatch*.

This is a plausibility claim, not a performance guarantee. Three costs can remain:

- retaining the full nested `Shape` parameter can still make ordinary compact collection large;
- open tag-row variables and meets can create their own generalization work; and
- opening a `Final` may add ordinary result/effect constraints and still legitimately restart the
  generalization loop.

**OPEN DECISION B6.1 — solver isolation:** should tag-row constraints have an entirely separate
worklist and epoch, or integrate into the ordinary constraint machine with a distinct entry kind?
Full isolation gives the strongest defense against dominance invalidation but duplicates lifecycle
machinery. Integration is smaller but must demonstrate that tag membership changes do not dirty
unrelated ordinary type summaries.

### B.7 Likely compiler touch points

This list is an architectural sketch, not an implementation plan.

- `crates/poly/src/types.rs` would need serializable final-family/tag-row terms or side tables in
  schemes, plus quantifiers if open tag rows are allowed. They should be distinct from the existing
  effect `Pos::Row` / `Neg::Row` nodes.
- `crates/infer/src/annotation/constraints.rs` would lower family, tag-row, and `Final` annotations.
  It must not route them through effect-row subtraction or closed-effect-row caches.
- A focused new area such as `crates/infer/src/interpretation/` would own
  `InterpreterTable`, declaration coherence, exact lookup, dictionary schemes, and lookup metrics.
  This is the analogue of `casts.rs`, not an extension of `roles.rs`.
- A separate `crates/infer/src/tag_rows/` (or equivalently explicit, non-`utils` module name) would
  own membership, meet/join, row variables, normalization, and diagnostics. Whether it has its own
  worklist is Decision B6.1.
- `crates/infer/src/compact/collect/`, `compact/merge/entries.rs`, `compact/finalize.rs`, and
  `generalize/core/free_vars.rs` / instantiation would need explicit integration only if tag rows
  survive in inferred schemes. Reusing effect-row branches here would be a design error unless a
  later proof establishes identical semantics.
- `crates/infer/src/lowering/` would need declaration lowering for interpretation families and
  interpreters, plus introduction/elimination lowering for `Final` and `run`. If the surface is a
  builtin operation rather than syntax, `builtin_ops.rs` and `lowering/builtin_op.rs` are likely
  entry points.
- `crates/infer/src/analysis/session/generalize.rs` would need to observe whether exact selection
  adds a genuinely new result/effect constraint and restart when it does, just as cast does. It
  should not call recursive role resolution for final programs. A tag lookup/cache fingerprint
  must also participate in existing session/cache invalidation.
- `crates/infer/src/module_table/`, `compiled_typed.rs`, and compiled-unit dependency data would
  need to transport family/tag identities, validated dictionaries, and the generations or
  fingerprints actually consulted by a file SCC.
- `crates/infer/src/role_solve/` should not gain Yumark/tag-specific fast paths. Ordinary roles keep
  their current semantics; migrating Yumark simply stops generating `YumarkRender` demands.

Outside `crates/infer`, parser/syntax ownership, specialization/monomorphization, VM/native closure
ABI, and stdlib migration would also be affected. That breadth is part of the risk estimate below.

**OPEN DECISION B7.1 — generic facility versus Yumark-only experiment:** should Stage 0 model a
general interpretation-family declaration immediately, or hard-code an internal experimental
family ID without user-visible semantics? A general surface is the goal; an internal experiment is
safer for measuring whether the cost model works before committing to syntax.

### B.8 Rank-1 staging variant

The lower-risk variant keeps the same family signature, tag identities, representation mapping,
and exact table, but does not package the builder as `Final`. A document remains a let-generalized
function:

```yu
my greeting alg = alg.cons (alg.text "hello") alg.nil

my html = greeting html_yumark
my markdown = greeting markdown_yumark
```

This already removes all Yumark roles and associated equalities from the example. It also provides
a precise oracle for the eventual `Final` elaboration. It cannot be stored and later instantiated
at multiple representations, so it satisfies only the weak reading of Decision 0.

**PROPOSED CHOICE B6:** make this rank-1 form the first Stage-0 executable characterization, not
automatically the first shipped language surface.

**OPEN DECISION B8.1 — acceptable intermediate semantics:** if this form meets the measured cost
target, is it acceptable as a documented limitation for one release, or would that compromise the
user's reason for introducing a primitive in the first place?

## C. Consolidated open-decision register

The detailed sections above contain the reasoning. This register is a stop checklist: implementation
should not begin while the decisions that affect core representation remain unanswered.

| ID | User decision required | Why it changes the design |
|---|---|---|
| 0 / A4.1 | Let-generalized builder only, or first-class multi-run `Final`? | Determines whether controlled rank-2 storage is required. |
| A1.1 | Compiler-enforced representation parametricity, or ordinary algebra typing? | Determines what "Final" guarantees and how escape checking works. |
| A1.2 / B5.1 | Explicit `run_with`, explicit tag shorthand, expected-type selection, or default tag? | Changes evidence selection from direct syntax to possible inference search/ambient behavior. |
| A2.1 | Row stores `tag => repr`, or membership plus family-level `Repr(F, tag)`? | Directly affects whether invariant representation equalities multiply per node. |
| A2.2 | Closed rows, open tails, or a staged closed-first model? | Controls extensibility, quantification, and solver complexity. |
| A2.3 | Exact lattice/subtyping polarity for capabilities? | Needed for principal composition and safe subsumption. |
| A4.2 / B2.2 | Preserve nested document shape as a phantom, or erase it? | Trades migration/static information against type size and classic final form. |
| A4.3 | Closed family algebra, operation rows, or versioned algebra? | Chooses the node-extension/backend-extension tradeoff. |
| A4.4 / B1.2 | One coherent default per key, visible-scope uniqueness, or explicit dictionaries only? | Determines whether table lookup is exact and how configurable interpreters work. |
| A4.5 / B3.2 / B5.2 | How do construction, interpretation, and representation effects appear? | Needed for inert construction, value restriction, and direct execution. |
| A4.6 / B4.1 | When is an empty/unsupported capability intersection rejected? | Changes principality and diagnostic locality. |
| B1.1 | Closed constructor-headed `repr` in v0, or generic representation schemes? | Generic matching can weaken the flat-lookup cost guarantee. |
| B3.1 | Explicit reusable `Final` syntax, or compiler-internal packaging behind combinators? | Controls generality, teachability, and surface commitment. |
| B3.3 | Fully parametric injection, or finite per-tag native thunks? | Determines whether existing injection behavior survives and how honestly "final" applies. |
| B4.2 | Indirect dictionary slots or specialization to direct calls? | Runtime/code-size tradeoff, independent of inference correctness. |
| B6.1 | Separate tag-row solver/worklist or distinct entries in the main machine? | Determines invalidation boundaries and the risk of recreating pervasive recompute. |
| B7.1 / A5.1 | Internal Stage-0 experiment, rank-1 user surface first, or full facility before shipping? | Controls evidence quality versus premature surface commitment. |

The leading sketch assumes, only for purposes of estimating cost: explicit tag selection, one
coherent default dictionary per closed `(family, tag)` key, family-level `Repr`, and a dedicated
tag-row domain. Those are **working assumptions, not decisions**.

## D. Size, risk, and Stage-0 characterization

### D.1 Honest size/risk estimate

**Leading Candidate 3: size XL, risk very high.** The flat table itself is small. The risk comes
from making a controlled higher-rank program a first-class value inside an HM language and carrying
it across inference, compiled-unit serialization, specialization, and runtime boundaries.

A rough decomposition is:

| Slice | Rough size | Risk | Main uncertainty |
|---|---:|---:|---|
| Explicit algebra-record semantic PoC | S-M | medium | Effects, injection, and actual Yumark ergonomics |
| Family/tag IDs and flat coherent table | M | medium | Visibility, cache fingerprints, generic `repr` temptation |
| Closed tag-capability lattice | M-L | high | Polarity, principality, diagnostic timing |
| Open tag rows and quantification, if chosen | L | high | Generalization/restart behavior and row lacks |
| First-class `Final` intro/elim | L-XL | very high | Sound controlled rank 2, escape/value restriction |
| Specialization and runtime dictionary ABI | M-L | high | Allocation, code size, VM/native parity |
| Yumark migration and parity corpus | M-L | high | Injection, effects, static incompatibility diagnostics |

The lower-risk rank-1 staging variant is roughly M-L / medium-high if it includes a real family/tag
table and row surface, or S-M / medium as an explicit-record PoC only. The exact node/tag-table
fallback is roughly M-L / high: it is smaller than `Final` but does not meet the full semantic goal.

### D.2 Stage 0: characterize before choosing syntax or implementation

**PROPOSED CHOICE D1:** Stage 0 should have no production semantic change and should not begin by
adding row nodes to `poly::types`. It should first establish whether the term encoding and cost
model work, then make the unresolved choices above explicit for user review.

#### Stage 0A — semantic oracle using existing language features

Build a minimal Yumark vocabulary as explicit algebra records/functions in an isolated PoC. It
should demonstrate:

1. one let-bound document applied to HTML (`html_node`) and Markdown (`str`) algebras;
2. a third interpreter whose representation is executable or effectful, demonstrating that direct
   interpretation is not synonymous with string rendering;
3. construction inertness and interpretation-time effects;
4. nested cons/unary composition matching the representative 72-node shape;
5. the exact boundary where passing/storing the builder loses polymorphism under current HM; and
6. both injection alternatives from Decision B3.3.

This pass should record inferred public types and failure diagnostics by hand, not adjust expected
types to whatever the prototype happens to infer.

#### Stage 0B — type-rule characterization on paper

Before compiler work, write candidate introduction/elimination and lattice rules for:

- `Final<F, Shape, R>` and rigid representation escape;
- `Member<Tag, R>`, meet, join, top, bottom, and subsumption;
- family-level `Repr(F, Tag)` coherence and exact-one selection;
- closed versus open rows and generalization;
- effect/value-restriction interaction; and
- separate explicit dictionaries versus coherent default lookup.

The rules should be tested against rename/module-move cases, two dictionaries with the same tag,
an unsupported leaf, empty capability intersection, a generic fragment, and a `Final` stored in a
record and passed through a function. Failure to derive a principal type is a design blocker, not a
reason to insert `Any`; unresolved information remains `Unknown` or a proper tag-row variable.

#### Stage 0C — cost-model simulator or internal shadow characterization

Model the characterized document without changing production semantics and count separately:

- structural tag-row meet inputs;
- tag-row solver mutations and ordinary type-machine mutations;
- exact interpreter-table lookups and bucket lengths;
- role demands/candidate scans attributable to the experimental path;
- ordinary upper/lower facts published at `run`;
- generalization iterations and restart reasons;
- variable-summary and dominance-interval recomputation; and
- compact/type size with and without the phantom `Shape` parameter.

The target is not "somewhat less than 2,272." The proposed architecture predicts zero Yumark role
candidate scans during document construction/generalization and one exact interpreter lookup per
run site. It also predicts no per-node `repr` equality batch. Stage 0 should reject that prediction
if instrumentation shows tag-row composition merely republishes equivalent facts through the main
constraint machine.

#### Stage 0D — runtime and compilation validation

Compare at least the established expensive Markdown root, HTML, repository-std-only, showcase, a
small non-role control, and a format-incompatible Yumark document. Record cold compile time, role
phase time, tag-row time, generalization restarts, candidate scans, published fact counts, internal
total, external wall time, and peak RSS. For executable interpreters, also record dictionary-call
overhead, closure allocation, specialized code size, and VM/native parity.

**OPEN DECISION D2 — quantitative gates:** the user needs to approve exact Stage-0 go/no-go
thresholds. A reasonable starting hypothesis is that the experimental route must remove all 2,272
Yumark candidate scans and the 179-fact format-dispatch batch, while not regressing small controls.
The desired reduction in 79.7%/100% recomputation and end-to-end compile time should be chosen only
after the shadow prototype reveals irreducible shape/generalization costs.

### D.3 Stop conditions before implementation commitment

Pause and return to the designer if any of the following occurs:

- "first-class `Final`" cannot be specified without silently enabling general impredicative or
  arbitrary rank-2 inference;
- family/tag representation coherence requires general role candidate search;
- open tag-row inference produces ordinary invariant facts or pervasive invalidation proportional
  to document nodes;
- static rejection of a format-incompatible leaf cannot be retained without rebuilding a recursive
  evidence tree;
- injection timing or backend-native representation requires construction-time effects;
- the only viable mechanism is an initial-tree visitor dressed in `run` syntax, contrary to the
  genuine tagless-final goal;
- retaining typed `Shape` leaves the measured generalization cost substantially unchanged; or
- the explicit rank-1 semantic oracle cannot express the actual Yumark vocabulary cleanly.

### D.4 Suggested decision sequence

**PROPOSED CHOICE D3:** ask the designer to decide in this order, because later choices depend on
earlier ones:

1. strong versus weak meaning of first-class document value (Decision 0);
2. family-level representation coherence versus representation-carrying rows (A2.1);
3. preserve or erase typed shape (A4.2);
4. closed-first versus open tag rows (A2.2);
5. injection and effect semantics (B3.2/B3.3); then
6. surface notation, defaults, and specialization policy.

This sketch's leading starting point is therefore not "add another row." It is: validate an
algebra-parametric Yumark term first; if the strong document-value requirement stands, package that
term behind a narrowly scoped `Final` primitive; track supported interpreter tags in a dedicated
capability lattice; and select one coherent family/tag dictionary through a flat exact lookup only
when the document is run. That architecture directly attacks both measured amplifiers—the 2,272
candidate scans and the per-node associated-`repr` publication—while leaving the genuinely novel
higher-rank and row-design choices visible for user approval.
