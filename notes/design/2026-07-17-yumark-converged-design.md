# Yumark redesign: converged flat-role algebra-passing design

Date: 2026-07-17

Status: **converged pre-implementation direction, not an implementation specification**. This
document consolidates the investigation recorded in
`2026-07-16-generalize-role-resolve-snapshot-spec.md`,
`2026-07-17-yumark-primitive-format-dispatch-sketch.md`, the corrected Stage 0A fixture, and the
2026-07-17 record/capability/flat-role experiments. It replaces the earlier sketch's candidate
ranking for future Yumark redesign work: Candidates 2, 3, and 4 are no longer competing target
architectures, and Candidate 1 contributes only its ordinary rank-1 algebra-passing core, not its
proposed tag-row type-system extension. The earlier sketch remains unchanged as the historical
record of the explored alternatives.

The currently implemented value model and its original rationale remain documented by the signed
`2026-07-08-yumark-value-model-tagless-final.md`. This note proposes how to replace that model; it
does not claim that `lib/std/text/yumark.yu` has already migrated. Surface syntax, injection,
effects, and migration details identified below remain deliberately open.

This document uses the same labels as the first sketch:

- **ESTABLISHED FACT** records a result already established by today's investigation. It is an
  input, not a hypothesis re-derived here.
- **PROPOSED CHOICE** records the converged architectural direction for the next validation and
  implementation stages.
- **OPEN DECISION** records a genuine remaining design choice. The core direction does not silently
  settle it.

## 1. Executive decision

**PROPOSED CHOICE — converged architecture:** represent a Yumark document as an ordinary
let-generalized function which consumes a `yumark_algebra 'repr` and produces `'repr`. Document
construction is therefore genuine tagless-final algebra passing. It does not first construct a
typed `cons_cell` / `doc_leaf` tree and does not ask a role solver to interpret that tree later.

Format selection and format support are separate, small responsibilities:

1. `YumarkFormat Format` is an ordinary role implemented directly by ordinary marker types such as
   `html_format` and `markdown_format`. Its associated `repr` maps one format to its representation,
   and its method supplies the corresponding algebra. This role is resolved once when a document
   is selected for a format. Its implementations have no role prerequisites.
2. `SupportsFormat Capability Format` is another ordinary role. Direct implementations state that
   one ordinary capability marker supports one ordinary format marker. A document fragment carries
   such requirements as ordinary rank-1 role predicates over the single selected format. Combining
   fragments conjoins those predicates; it does not construct or infer a first-class set of tags.
3. A final selection such as HTML instantiates the document builder once at `html_format` and the
   HTML representation. All accumulated pointwise support predicates must resolve at that site.
   The selected algebra is then passed through the whole builder.

In compact form:

```text
source Yumark
    -> let-generalized builder
       forall repr, format.
       pointwise SupportsFormat(Ci, format) predicates
       => format -> yumark_algebra repr -> repr

select(builder, html_format)
    -> resolve YumarkFormat(html_format) once
    -> check each accumulated SupportsFormat(Ci, html_format) directly
    -> obtain repr = html_node and one html algebra
    -> execute builder with that algebra
```

There is no role whose receiver is `cons_cell Head Tail`, `doc_leaf Children`, or any other
recursive document shape. There is no per-node associated `repr`, no recursively assembled
interpreter-evidence tree, and no generic record-intersection operation.

**ESTABLISHED FACT — Decision 0 resolved weakly:** ordinary let-generalized rank-1 polymorphism is
sufficient. A Yumark builder need not be stored as a first-class value that can later be opened
multiple times at different representations. A let-bound builder may be instantiated separately at
HTML and Markdown use sites, exactly as the corrected Stage 0A PoC demonstrates. Consequently this
design does not need a primitive `Final` package, controlled rank 2, impredicative fields, or a new
value-restriction rule for such a package.

**PROPOSED CHOICE — no new type-system feature:** implement the design with mechanisms Yulang
already has: ordinary nominal structs, functions and HM let-generalization, roles, associated types,
generic `where` predicates, and ordinary format marker types. Do not add a kind system, a tag-row or
tag-lattice type, reuse effect rows as capabilities, add controlled rank 2, add record-row
intersection, or encode unresolved information as `Any`. `Unknown` remains the only unresolved
ordinary type placeholder.

## 2. Why this is the required boundary

### 2.1 The cost being removed

**ESTABLISHED FACT:** the expensive `proof` root in current Yumark has 28 binary `cons_cell`
applications and 15 unary containers. Their 71 recursive role prerequisites each scan the shared
32-candidate `YumarkRender` bucket, producing `71 * 32 = 2,272` candidate scans for the characterized
root. The completed 72-node resolution tree publishes 179 new, non-subsumed associated-`repr`
upper-bound facts in one batch. That publication causes the following generalization iteration to
recompute 79.7% of variable summaries and 100% of dominance intervals. The diagnosis and iteration
sequence are recorded in `2026-07-16-generalize-role-resolve-snapshot-spec.md` sections 2.1-2.2 and
summarized in `2026-07-17-yumark-primitive-format-dispatch-sketch.md` section 0.

The important unit is not simply “a role.” It is a broad role bucket plus recursive prerequisite
resolution over every document node plus one associated equality per solved node. Optimizing one
of those three amplifiers while retaining the other two would leave the architecture exposed to the
same scaling shape.

### 2.2 What the corrected Stage 0A PoC proved

**ESTABLISHED FACT:** `tests/yulang/regressions/cache/yumark_algebra_final_poc.yu`, corrected in
commit `6c27153c` after the tuple-versus-curried authoring error in `34ad6e6d`, matches the
characterized root structurally: 28 `cons` operations, 15 unary wrappers, 72 algebra operations, and
71 representation-typed structural edges. Its public builder type is the clean
`forall 'a. yumark_algebra 'a -> 'a`. The same let-bound builder specializes into independent
`html_node` and `str` mono instances, and `run-mono-std` succeeds.

The corrected three-sample medians recorded by `6c27153c` were:

| Workload | Prerequisite role scans | `generalize_resolve_roles` | `quantify_generalize` |
| --- | ---: | ---: | ---: |
| Algebra-passing PoC | 0 | 6.7 ms | 434.2 ms |
| Role-based Yumark workload | 2,336 | 2.061 s | 4.838 s |
| Repository std only | 0 | 6.8 ms | 203.9 ms |

The 2,336 counter is the full measured role-workload value; the 2,272 figure is the precisely
localized `71 * 32` contribution of the characterized `proof` tree. The algebra route eliminates
both: it adds zero top-level and zero prerequisite scans above the std-only baseline. It also has no
per-node associated-`repr` role tree capable of publishing the characterized 179-fact batch.

Absolute `quantify_generalize` time fell by 91.025% (`4.838 s -> 434.2 ms`), or 95.030% after
subtracting the 203.9 ms std-only baseline. `generalize_resolve_roles` fell by 99.675%. A separate
no-cache runtime-phase run reproduced the direction: median `build_poly / run.total /
generalize-role` was `1.718 s / 1.851 s / 7.5 ms` for algebra passing versus
`5.302 s / 5.555 s / 1.926 s` for role-based Yumark.

This proves the rank-1 construction core at the relevant 72-node/71-edge scale. It does **not** yet
prove the full design in this note: that PoC used only five toy algebra operations and did not
combine the flat format role with pointwise capability predicates.

### 2.3 What the remaining 2026-07-17 experiments ruled in and out

**ESTABLISHED FACT — flat roles are cheap in the measured shape:** an ordinary role with an
associated `repr`, implemented directly for two plain marker types and with no recursive
prerequisites, resolved in a median of approximately 304.5 microseconds in today's microbenchmark.
It published four new associated-equality facts, not 179. This is evidence that the existing
role/associated-type machinery is suitable for one flat format-selection boundary. It is not
evidence that an arbitrarily larger role workload is free: the benchmark had two marker
implementations and a trivial two-operation consumer, not the complete Yumark algebra plus
capability checks.

**ESTABLISHED FACT — pointwise predicates are sufficient:** the desired “intersection” behavior
does not require a first-class capability set. For a single selected tag `F`, a composition is
usable exactly when every participating fragment's ordinary predicate
`SupportsFormat Capability_i F` is satisfiable. This logical conjunction is the pointwise
intersection of their support. No term-level set value or type-level meet has to be constructed.

**ESTABLISHED FACT — records are not the generic solution:** anonymous records have structural
width subtyping, including end-to-end runtime success, and thunked fields behave normally. Yulang
does not have a term-level operation that constructs the automatic field intersection of two
arbitrary input records, however. That missing operation is exactly what a generic record-based
`cons` would need to combine HTML-only, Markdown-only, and both-format fragments. A direct
`{html}` / `{html, markdown}` specialization also exposed a current mono bug: the poly/infer join
succeeds, but `dump-mono-std` reports “conflicting type candidates.” Nominal nested structs do not
provide the same width behavior, and anonymous record types such as `{html: () -> int}` cannot
currently be written as surface type annotations. The converged design therefore does not depend
on record rows, record intersection, or fixing these record issues first.

**ESTABLISHED FACT — there is no reusable hidden tag-set feature:** Yulang has no existing kind
system or closed type-level tag set with subset subtyping. Effect rows are the nearest algebraic
precedent, but remain coupled to effect subtraction, stack weights, and handler hygiene. Reusing
them for Yumark format capabilities would not be a small library design.

## 3. Architectural invariants

The following are not notation preferences. They are the boundaries which keep the new design from
recreating the old cost.

1. **Document structure is term composition.** `cons`, `paragraph`, `heading`, `list_block`, and
   other constructors call slots on one supplied algebra. They do not allocate a typed initial tree
   whose shape later becomes a role receiver.
2. **One representation variable flows through one run.** Every nested operation in a builder uses
   the same `'repr` selected by its `yumark_algebra 'repr` argument.
3. **Format mapping is flat.** `YumarkFormat html_format` and
   `YumarkFormat markdown_format` are direct implementations with no `where` prerequisites. The
   associated representation is selected once per format-selection site, never once per node.
4. **Capability checks are flat and pointwise.** A support implementation relates one concrete
   capability marker to one concrete format marker. A support implementation must not recursively
   ask whether children, a `cons_cell`, or a document AST support that format.
5. **Composition accumulates predicates, not proof trees.** Generic composition may retain multiple
   independent `SupportsFormat Ci F` predicates, but it must not manufacture a nested
   `CombinedCapability Left Right` whose own `SupportsFormat` implementation recursively resolves
   `Left` and `Right`.
6. **No per-node associated representation.** Only `YumarkFormat` owns `repr`. `SupportsFormat`
   should be a marker predicate without an associated representation.
7. **No name-based inference.** Marker names resolve through ordinary symbols and role
   implementations. No inference branch tests strings such as `"html"`, `"markdown"`, `"cons"`,
   or a fixture path.
8. **Construction remains inert.** Merely defining or composing a builder does not interpret it or
   force injected work. Interpretation-time effects and injection remain ordinary explicit
   concerns, subject to the open decisions in section 8.

The critical prohibited form is:

```text
impl CombinedCapability<Left, Right>: SupportsFormat<Format>
    where Left: SupportsFormat<Format>
    where Right: SupportsFormat<Format>
```

If every `cons` creates another `CombinedCapability`, selecting a format asks the role solver to
walk a document-shaped prerequisite tree again. A smaller candidate bucket could reduce the
constant while preserving the original pathology. This design instead leaves the conjunction as
flat predicates on the ordinary builder/composition boundary.

## 4. Concrete Yumark vocabulary under algebra passing

### 4.1 The algebra

The following is realistic pseudocode in current Yulang style. It deliberately uses a nominal
struct rather than an anonymous record, and all operation names and payloads correspond to the
current `lib/std/text/yumark.yu`. Exact field syntax and effect annotations remain open.

```yu
pub struct yumark_algebra 'repr {
    nil: () -> 'repr,
    cons: 'repr -> 'repr -> 'repr,

    doc: 'repr -> 'repr,
    text: str -> 'repr,
    paragraph: 'repr -> 'repr,
    heading: str -> int -> 'repr -> 'repr,
    blank_line: str -> 'repr,
    section_close: str -> 'repr -> 'repr,
    list_block: bool -> 'repr -> 'repr,
    list_item: str -> 'repr -> 'repr,
    list_item_body: 'repr -> 'repr,
    code_fence: str -> str -> 'repr,
    quote_block: 'repr -> 'repr,
    emphasis: 'repr -> 'repr,
    strong: 'repr -> 'repr,
}
```

`nil` remains thunked, as in the validated Stage 0A algebra, so constructing the dictionary does
not eagerly manufacture a backend value. The other slots are ordinary functions. If interpretation
effects are admitted, those function types acquire ordinary Yulang effect rows; no custom Yumark
effect or capability-row mechanism is implied.

The old-to-new vocabulary correspondence is direct:

| Current typed-tree vocabulary | Algebra-passing vocabulary | Payload retained |
| --- | --- | --- |
| `nil_cell` | `algebra.nil()` | none / marker no longer semantic |
| `cons_cell Head Tail` | `algebra.cons head_repr tail_repr` | ordered head and tail |
| `doc_leaf Children` | `algebra.doc children_repr` | children |
| `text_leaf` | `algebra.text value` | `value: str` |
| `paragraph_leaf Children` | `algebra.paragraph children_repr` | children |
| `heading_leaf Children` | `algebra.heading marker level children_repr` | `marker`, `level`, children |
| `blank_line_leaf` | `algebra.blank_line marker` | `marker` |
| `section_close_leaf Children` | `algebra.section_close marker children_repr` | `marker`, children |
| `list_block_leaf Items` | `algebra.list_block ordered items_repr` | `ordered`, items |
| `list_item_leaf Children` | `algebra.list_item marker children_repr` | `marker`, children |
| `list_item_body_leaf Children` | `algebra.list_item_body children_repr` | children |
| `code_fence_leaf` | `algebra.code_fence info body` | `info`, `body` |
| `quote_block_leaf Children` | `algebra.quote_block children_repr` | children |
| `emphasis_leaf Children` | `algebra.emphasis children_repr` | children |
| `strong_leaf Children` | `algebra.strong children_repr` | children |

`cons_cell` and the `*_leaf` names may remain as source-facing/lowering-facing combinator names if
that is ergonomically useful, but they no longer denote nested document-shape types. For example,
`paragraph` is a function that accepts a child builder and, when supplied an algebra, calls
`algebra.paragraph` on the child's result.

### 4.2 Builder combinators

The semantic shape of the ordinary combinators is:

```yu
# Illustrative current-feature pseudocode; exact argument order is unsettled.
pub nil(format: 'format, algebra: yumark_algebra 'repr): 'repr =
    algebra.nil()

pub text(value: str, format: 'format, algebra: yumark_algebra 'repr): 'repr =
    algebra.text(value)

pub cons(head, tail, format: 'format, algebra: yumark_algebra 'repr): 'repr =
    algebra.cons(
        head(format, algebra),
        tail(format, algebra),
    )

pub paragraph(children, format: 'format, algebra: yumark_algebra 'repr): 'repr =
    algebra.paragraph(children(format, algebra))

pub heading(marker: str, level: int, children,
            format: 'format, algebra: yumark_algebra 'repr): 'repr =
    algebra.heading(marker)(level)(children(format, algebra))

pub list_block(ordered: bool, items,
               format: 'format, algebra: yumark_algebra 'repr): 'repr =
    algebra.list_block(ordered)(items(format, algebra))

pub quote_block(children, format: 'format,
                algebra: yumark_algebra 'repr): 'repr =
    algebra.quote_block(children(format, algebra))

pub emphasis(children, format: 'format,
             algebra: yumark_algebra 'repr): 'repr =
    algebra.emphasis(children(format, algebra))

pub strong(children, format: 'format,
           algebra: yumark_algebra 'repr): 'repr =
    algebra.strong(children(format, algebra))
```

`doc`, `blank_line`, `section_close`, `list_item`, `list_item_body`, and `code_fence` follow the
same pattern. The extra `format` argument carries only the single tag against which pointwise
capability predicates are stated. It does not control operation dispatch inside the builder; the
algebra value does that.

A representative real-vocabulary builder then has the following shape:

```yu
my article(format: 'format, algebra: yumark_algebra 'repr): 'repr =
    doc(
        cons(
            heading("# ", 1, cons(text("Yumark"), nil())),
            cons(
                paragraph(cons(
                    text("A paragraph with "),
                    cons(emphasis(cons(text("emphasis"), nil())),
                    cons(text(" and "),
                    cons(strong(cons(text("strong"), nil())), nil()))),
                )),
                cons(
                    list_block(false, cons(
                        list_item("- ", list_item_body(
                            cons(text("an item"), nil())
                        )),
                        nil(),
                    )),
                    cons(
                        code_fence("text", "body"),
                        cons(quote_block(cons(text("quoted"), nil())), nil()),
                    ),
                ),
            ),
        ),
        format,
        algebra,
    )
```

This snippet is intentionally notation-level rather than claimed compilable source: current
Yulang currying/partial-application spelling and the eventual lowering-friendly constructor
surface still need the fuller PoC. Semantically, every nested call receives the same `format` and
the same `yumark_algebra 'repr`; no intermediate `cons_cell` or leaf value is produced.

### 4.3 HTML and Markdown algebras

The two current sets of 16 `YumarkRender Node Format` implementations become two ordinary algebra
values. The existing method bodies transfer almost mechanically into slots:

```yu
my html_algebra(): yumark_algebra html_node = yumark_algebra {
    nil: html_nil,
    cons: html_fragment,
    doc: html_doc,
    text: html_text,
    paragraph: html_paragraph,
    heading: html_heading,
    blank_line: html_blank_line,
    section_close: html_section_close,
    list_block: html_list_block,
    list_item: html_list_item,
    list_item_body: html_list_item_body,
    code_fence: html_code_fence,
    quote_block: html_quote_block,
    emphasis: html_emphasis,
    strong: html_strong,
}

my markdown_algebra(): yumark_algebra str = yumark_algebra {
    nil: markdown_nil,
    cons: std::text::str::concat,
    doc: markdown_doc,
    text: markdown_text,
    paragraph: markdown_paragraph,
    heading: markdown_heading,
    blank_line: markdown_blank_line,
    section_close: markdown_section_close,
    list_block: markdown_list_block,
    list_item: markdown_list_item,
    list_item_body: markdown_list_item_body,
    code_fence: markdown_code_fence,
    quote_block: markdown_quote_block,
    emphasis: markdown_emphasis,
    strong: markdown_strong,
}
```

The HTML representation remains the structured `html_node { tag, body }`; Markdown remains `str`.
The algebra is closed over the current static vocabulary. Adding a format supplies one new algebra.
Adding a new node operation requires extending every algebra; whether that closed-world tradeoff is
accepted is an open decision in section 8.

## 5. Flat format mapping and selection

### 5.1 The only associated representation role

The representation mapping uses an ordinary role on the format marker itself:

```yu
# Illustrative spelling only.
pub role YumarkFormat 'format:
    type repr
    our format.yumark_algebra: () -> yumark_algebra repr

impl html_format: YumarkFormat:
    type repr = html_node
    our format.yumark_algebra _ = html_algebra()

impl markdown_format: YumarkFormat:
    type repr = str
    our format.yumark_algebra _ = markdown_algebra()
```

These are ordinary direct implementations. Neither has a `where` prerequisite. `repr` belongs to
the format mapping once; it is not repeated on `nil`, `cons`, `paragraph`, or any other document
operation.

Conceptually, selection is:

```yu
pub run_yumark(format: 'format, document): repr =
    where 'format: YumarkFormat
    document(format, format.yumark_algebra())
```

The exact surface spelling of the associated result in `run_yumark` is not settled. Current Yumark
already sometimes needs a typed command helper to pin an associated `repr`, so Stage 0B must prove
the cleanest existing-language spelling rather than inventing syntax. The semantic rule is settled:
resolve one concrete `YumarkFormat Format` role at the selection site, obtain one algebra and one
representation, and run the entire builder with them.

Convenience wrappers may remain:

```text
render_html_doc(document)     = run_yumark(html_format_value(), document)
render_markdown_doc(document) = run_yumark(markdown_format_value(), document)
```

Passing a let-generalized builder to either wrapper instantiates it once at that wrapper's concrete
format and representation. Calling both wrappers at two sites creates two ordinary rank-1
instantiations, as Stage 0A already demonstrated for the algebras directly. The wrapper does not
store a polymorphic builder for later multi-run use.

### 5.2 Flatness rule

`YumarkFormat` must remain proportional to the number of visible formats, not to the number of
document nodes. Adding more operations to `yumark_algebra` changes declaration-time conformance of
the two algebra values, but it must not add format-role prerequisites at a run site. Adding another
paragraph or `cons` to a document must not change the number of `YumarkFormat` resolutions or
associated representation facts produced by selecting that document once.

This is the exact role shape for which today's marker-type microbenchmark measured approximately
304.5 microseconds and four new associated-equality facts. Stage 0B must repeat the measurement with
the full algebra and the capability layer present; until then, “one flat lookup remains cheap at
full scale” is a strongly supported prediction, not a completed validation.

## 6. Pointwise capabilities and the worked mixing case

### 6.1 Direct support facts, not a type-level set

Capability profiles are ordinary nominal marker types. For a minimal HTML/Markdown universe:

```yu
pub struct html_only_capability { marker: str }
pub struct markdown_only_capability { marker: str }
pub struct html_markdown_capability { marker: str }

pub role SupportsFormat 'capability 'format:
    our capability.supports_format: 'format -> ()

impl html_only_capability: SupportsFormat html_format:
    our capability.supports_format _ = ()

impl markdown_only_capability: SupportsFormat markdown_format:
    our capability.supports_format _ = ()

impl html_markdown_capability: SupportsFormat html_format:
    our capability.supports_format _ = ()

impl html_markdown_capability: SupportsFormat markdown_format:
    our capability.supports_format _ = ()
```

The trivial method is only an evidence anchor if Yulang requires a role member; the type-level
meaning is the ordinary predicate. These four implementations are all direct. In particular, there
is no implementation for a cons-shaped capability and no implementation with a
`SupportsFormat` prerequisite.

This marker vocabulary can represent named support profiles, product policy, or the support of a
format-specific extension. It is not a kind and does not contain a set value. “Both” above means
exactly the two direct facts that were declared. It does not automatically mean every future
format.

Representative fragments state their support as bounds on the one tag at which the fragment is
being instantiated:

```yu
# Illustrative spelling. The bodies use normal algebra operations so the example
# isolates capability typing rather than prematurely choosing an injection design.
my html_only_fragment(format: 'format,
                      algebra: yumark_algebra 'repr): 'repr =
    where html_only_capability: SupportsFormat 'format
    paragraph(cons(text("HTML-only fragment"), nil()), format, algebra)

my markdown_only_fragment(format: 'format,
                          algebra: yumark_algebra 'repr): 'repr =
    where markdown_only_capability: SupportsFormat 'format
    paragraph(cons(text("Markdown-only fragment"), nil()), format, algebra)

my both_fragment(format: 'format,
                 algebra: yumark_algebra 'repr): 'repr =
    where html_markdown_capability: SupportsFormat 'format
    paragraph(cons(strong(cons(text("shared fragment"), nil())), nil()),
              format,
              algebra)
```

The role bound is the authoritative support declaration. The example bodies intentionally do not
pretend that backend-native injection is solved; section 8 keeps that question open.

### 6.2 What `cons` means pointwise

At a single format `F`, `cons(left, right)` is runnable precisely when both child calls are
runnable with the same `F` and the same algebra. If `left` carries predicate
`SupportsFormat CL F` and `right` carries `SupportsFormat CR F`, ordinary inference retains their
conjunction:

```text
left  : F -> yumark_algebra R -> R
        requires SupportsFormat(CL, F)

right : F -> yumark_algebra R -> R
        requires SupportsFormat(CR, F)

cons(left, right)
      : F -> yumark_algebra R -> R
        requires SupportsFormat(CL, F)
             and SupportsFormat(CR, F)
```

Nothing computes `Intersection(CL, CR)`. The common-format behavior follows from asking whether
the same concrete `F` satisfies both ordinary predicates.

For example, an explicitly named composition can expose those flat bounds:

```yu
my html_and_both(format: 'format,
                 algebra: yumark_algebra 'repr): 'repr =
    where html_only_capability: SupportsFormat 'format
    where html_markdown_capability: SupportsFormat 'format
    cons(html_only_fragment, both_fragment, format, algebra)

my markdown_and_both(format: 'format,
                     algebra: yumark_algebra 'repr): 'repr =
    where markdown_only_capability: SupportsFormat 'format
    where html_markdown_capability: SupportsFormat 'format
    cons(markdown_only_fragment, both_fragment, format, algebra)
```

The conceptual generalized schemes are:

```text
forall F R.
  SupportsFormat(html_only_capability, F),
  SupportsFormat(html_markdown_capability, F)
  => F -> yumark_algebra R -> R

forall F R.
  SupportsFormat(markdown_only_capability, F),
  SupportsFormat(html_markdown_capability, F)
  => F -> yumark_algebra R -> R
```

Therefore:

- `render_html_doc(html_and_both)` succeeds. Both direct HTML facts exist.
- `render_markdown_doc(html_and_both)` fails to type-check at the Markdown selection/instantiation
  site because there is no
  `html_only_capability: SupportsFormat markdown_format` implementation.
- `render_markdown_doc(markdown_and_both)` succeeds. Both direct Markdown facts exist.
- `render_html_doc(markdown_and_both)` fails to type-check at the HTML selection/instantiation site
  because there is no
  `markdown_only_capability: SupportsFormat html_format` implementation.

The failure is compile-time role resolution triggered by specializing the let-bound builder at the
concrete format. No rendering begins and no runtime “missing field” branch is involved. The current
diagnostic may point into the instantiated call or unresolved role method until diagnostic
provenance is polished, but the semantic failure boundary is the final format-selection call.

### 6.3 Combining HTML-only, Markdown-only, and both

All three fragments can be composed as an ordinary generic builder:

```yu
my all_three(format: 'format,
             algebra: yumark_algebra 'repr): 'repr =
    where html_only_capability: SupportsFormat 'format
    where markdown_only_capability: SupportsFormat 'format
    where html_markdown_capability: SupportsFormat 'format
    cons(
        html_only_fragment,
        cons(markdown_only_fragment, both_fragment),
        format,
        algebra,
    )
```

Under use-site-only pointwise checking, defining `all_three` type-checks. Its generalized scheme
honestly retains three independent predicates. With only the two formats declared above, however,
it has no runnable format:

- `render_html_doc(all_three)` fails because
  `markdown_only_capability: SupportsFormat html_format` is unsatisfied.
- `render_markdown_doc(all_three)` fails because
  `html_only_capability: SupportsFormat markdown_format` is unsatisfied.

The conceptual diagnostic ownership is therefore:

```text
unresolved role: markdown_only_capability: SupportsFormat html_format
required while instantiating all_three at render_html_doc(all_three)
```

The final wording and source span remain diagnostics work; the missing direct fact and the
selection call which demands it are not ambiguous.

This is the exact analogue of an empty support-set intersection, expressed without constructing an
empty set. It is important not to overstate the diagnostic timing: generic `cons` cannot reject
`all_three` merely because no currently known tag satisfies all predicates. Such a rejection would
require an existential search over a closed format universe or a first-class set/intersection
feature, both deliberately absent from this design.

If earlier static rejection is required, the combination point must explicitly choose the tag:

```text
cons_for(html_format_value(), html_only_fragment, markdown_only_fragment)
```

`cons_for` checks both ordinary support bounds at `html_format`; this expression fails immediately
on the Markdown-only fragment. The corresponding Markdown selection fails immediately on the
HTML-only fragment. The result is a composition selected for one concrete format, not a reusable
generic builder.

**PROPOSED CHOICE — default validation target:** first validate compile-time rejection at the final
format-selection site, because it follows directly from existing role bounds and preserves the
current design's “unsupported format does not run” property without recursive evidence. An
explicit-tag combination helper may be added for users who want a nearer diagnostic.

**OPEN DECISION — rejection timing:** the user still needs to decide whether final-selection
compile-time failure is sufficient, whether important APIs should require an explicit format at
composition time for an earlier error, or whether some dynamic/later-checked fragment form is also
desired. Runtime fallback is not supplied automatically by the pointwise role design; it would be
a separate dynamic representation and error contract.

### 6.4 Why the capability role stays cheap

At selection, every retained support predicate is a direct query over a small ordinary role bucket.
The number of pointwise queries can grow with the number of distinct restricted fragments or
explicit support bounds, but the depth of every proof remains one. There is no 72-node evidence
tree and `SupportsFormat` publishes no associated representation equality.

This distinction must appear in measurements:

```text
acceptable:
    N independent SupportsFormat(Ci, html_format) checks
    each with zero recursive prerequisites

prohibited:
    one SupportsFormat(DocumentShape, html_format) check
    which recursively proves N child SupportsFormat prerequisites
```

The first may still need ordinary engineering if `N` becomes large, but it cannot recreate the
specific recursive associated-`repr` publication burst. The second is the original architecture
with renamed roles and must not be introduced.

## 7. Cost model and evidence-backed prediction

### 7.1 Work removed and work retained

For one document selected once at one format:

| Work | Current `YumarkRender Node Format` | Converged design |
| --- | ---: | ---: |
| Document representation during inference | Nested nominal type tree | Ordinary builder applications over one `'repr` |
| Format-dispatch role receiver | Every node shape | One concrete format marker |
| Recursive format-role prerequisite edges at the characterized root | 71 | 0 |
| Characterized root candidate scans | 2,272 (`71 * 32`) | 0 construction scans; one flat format-role selection |
| Full measured role-workload prerequisite scans | 2,336 | 0 in Stage 0A algebra route |
| Interpreter evidence | 72-node role-resolution tree | One algebra value threaded through the builder |
| Associated `repr` equalities from nodes | 179 new facts in one batch | None; `repr` belongs only to the selected format |
| Capability composition | Implicit in recursive node roles | Independent, depth-one `SupportsFormat` predicates |
| Runtime interpretation | Visits all operations | Still visits all operations; this work is semantic |

The design does not claim that building or rendering a 72-operation document becomes constant
time. It claims that compile-time *format discovery* no longer follows those 72 operations. The
ordinary function/type work of applying the algebra remains, and runtime interpretation must still
execute every operation.

### 7.2 Why the 179-fact burst has no producer

In current Yumark, every recursively solved node carries an associated `repr`. Flattening the
completed proof tree publishes equalities for those repeated associated projections. In the
converged design, the document is checked once as
`yumark_algebra 'repr -> 'repr`; all 71 structural edges already share the same ordinary type
variable. At selection, one `YumarkFormat Format` fact identifies that one variable with
`html_node` or `str`.

`SupportsFormat` has no associated type. It can succeed or remain unsatisfied, but cannot publish a
second representation equality. Therefore the specific per-node producer of the 179-fact batch is
absent. Other ordinary constraints and generalization restarts may still exist; the claim is not
that all generalization cost disappears.

### 7.3 Strength and limits of the current evidence

The evidence composes into a strong architectural case, but not yet into a full-system benchmark:

- The corrected Stage 0A fixture validates the full 72-operation/71-edge algebra-passing shape,
  clean rank-1 generalization, separate representations, mono specialization, execution, zero
  workload-attributable role scans, and the 91-95% / 99.675% phase improvements. It has only five
  algebra operations and no capability role.
- The flat-role microbenchmark validates an ordinary associated-type role over two format markers
  at about 304.5 microseconds median with four new equality facts. Its temporary test fixture was
  not committed, so Stage 0B must preserve a reproducible version. It does not contain the full
  Yumark vocabulary.
- The pointwise-capability investigation establishes that direct marker-pair facts express the
  required common-format rule without a type-level set. The full real-vocabulary builder, format
  mapping, and multiple accumulated support predicates have not yet been compiled and measured
  together.
- The record investigation establishes why record width subtyping cannot supply the missing
  generic intersection combinator and also found a mono specialization failure. The converged
  design avoids depending on that route; it does not fix the bug.

The missing combined measurement is the principal validation gap. It would be false confidence to
extrapolate the four-fact microbenchmark into a guaranteed full-vocabulary fact count without
building that combined fixture.

## 8. Genuine remaining open decisions

### 8.1 Surface vocabulary and notation

**OPEN DECISION:** the user still owns the public spelling. In particular:

- whether users see `yumark_algebra` explicitly or only generated/lowering-facing combinators;
- whether the format marker is the first or last builder argument;
- whether `render_html_doc` / `render_markdown_doc` remain the primary public API or a generic
  `run_yumark format document` is exposed;
- whether old names such as `doc_leaf` and `paragraph_leaf` survive as compatibility combinators;
  and
- how inferred support predicates are displayed in hover and diagnostics.

These choices do not change the semantic boundary, provided the result elaborates to an ordinary
rank-1 algebra-consuming builder and flat pointwise predicates.

### 8.2 Unsupported-format diagnostic timing

**OPEN DECISION:** section 6 proposes compile-time rejection when a generic builder is finally
selected, with optional explicit-format combination helpers for nearer errors. It remains the
user's call whether that is sufficient. Rejecting every empty common-format composition without an
explicit tag would require a closed-world existence check or a type-level support set, which is
outside the converged no-new-feature design. A runtime/later-checked form is possible only as a
separate dynamic API with an explicit error type and must not silently replace the static form.

### 8.3 Backend-native injection

**OPEN DECISION:** the new core does not yet explain how a fragment injects a value that is already
native to one backend, because such a value cannot be manufactured uniformly under abstract
`'repr`.

Two existing-feature directions remain honest:

1. make injection itself an algebra operation whose input is backend-neutral and let each algebra
   construct its native value; or
2. retain the current Candidate B idea: an ordinary nominal payload with one monomorphic thunk per
   supported format, selected only during interpretation.

The second preserves the previously established inert construction and genuinely backend-native
results, but is finite and format-indexed: adding a format changes the payload shape. Anonymous
record width subtyping does not make arbitrary payload intersections compositional, and rank-1 HM
does not permit storing one multi-representation polymorphic thunk as ordinary data. The fuller PoC
must try realistic injection before migration chooses either direction. If injection requires
controlled rank 2 after all, that is a stop condition and a separate language project, not license
to grow this design back into Candidate 3.

### 8.4 Interpretation effects

**OPEN DECISION:** the current role methods return effect-polymorphic computations, while the
validated Stage 0A algebra is pure. The full design still needs to establish:

- how a common interpretation effect row appears in `yumark_algebra` function fields;
- whether different algebra slots may carry different effects without requiring polymorphic fields;
- that constructing/composing a builder is inert and effects fire only when the selected algebra is
  executed;
- that an executable representation, rather than only `html_node` or `str`, specializes cleanly;
  and
- VM/native parity and specialization behavior for effectful function fields.

Effects remain ordinary Yulang effects. They must not be encoded in `SupportsFormat` or a revived
tag row.

### 8.5 Closed algebra and extension policy

**OPEN DECISION:** the nominal algebra shown here is closed over the current static vocabulary.
Adding a format is cheap and local: define a marker, a flat `YumarkFormat` implementation, and one
algebra value. Adding a node operation changes the algebra struct and every format algebra. The
current per-node role design was open in both dimensions, albeit at the measured cost.

The user needs to choose whether the smaller closed algebra is the intended Yumark extension model,
whether algebras should be versioned, or whether extension nodes belong behind an explicit generic
escape operation. A row-polymorphic operation algebra would be another type-system project and is
not part of this proposal.

### 8.6 Interpreter identity and configuration

**OPEN DECISION:** one marker may identify one default format policy, or separate marker types may
identify configured policies such as strict HTML and preview HTML. The latter uses existing
mechanisms and keeps each `YumarkFormat` resolution coherent and flat. Whether a public
`run_with(document, explicit_algebra)` bypass should coexist with marker selection is an API choice,
not a reason to introduce a global primitive table.

### 8.7 Migration and compatibility

**OPEN DECISION:** `lib/std/text/yumark.yu` currently exposes concrete `cons_cell`, leaf structs,
`YumarkRender`, and render wrappers. Real lowering currently synthesizes that vocabulary for the
plain-text Yumark slice, while much of the richer static vocabulary is present in the stdlib but not
fully connected from lowering. Migration needs an explicit compatibility decision:

- switch lowering directly to algebra combinators and break old constructed-tree code;
- provide a temporary compatibility layer which preserves familiar constructor names but returns
  builders; or
- run old and new paths side by side until parity is demonstrated.

The temporary layer must not adapt a new builder by rebuilding the old recursive role tree, because
that would preserve the pathology at the compatibility boundary.

## 9. Updated size and risk

The original leading Candidate 3 was estimated **XL / very high risk** because it combined a new
tag-capability lattice, controlled first-class rank-2 `Final` introduction/elimination,
serialization and specialization rules, and a runtime dictionary ABI. Decision 0 and the pointwise
capability result remove all of those language-feature projects.

The updated estimate separates the settled core from unresolved product parity:

| Slice | Updated size | Updated risk | Main uncertainty |
| --- | ---: | ---: | --- |
| Reproducible full-vocabulary combined PoC | S-M | medium | Existing syntax, predicate accumulation, mono specialization |
| Nominal algebra plus HTML/Markdown values | M | medium | Ergonomics and closed-algebra maintenance |
| Flat `YumarkFormat` and pointwise support profiles | S-M | low-medium | Diagnostics and keeping all impls prerequisite-free |
| Lowering and public-API migration | M | medium | Compatibility and generated builder shape |
| Effectful interpretation validation | S-M | medium-high | Effect rows in stored function fields |
| Backend-native injection parity | M | medium-high | Parametric algebra operation versus finite per-tag thunks |
| Regression/performance/parity corpus | M | medium | Coverage across HTML, Markdown, negative support, VM/native |

**PROPOSED CHOICE — overall estimate:** the converged core is approximately **M / medium risk**.
A complete migration including effects, injection, compatibility, and parity is approximately
**M-L / medium-high risk**. That is materially smaller than XL / very high risk, but it is not yet a
small mechanical stdlib rewrite. Injection and effectful function fields are the two uncertainties
most capable of raising the migration risk.

No compiler type-system work is planned. If the next validation discovers that an essential public
requirement cannot be expressed with existing rank-1 functions and flat roles, the project should
stop and report that requirement rather than silently implementing a new kind, row, or rank-2
feature.

## 10. Recommended next validation: Stage 0B, then a shadow Stage 1

### 10.1 Stage 0B: one combined, reproducible existing-feature PoC

Before changing `lib/` or lowering, add one isolated fixture which combines every architectural
piece in this note:

1. Define the full nominal `yumark_algebra` with all current operations: `nil`, `cons`, `doc`,
   `text`, `paragraph`, `heading`, `blank_line`, `section_close`, `list_block`, `list_item`,
   `list_item_body`, `code_fence`, `quote_block`, `emphasis`, and `strong`.
2. Build a representative document with the actual static vocabulary and the same
   72-operation/71-edge scale as the corrected Stage 0A root, not five generic toy operations.
3. Define complete HTML (`html_node`) and Markdown (`str`) algebra values and select them through
   the flat `YumarkFormat` role, not by direct calls alone.
4. Include HTML-only, Markdown-only, and both-supporting fragments using direct pointwise
   `SupportsFormat` implementations. Preserve positive runs and negative compile fixtures for all
   cases in section 6.
5. Run `check-poly-std`, inspect the inferred public schemes, run `dump-mono-std`, and execute both
   representations. The mono steps are mandatory because today's record-width experiment and the
   first erroneous Stage 0A both show that poly success alone is insufficient evidence.
6. Measure at least three no-cache samples with the same analysis counters used by `6c27153c`:
   top-level/prerequisite role scans and matches, published upper bounds, generalization
   iterations/restarts, `generalize_resolve_roles`, `quantify_generalize`, infer, and total check.
   Retain repository-std-only and current role-based Yumark as controls.
7. Instrument role proof depth and associated-fact publication by role. Confirm that
   `YumarkFormat` resolutions are proportional only to format-selection sites, every
   `SupportsFormat` proof has depth one and zero prerequisites, and neither count grows because a
   paragraph or `cons` was added.
8. Add one construction-inert/effectful interpreter or representation and one realistic injection
   experiment. If both injection directions remain viable, record both rather than choosing from a
   toy case.

This is still a PoC and measurement stage. It should not change production semantics, add syntax,
or migrate `lib/std/text/yumark.yu`.

### 10.2 Stage 0B acceptance conditions

The combined PoC should meet these structural gates before any implementation plan is approved:

- public builders remain ordinary rank-1 schemes and specialize independently to `html_node` and
  `str`;
- construction/generalization performs no recursive `YumarkRender`-style document proof;
- format selection performs one depth-one mapping resolution per selection site;
- support checks are direct and prerequisite-free, with no document-shaped capability receiver;
- associated representation fact count is independent of document-node count and has no analogue
  of the 179-fact batch;
- positive support combinations execute and negative combinations fail at the documented selection
  or explicit-composition boundary;
- `dump-mono-std` and runtime execution succeed, not only poly inference; and
- the measured performance remains in the Stage 0A direction without a new pervasive
  generalization restart source.

Exact wall-time thresholds remain an **OPEN DECISION** for the user after the combined measurements
exist. The structural gates above are more important than selecting a favorable noisy timing run.

### 10.3 Shadow Stage 1 after Stage 0B

If Stage 0B passes, the next step should be a side-by-side lowering/stdlib prototype, still without
removing the current path:

- lower the currently supported plain-text Yumark slice into the new combinators behind an internal
  experiment boundary;
- compare HTML output, Markdown output where available, diagnostics, construction inertness, and
  phase counters against the current path;
- extend the shadow only far enough to cover the real static vocabulary and the chosen injection
  experiment; and
- return to the user with a concrete migration/API proposal before switching the public stdlib.

### 10.4 Stop conditions

Stop before production implementation if any of the following occurs:

- the full builder cannot retain clean rank-1 polymorphism through actual composition;
- generic selection requires first-class multi-run storage, controlled rank 2, a generic record
  intersection, or a new tag kind;
- `YumarkFormat` associated facts or capability proof depth grow with document-node count;
- pointwise predicates are internally converted into a recursive `CombinedCapability` proof;
- poly succeeds but mono specialization cannot keep HTML and Markdown instances separate;
- effectful algebra fields force construction-time effects or unsupported polymorphic storage;
- backend-native injection cannot preserve required typing and inertness with either existing-feature
  direction; or
- compile-cost measurements lose the Stage 0A advantage once the actual vocabulary and capability
  layer are combined.

## 11. Consolidated proposal

**PROPOSED CHOICE:** proceed with ordinary rank-1 algebra passing as Yumark's document
representation. Use one nominal algebra containing the real Yumark operation vocabulary. Implement
HTML and Markdown as ordinary values of that algebra at different representations. Map a concrete
format marker to its representation and algebra through one flat, non-recursive ordinary role with
an associated type, resolved only when a builder is selected.

Express fragment support through independent `SupportsFormat Capability Format` facts and check
them pointwise against the same concrete format. Let generic composition retain a conjunction of
flat predicates; never turn the document or its capability profile into a recursively resolved role
receiver. This gives the common-format behavior of capability intersection without a tag set,
record intersection, effect-row reuse, or new kind machinery.

The measured evidence supports each boundary separately: the corrected 72-operation algebra PoC
eliminated all workload-attributable role scans and reduced the relevant phases by 91-99.675%; the
flat marker-role experiment produced only four associated facts at microsecond-scale resolution;
and pointwise support facts express the required mixing rule. What remains unvalidated is their
combination at full real-vocabulary scale, plus injection and effects. Stage 0B must close that gap
before production migration begins.

## 12. Evidence trail

- `notes/design/2026-07-16-generalize-role-resolve-snapshot-spec.md`, especially sections 1 and
  2.1-2.3 — localized `proof` cost, 71 prerequisites, 2,272 scans, 179 facts, structural expansion,
  and generalization restarts.
- `notes/design/2026-07-17-yumark-primitive-format-dispatch-sketch.md` — historical candidate
  exploration, cost walkthrough, original XL / very-high-risk Candidate 3 estimate, and the Stage 0
  questions now narrowed by this note.
- `tests/yulang/regressions/cache/yumark_algebra_final_poc.yu` and commits `34ad6e6d` /
  `6c27153c` — rank-1 algebra-passing semantic/performance oracle, corrected currying, clean public
  type, separate mono instances, execution, counters, and timings.
- `notes/design/2026-07-08-yumark-value-model-tagless-final.md` — authoritative rationale and
  evidence for the currently implemented typed cons-chain, real static vocabulary, Candidate B
  injection, effect timing, and existing open lowering work.
- `lib/std/text/yumark.yu` — current concrete vocabulary and HTML/Markdown implementations from
  which section 4's algebra slots are derived.
- 2026-07-17 uncommitted characterization experiments — anonymous-record width/runtime behavior,
  missing generic record intersection, the mono record-join conflict, absence of reusable kind/tag
  machinery, direct pointwise support predicates, and the approximately 304.5-microsecond / four-fact
  flat-role measurement. Stage 0B must turn the relevant flat-role and capability cases into retained
  reproducible fixtures.

## 13. Shadow Stage 1 complete (2026-07-17): closeout and migration decision proposal

Shadow Stage 1 is complete as a validation project. It does **not** activate algebra-passing
lowering, change the public stdlib, authorize a compatibility policy, or close the separately
tracked CURRENT-route memory-exhaustion bug. The production default remains the typed cons tree
until the user chooses a migration path from section 13.5.

### 13.1 Slice results

Shadow Stage 1 landed in three production-inactive slices:

1. **Slice 1 — nil/text-only shadow lowering (`cdb8d0a8`).** The internal lowering scope redirected
   only empty and plain-text literals to the algebra-passing vocabulary. HTML and Markdown output
   was byte-identical to CURRENT, leaving the shadow scope restored byte-identical CURRENT poly and
   runtime results, and an effectful representation proved that document construction remained
   inert: interpretation effects were not forced until the selected representation was run. The
   scope was hidden, had no CLI entry, and did not change the parser or public default.
2. **Slice 2 — full currently lowerable static vocabulary (`5c89ed9a`).** The shadow grew to cover
   emphasis, strong, paragraphs, headings, blank lines, section closes, lists and list internals,
   code fences, quotes, text, cons, and nil. One rich literal produced byte-identical HTML and
   Markdown through CURRENT and shadow. Comparing a plain document with that rich document left
   flat format-role demands, scans, and matches unchanged and kept prerequisite demands, scans, and
   matches at zero. An intermediate generated partial application exposed a real
   `ConflictingTypeCandidates` specialization conflict between `str` and `html_node`; the slice was
   not accepted with that regression. Eta-expanding every generated document into explicit format
   and algebra lambdas restored ordinary representation generalization and independent HTML and
   Markdown specialization before commit.
3. **Slice 3 — real-literal scale (`b67db4f5`).** A real apostrophe literal with more than 70 static
   algebra operations, matching the vocabulary and scale of the characterized `proof` root, was
   placed inside an ordinary named/generalized definition. The shadow route compiled,
   specialized, and rendered structurally sane HTML and Markdown cleanly and promptly under a hard
   process resource limit. The corresponding CURRENT route did not reach a parity result: during
   check/generalization it exhausted memory and aborted. An independent 4 GiB-limited run crossed
   4 GiB RSS and failed after about 51 seconds; the retained regression now fails closed inside a
   child process with a 3 GiB address-space limit and core dumps disabled. This is a genuine,
   severe, previously undiscovered production bug in a completely ordinary usage pattern, not a
   shadow defect.

The Slice 3 failure is documented separately in
`notes/bugs/2026-07-17-yumark-generalization-memory-exhaustion.md`. Its solver-level root cause and
fix are explicitly outside this migration project. The quarantined regression must retain its OS
resource limits, and a future migration must not claim to have fixed the CURRENT solver merely
because ordinary literals stop entering that path.

### 13.2 What Stage 1 now proves

The completed evidence supports three distinct conclusions:

1. **Correct output.** At safe paired scale, nil/text and rich static literals have exact byte
   parity for both renderers. At real-document scale, where CURRENT cannot complete, shadow still
   compiles, specializes, and renders both representations with the expected structural markers.
   The latter is a success/safety oracle, not a false byte-parity claim.
2. **Dramatically lower compile cost.** The 72-operation Stage 0A and full-vocabulary Stage 0B
   controls measured 98.7-99.675% reductions in role-resolution time relative to the current
   role-shaped workload, while the retained rich shadow comparison confirms zero growth in
   prerequisite role scans as document vocabulary grows. Slice 3 cannot honestly report another
   paired percentage because CURRENT exhausts memory before completing. That non-completion makes
   the practical real-document difference larger, not a reason to invent a timing ratio.
3. **Categorically safer for realistic documents.** The current implementation can terminate the
   compiler through multi-gigabyte memory exhaustion when an ordinary real-sized literal is used in
   a named definition. The algebra-passing shadow cannot trigger this failure class because it
   never constructs or resolves the per-node recursive role tree. It is therefore not merely a
   faster equivalent path; for this realistic workload shape it removes the mechanism which makes
   CURRENT unsafe.

Taken together, Stage 0B and Shadow Stage 1 have closed the core validation gap identified in
section 10: the existing-feature algebra-passing design works through actual lowering, preserves
output and construction inertness at paired scale, stays flat as the static vocabulary grows, and
survives the real scale at which CURRENT crashes. Migration is now well-motivated for basic compiler
safety as well as performance. This is an honest reason to migrate, not evidence that the migration
itself is trivial or that its public API choices have already been made.

### 13.3 Remaining migration work and decisions

Making the shadow architecture the production default is still a meaningful engineering project.
At minimum it must:

- replace or reorganize `lib/std/text/yumark.yu` so its public implementation is the nominal
  algebra plus HTML and Markdown algebra values rather than the recursive `YumarkRender` tree;
- change `crates/infer/src/lowering/yumark_lit.rs` so eta-expanded algebra-passing builders are the
  default for supported literals, while retaining an explicit test/rollback control long enough to
  compare routes;
- settle the public spelling of the algebra, builder combinators, format selection, and render
  wrappers. The common literal-facing source can remain as small as:

  ```yu
  use std::text::yumark::{html_tag, render_html_doc, render_markdown_doc}

  my article = '{# Algebra-passing Yumark
  A document remains an ordinary let-generalized value.
  #.
  }

  html_tag (render_html_doc article)
  render_markdown_doc article
  ```

  Internally, `article` is an eta-expanded rank-1 builder and both calls instantiate it separately;
  it is not a `cons_cell` / `doc_leaf` value;
- decide what happens to source which directly constructs `cons_cell`, `doc_leaf`, or the other
  leaf structs, and ensure no compatibility adapter rebuilds the recursive tree for new builders;
- choose one of section 8.3's validated injection directions: a backend-neutral algebra operation
  or a finite payload with one monomorphic thunk per supported format. Stage 0B proved both
  directions are expressible, but Shadow Stage 1 still rejects `YmCommand` and `YmInlineExpr` and
  did not carry either direction through real lowering; and
- settle the public effect-row shape and parity gate. Stage 0B proved construction inertness and
  effectful execution under the evidence VM, while also recording the pre-existing legacy
  interpreter/mono-runtime effect-handling gap. Shadow Stage 1 revalidated inert construction but
  did not establish complete effectful real-lowering or VM/native parity.

Injection and effects may either be explicit prerequisites for the default switch or explicitly
deferred unsupported features, but that product decision must be made before the migration is
described as full public parity. It must not be hidden inside a supposedly mechanical flip.

### 13.4 Repository compatibility inventory

A repository-wide search for `cons_cell` and `doc_leaf` found one tracked consumer which imports the
actual public stdlib and manually constructs a tree:

- `tests/yulang/regressions/cache/std_prefix_role_equivalence.yu` builds a small `doc_leaf` /
  `cons` / leaf-struct canary against `std::text::yumark`.

The other matches do not establish further public-API consumers. The two
`std_prefix_yumark_*` performance workloads and the two `examples/yumark_typed_*_poc.yu` files
declare private copies of the old vocabulary; they characterize the old architecture rather than
importing its public types. `examples/yumark_lowering_plain_text_poc.yu` uses only an apostrophe
literal and render wrappers. No other tracked `.yu` source both imports `std::text::yumark` and
manually constructs a typed tree.

This makes the known in-repository source migration small, but it says nothing about untracked or
external users. Because `cons_cell` and the leaf structs are public today, absence of another repo
consumer is evidence for blast-radius estimation, not proof that a breaking switch is harmless.

### 13.5 Concrete migration paths for user decision

All three paths below make the new path production-quality rather than exposing the test-only
shadow module as-is. They differ in compatibility policy and activation timing.

#### Option A — direct clean switch

Make algebra-passing literals and algebras the only public Yumark model in the migration change.
Keep the familiar `render_html_doc` / `render_markdown_doc` convenience calls where their behavior
fits, but remove the public typed-tree structs, recursive role, and manual-tree constructors rather
than carrying a legacy runtime. Update the one in-repository public-API canary to an algebra-builder
equivalent and retain separate historical workload fixtures for solver regression coverage.

Tradeoffs:

- shortest implementation and test matrix, with no unsafe legacy path left looking supported;
- quickest route to making ordinary named literals safe by default;
- clearest long-term API and no temporary names to remove later;
- immediate source break for any external direct `cons_cell` / `doc_leaf` / leaf-struct construction;
  and
- weakest source-level rollback story if unknown users depend on typed-tree extension.

This path is most defensible if Yumark's current public construction API is explicitly experimental
and a clean break is acceptable.

#### Option B — default switch with a bounded compatibility layer (recommended balance, not decided)

Make algebra passing the default immediately after the focused migration gates pass. Preserve the
ordinary literal and render-wrapper surface above. Familiar constructor *functions* may remain as
deprecated builder combinators where their signatures can honestly return builders. Move the old
concrete structs, recursive `YumarkRender`, and old render entrypoints into a proposed explicit
deprecated `std::text::yumark_legacy` manual-construction module for one announced compatibility
window. Do not adapt a new builder to the legacy tree or choose the legacy path by inspecting names
or inferred shapes.

Tradeoffs:

- removes the crash mechanism from the default literal path while retaining a deliberate escape
  hatch for manual-tree code;
- gives external users a concrete rewrite window and keeps rollback evidence available;
- preserves common literal-facing source even though direct struct-literal construction needs an
  import/path change;
- temporarily maintains two implementations and two focused regression surfaces;
- leaves the known memory-exhaustion mechanism reachable in the deprecated legacy path, so that
  path must be documented as manual-only and unsafe for large named trees; and
- requires an explicit removal date or review gate, otherwise “temporary” becomes permanent dual
  architecture.

Given the severe default-path bug and the small known repo blast radius, this is the strongest
current recommendation: it moves safe ordinary usage promptly without pretending that a public
typed-tree API never existed. The recommendation does not authorize the choice.

#### Option C — extended side-by-side period with an explicit compiler/project mode

Publish the algebra module and wrappers while retaining CURRENT as the default, and add an explicit
toolchain or project switch which selects matching lowering and stdlib surfaces as one mode. Run
the paired corpus under both modes, seek external compatibility evidence, and return for a second
activation decision before changing the default. After activation, the switch could temporarily
serve as rollback rather than silently selecting a route per expression.

Tradeoffs:

- strongest observation window for unknown external direct-tree users and easiest whole-mode
  rollback;
- allows injection/effect decisions and diagnostics to mature before activation;
- keeps the known crash-prone implementation as the ordinary default for longer, which is a real
  safety cost rather than a neutral delay;
- adds configuration, documentation, and a doubled compatibility matrix to a design whose core
  parity is already established; and
- risks two public Yumark dialects and long-lived mode-dependent types if the activation date is not
  fixed up front.

This path is justified only if unknown external compatibility risk is judged more important than
promptly removing the demonstrated default-path safety hazard.

### 13.6 Updated migration-only size and risk

This estimate is specifically for turning the proven algebra-passing path into the production
stdlib/lowering default. It is separate from section 9's **M / medium** core-design estimate and
does not re-estimate the already completed Stage 0B/Shadow Stage 1 investigation.

| Migration policy | Size | Risk | Dominant risk |
| --- | ---: | ---: | --- |
| Option A: clean direct switch, static vocabulary | S-M | medium | Public source break and complete parity corpus |
| Option B: default switch plus bounded legacy layer | M | medium | Dual API ownership, deprecation boundary, legacy safety warning |
| Option C: extended side-by-side compiler/project mode | M-L | medium-high | Mode-coupled lowering/stdlib behavior and doubled test matrix |

For any option, including injection and effectful interpretation as day-one parity rather than an
explicitly deferred surface raises the actual migration to approximately **M-L / medium-high**,
consistent with section 9's complete-migration estimate. The known static-vocabulary default flip
is no longer high algorithmic risk: its generated builder shape, specialization repair, output,
flat role cost, and real-scale safety have all been exercised. Its remaining risk is public API and
compatibility work, plus the unchosen injection/effect contract.

**OPEN DECISION — explicit user sign-off required:** choose Option A, B, or C; choose whether
injection and full effect parity gate the default switch or remain explicitly deferred; and choose
the lifetime, if any, of the old typed-tree API. No migration step begins and no public stdlib or
lowering default changes until that decision is made.
