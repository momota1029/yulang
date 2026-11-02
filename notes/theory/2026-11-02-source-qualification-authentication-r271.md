# R271-r3 — concrete source carrier and qualification inventory

Revision 1. **Candidate source-native constructive trace, pending independent
review.** Author: `/root/sol_r270_source_qualification_auth`; no coauthors or
descendants. Contract: `tasks/agent-loop/sprints/source-qualification-authentication-r271-r3.md`,
SHA-256 `67f9423c61042798b9fb6a85efe9ecf74577d941fb64cf8f1fe2c77a291f20bc`.
Source baseline supplied by Luna: `8d646ac2ed171e13a529e25e035fc75f91678b0b`.

## Claim, evidence class and parent application

The parent remains full inference/effects soundness → R70 copy correspondence →
`R71-RAW-CANONICAL-FIBER-COVERAGE-1`, with its original accepted source domain,
quantifiers, Simple-sub A/B, independent satisfying assignments, shared
witnesses, F1/FK1 and foreign continuations. Parent/A/B delta is **0→0**.

The result below is a finite, source-body derivation for the actual opt-in
fixture constructor, including its selected feature/configuration and ordinary
successful-allocation envelope. It derives the source carrier and the graph
that collection constructs, rather than taking fixture assertions or `unwrap`
as success premises. It is not a kernel-checked Rust theorem, an observed test
run, a proof of the complete third-party libraries, or successful final type
inference/publication. No executable check was authorized or performed.
Independent review has not certified the derivation.

For this carrier the complete graph has 19 vertices and 23 raw edges. There
are exactly three checking events. Raw Value-reference SCC membership relates
loop and helper; the actual sealed native partition puts every vertex in a
singleton. All three native qualifications are false. This authenticates a
specific graph/qualification discrepancy at the constructor level, subject to
review of the source trace. It establishes neither an actual source-generated
extrusion pair at those events nor an approved intrusion-clause violation.

The first remaining parent implication is now explicit:

```text
this source Apply/checking event
  → actual reached production extrusion Ω and its actual polar parent/copy pairs
  → source-required equality / selected Parent j / physical slot s
  → independently required canonical c and its witnessed R71 continuation.
```

No occurrence, Parent, selected bound or canonical c at this implication is
invented here. `Need_D`, the R268 incidence square, all-history/raw-canonical
coverage and the original parent remain OPEN. The finite ASCII calculation
below restricts this witness calculation only; it does not narrow the parent.

## 1. Exact input, cursor and classifier facts

The constructor input at `candidate_source.rs::local_self_recursion_tests::hir`
is exactly the following 87-byte ASCII string, without a trailing newline:

```text
my outer = { my loop x = { my direct = loop x; my helper y = loop y; helper x }; loop }
```

Its source allocation is cloned into `scan_header`; `parse_file` receives that
same allocation and header. Thus the explicit `Arc::ptr_eq` assertion in
`full_parse.rs:345–360` holds by construction, independently of the test's
later `unwrap`. The selected syntax environment is `SyntaxEnvironment::empty`.

The previously missing local lexical transaction is supplied by actual source:

* `cursor.rs::SyntaxIn::token` creates an `In<&str,&mut LexRecover,()>` over
  the live source suffix and invokes its `token` method.
* `chasa-recover/src/input.rs::In::token` invokes
  `parser::token(raw).run_once(grammar)`. `parser.rs:136–152` saves a
  checkpoint, invokes the raw closure directly, and rolls back iff it returns
  `None`; it does not route the raw closure through the ordinary
  nonconsumption assertion.
* The checkpoint saves `Input::mark` and the recover mark. `Input for &str`
  saves the exact borrowed suffix; rollback assigns that suffix back.
  `LexRecover::mark/rollback` are unit operations (`cursor.rs:38–42`).
  The inspected reborrow trait and derive templates shorten field borrows;
  they do not introduce another source cursor or copy source contents.
* `In::with_str` saves start/end suffixes, checks their length/pointer relation,
  and returns the consumed prefix. It does not repair the cursor. The rollback
  belongs to `Token`, not to source capture.

In `unicode-ident` 1.0.24, `lib.rs:261–274` takes the ASCII branch and compares
the appropriate mask with `1 << (ch as u128)`. `tables.rs:14–15` gives

```text
ASCII_START    = 0x7fffffe07fffffe0000000000000000
ASCII_CONTINUE = 0x7fffffe87fffffe03ff000000000000
```

Reading their set bits gives Start at 65…90 and 97…122; Continue additionally
has 48…57 and 95. The fixture letters
`c,d,e,h,i,l,m,o,p,r,t,u,x,y` therefore satisfy both predicates. Space (32),
`;` (59), `=` (61), `{` (123), and `}` (125) satisfy neither. These are finite
bit-index calculations from the constants, not calls to a probe. Non-ASCII
trie/table lookup is not reached by this input.

Consequently `lexer.rs::scan_identifier` consumes exactly each identifier.
For example its continuation probe consumes the space after `outer`, returns
`None`, and restores that space; its optional `?`/`!` suffix probe likewise
restores the same space. The next CurrentItem owner then consumes the space
as trivia. The same argument applies to each identifier/terminator in this
string. `scan_exact_word` checks its source prefix before consuming a keyword;
the keyword-following space does not violate its maximal-word guard.

Falsifiers of this step are a different mask bit, a cursor reborrow that does
not share the input field, a Token implementation that commits `None`, or a
non-ASCII character/different source allocation. None is supplied by the
inspected constructors for this exact input.

## 2. Header, full parse and CST content

`header.rs::discover_header_with_cursor` sees `my` at physical start and then
`outer`. The use selector rejects because the observed following word is not
`use`. Binding's mod/struct/type selectors all return false from their
ordinary source-word mismatch; binding's follower accepts the ordinary
identifier `outer`. Thus `header::operator_selected` returns false at its
Binding preference. Discovery stops at the first non-header, with coverage
`0..0`, `HeaderStop::FirstNonHeader`, empty imports and empty operator facts.
All selector owners added in R270-r3 were inspected; there is no assumed
normal return through the former unlisted selector chain.

`SyntaxEnvironment::empty` supplies an empty imported table.
`effective_full_parse_operators` executes neither merge loop on these two
empty inputs. Its default builder's empty map builds `OperatorTable::empty`.
It returns `Ok(empty)`; the caller's `expect` is therefore justified by this
specific construction, not used as a success axiom.

The full root loop then classifies `my outer` as Binding. Its complete
nonbinding selection sequence is struct/enum/error/mod/type/role/impl/cast/act,
then `for`; each rejects the ordinary following word `outer` (and the `for`
selector rejects `my`). Binding accepts. The same finite selector calculation
applies to `my loop`, `my direct`, and `my helper`. The expression-only heads
`loop`, `helper`, `x`, `y` are ordinary Identifier Items, without a dynamic
operator entry.

The precise node-building steps are:

1. `binding_statement_normalized` starts BindingStatement/BindingHeader,
   emits MyKw, and builds a Pattern. Its identifier branch emits
   IdentifierPattern. For `loop x` and `helper y`, the space admits one
   PatternMlApplicationTail containing a Pattern/IdentifierPattern formal.
   The exact Equals Item is handed back at `PATTERN_STOP_EQUALS`, then emitted
   by the Binding owner. `outer` and `direct` have no formal tail.
2. There are no introduced-body newlines. The inline body path starts an
   OperatorChain. Its ordinary `{` head goes to `braced_nud_normalized`;
   `literal::string_mode_from_opener` returns None because quote_run is zero
   while the ordinary spelling is nonempty. The contextual rule/case/catch/if
   cases do not match. The same None argument holds for ordinary identifiers.
3. `braced_statement_block_with_recovery_normalized` starts
   BracedStatementBlockExpression and wraps each admitted child in Statement.
   The two explicit inner semicolons and the outer semicolon are consumed by
   `braced_explicit_separator_normalized`, each making a
   BlockStatementSeparator. Every block ends with an expression, not a
   trailing separator or a missing statement.
4. The Identifier head in each `loop x`, `loop y`, `helper x` emits an
   IdentifierExpression. The space admits exactly one MlArgument;
   its argument OperatorChain uses `MlMode::None`. Each argument ends at the
   already active semicolon or right brace. No operator, nested Apply, literal,
   annotation, path tail or additional argument is present.
5. The matching right braces are actually emitted by the braced successor/
   terminal owners. After the outer brace, the root loop receives EOF and its
   terminal assertion holds. All recovery-emitting alternatives are bypassed:
   each required Pattern/body exists, every inner separator has a following
   statement, each close matches, and no unclaimed token remains.

Ignoring trivia tokens, the resulting CST is exactly:

```text
Root
  BindingStatement outer
    BindingHeader: MyKw Pattern(IdentifierPattern outer) Equals
    BindingBody: OperatorChain
      BracedStatementBlockExpression
        Statement: BindingStatement loop
          BindingHeader: MyKw Pattern(loop, ML-tail Pattern(x)) Equals
          BindingBody: OperatorChain
            BracedStatementBlockExpression
              Statement: BindingStatement direct
                BindingHeader: MyKw Pattern(direct) Equals
                BindingBody: OperatorChain(Name loop, MlArgument Chain(Name x))
              BlockStatementSeparator ;
              Statement: BindingStatement helper
                BindingHeader: MyKw Pattern(helper, ML-tail Pattern(y)) Equals
                BindingBody: OperatorChain(Name loop, MlArgument Chain(Name y))
              BlockStatementSeparator ;
              Statement: OperatorChain(Name helper, MlArgument Chain(Name x))
        BlockStatementSeparator ;
        Statement: OperatorChain(Name loop)
```

This content argument uses the inspected Rowan constructors, not a supplied
tree assertion. GreenNodeBuilder pushes a parent checkpoint at start_node,
drains precisely the appended child suffix at finish_node, and finally
requires one root child. GreenNode::new records children in iterator order and
accumulates relative text offsets. NodeCache either builds that node or
returns one with the same kind and exact child identities; token equality is
kind plus text. Hashbrown's inspected from_hash/search/find path returns an
occupied entry only after the equality predicate succeeds. Therefore hashing
or interning does not select a different CST content. SyntaxNode's root/first
child/next sibling adapters traverse those ordered green children while
skipping tokens for `children()`. Text-size arithmetic is within 87 bytes.

This is a content trace within ordinary Rust/library successful allocation,
not a new proof of unsafe allocator/reference-count internals or arbitrary
library inputs. The exact external source bytes are authenticated by the
manifest and archive checksums; Luna's readiness records the archive-member
comparisons. This author rechecked their file hashes, not every archive-member
comparison. No build or macro expansion was executed.

## 3. HIR identity and lexical construction

The fixture identity is `ModuleIdentity::source_root(FileId::new(FileKey::new(
"local-self-recursion-kernel", "source.yu")))`. Let A be the freshly minted HIR
artifact token. Its single direct root is an admitted private Binding named
outer, `same_name_ordinal=0`, with no root parameters. Let R denote its actual
`DefinitionRootId(A, DefId(module,"outer",0))`; let `SR=Definition(R)`.
These symbols retain the constructor identities, not chosen integer stand-ins
or solver rows.

`lower_module_with_local_source` creates source keys from this exact ParsedFile,
sets local_source=true and calls the common lowering owner. There are no
structural recoveries. Source effect/role/implementation declaration scans have
no matching root kind, and no import/caller-evidence checks are activated by
`SemanticImports::empty`. `plan_root` and `plain_binding_header` accept the
shown outer header. The module namespace has its single outer definition.

Before ordinary body lowering, `lower_plan` invokes `local_source::form` with
this R and no root parameters, and stores the returned carrier under R in
`counters.local_sources`. All source keys needed by this finite traversal came
from `source_keys(parsed)`; `SourceNodeKey` retains the parse brand, green
allocation and start position, including repeated identifier spellings.
The carrier is retained even though the older ordinary body projection is
Unsupported for the brace body and yields an UnsupportedExpression placeholder.
That placeholder is not failure of `form` or of the opt-in HIR constructor;
neither is it a successful ordinary/default type inference result.

The exact LocalSource slots are below. Write e_i for the actual occurrence in
slot i, and I_i for `LocalSourceIndex(SR,i)`. Local IDs are
`L=HirLocalId(SR,0)`, `D=HirLocalId(SR,1)`, `H=HirLocalId(SR,2)`;
parameter IDs are `X=HirParameterId(SR,0)`, `Y=HirParameterId(SR,1)`.

| i | Form / children or resolution | Source owner scope |
|---|---|---|
| 0 | Block bindings [L], final I1 | Definition R |
| 1 | Name loop → Local L | Expression I0 |
| 2 | Lambda parameter X, body I3 | LocalInitializer L |
| 3 | Block bindings [D,H], final I4 | Parameter X |
| 4 | Apply callee I12, argument I13, MlArgument | Expression I3 |
| 5 | Apply callee I7, argument I8, MlArgument | LocalInitializer D |
| 6 | Lambda parameter Y, body I9 | LocalInitializer H |
| 7 | Name loop → Local L | LocalInitializer D |
| 8 | Name x → Parameter X | LocalInitializer D |
| 9 | Apply callee I10, argument I11, MlArgument | Parameter Y |
| 10 | Name loop → Local L | Parameter Y |
| 11 | Name y → Parameter Y | Parameter Y |
| 12 | Name helper → Local H | Expression I3 |
| 13 | Name x → Parameter X | Expression I3 |

The initializer indices of L,D,H are I2,I5,I6, respectively. The builder
allocates I0, outer final I1, L initializer I2, L body I3, then inner final I4,
D initializer I5, H initializer I6. Processing D first allocates I7/I8;
processing H next allocates I9 then I10/I11; the final Apply allocates I12/I13.
This is the actual slot/allocation order, not textual sorting. Named groups
belong to L and H and retain X/Y respectively. There are no defaults,
annotations, where clauses, root parameters, expression-prefix statements,
synthetic Unit/Apply nodes or unused empty expression slots.

The binding calculation is source-directed. Initializer(L) temporarily pushes
Local L before parameter X. D has no self binder and sees that L and X; Publish
D then installs D. Initializer(H) temporarily pushes H, then Y, so its loop
still resolves to the outer L and its y resolves to Y. Publish H restores its
guard and installs H. The inner final helper/x resolves to H/X. Restoring the
inner block removes D/H; Publish L restores its outer guard then installs L,
so the outer final loop also resolves to L. Every Name uses the latest lexical
entry; module fallback is never selected for these seven Names. This accounts
for shadowing and nested recursion rather than treating spelling as identity.

`form` verifies every allocated slot is filled. It returns the above carrier;
the surrounding HIR owner returns its single binding with the same R. Resource
failure is an explicit availability exit; this trace states normal-return
equations rather than claiming allocation can never fail.

## 4. Collection retains exactly that carrier

Use the fixture's call `ConstraintBatch::collect_candidate_mode(hir,true,true)`
under `shadow-apply-candidate` (which activates HIR shadow through shadow-f5).
It selects unscoped mode: scoped_experiment=false, operation_v1=false, one HIR,
empty imported-definition and provider-root inputs. This configuration is
explicit; no claim about an unselected/default build follows.

`lib.rs:1060–1083` registers R and its same DefId in the Value-reference graph
before visiting the body. It creates one collection-branded DefinitionOrderId
with ordinal 0. The true/true branch obtains `hir.local_source_for(SR)`;
that method returns the carrier in `local_sources[R]` for this opt-in HIR.
`emit_candidate_source` independently obtains it again and checks pointer
equality plus exact receiver DefinitionOrderId/R ownership. Thus no reconstructed
or foreign copy of a similar carrier enters the graph.

All 14 occurrences are artifact-owned; source-owner inserts agree on SR.
The positions/parameter/local maps have 14/2/3 entries with distinct identities.
There is no unresolved/imported/module Name, so pending definition uses are
empty. The source walk sees only Block/Lambda/Apply/resolved Name branches.
Each required map lookup uses an entry already constructed above. There is no
scoped-only callee refusal or annotation/default/catch/operator branch.

Planning begins at I0 level 1. A Block increases initializer level by one,
preserves final-expression level; Lambda preserves its body level. Therefore
the source expression levels, in slot order, are

```text
i:      0 1 2 3 4 5 6 7 8 9 10 11 12 13
level:  1 1 2 2 2 3 3 3 3 3  3  3  2  2
```

L/X birth at 2 and D/H/Y birth at 3 are recorded at their actual declaration/
formal introductions. Later Names do not reassign their semantic births.
Recursive Name slots I7/I10 emit Links to the active L initializer endpoint;
the published H at I12 and L at I1 use Local actions. Links are constraints,
not row equality. The two Blocks generate Group recipes and the two Lambdas
generate Lambda recipes; neither creates another reference event.

The collection seal at `lib.rs:1551` is analyzed next. The remaining static
definition-SCC planner has one same-artifact definition and zero uses; its
forward/reverse graphs have one empty adjacency and one singleton component.
Its duplicate/foreign/totality guards are satisfied. Thus the trace gives the
normal `Ok(batch)` return, conditional on the explicit allocation envelope,
rather than relying on `unwrap`. It asserts no session drain or publication.

## 5. Complete Value graph, levels and event inventory

Graph::retain_source first interns the module root O. The root-owner walk
interns L, then D/H at the inner Block; its LIFO walk visits H's initializer
before D's, so Y is interned before X. Fragment helpers are then allocated in
expression-vector order, followed by Apply-result Values in that same order.
The exact ordinals and complete outgoing adjacency are:

| v | Descriptor | planning level | raw outgoing vertices |
|---|---|---:|---|
| 0 | O = Value::Module(outer DefId) | 1 | 1 |
| 1 | Value::Local L | 2 | 5,3 |
| 2 | Value::Local D | 3 | 5,1 |
| 3 | Value::Local H | 3 | 4,1 |
| 4 | Value::Parameter Y | 3 | ∅ |
| 5 | Value::Parameter X | 2 | ∅ |
| 6 | helper for Name I1 | 1 | 1 |
| 7 | helper for Apply I4 | 2 | 14,15 |
| 8 | helper for Apply I5 | 3 | 9,10 |
| 9 | helper for Name I7 | 3 | 1 |
| 10 | helper for Name I8 | 3 | 5 |
| 11 | helper for Apply I9 | 3 | 12,13 |
| 12 | helper for Name I10 | 3 | 1 |
| 13 | helper for Name I11 | 3 | 4 |
| 14 | helper for Name I12 | 2 | 3 |
| 15 | helper for Name I13 | 2 | 5 |
| 16 | Value::Expression e4 (helper x result) | 2 | 7 |
| 17 | Value::Expression e5 (direct's loop x result) | 3 | 8 |
| 18 | Value::Expression e9 (helper's loop y result) | 3 | 11 |

The seven definition-owner edges come from the seven Names I1,I7,I8,I10,I11,
I12,I13. The seven Name-helper edges target their actual resolved Values.
The three Apply Values each point to their helper; each Apply helper points
to its two direct Name-child helpers. Total: 7+7+3+6=23. Every reverse edge
is installed by the same `edge(from,to)` call. There are no containment edges
to D, no Lambda/Block semantic-expression vertices, and no copied type rows in
this graph. The ten descriptor-free helpers remain distinct from semantic
Values. Every branch represented by this HIR has been accounted for.

`retain_source` creates an event only for LocalSourceForm::Apply. It scans the
expression vector, giving exactly the following inventory; recipe execution
order (D, H, then inner final) is deliberately distinguished from event order.

| event | exact checking identity | origin v | receiver v | expression |
|---|---|---:|---:|---|
| 0 | ConstraintOccurrenceId(e4,0) | 1 (L) | 3 (H) | helper x in loop body |
| 1 | ConstraintOccurrenceId(e5,0) | 2 (D) | 1 (L) | loop x in direct |
| 2 | ConstraintOccurrenceId(e9,0) | 3 (H) | 1 (L) | loop y in helper |

Both origins and receivers are semantic Values; each checking identity comes
from the same actual occurrence used in its retained Apply recipe. Extra
synthetic events from fresh use, Group, Lambda, Links, module Names, type
copies, default fields or imported/operator bodies are absent on this carrier.

## 6. Seal success and actual qualification consumption

The graph initially has no component vector. Before seal all 19 planning-level
entries are Some and match edges.len(). Every edge entering a descriptor-free
helper is either an Apply-result→Apply-helper edge or an Apply-helper→its
Name-helper edge; the table shows equal levels at both ends. This proves both
actual rejection guards in `Graph::seal:354–366` are bypassed, rather than
assuming success from the caller's `?`.

Both SCC DFS passes traverse only equal-level edges (`:376,:389`). At level 1
there is no cycle; at level 2 the remaining directed paths end at X or leave
the level; at level 3 they end at Y or leave the level. Hence every induced
same-level SCC is singleton. Each second-pass root labels only itself, so
`components[v]=v` for all 0≤v<19. The procedure returns Ok after its finite
walk, subject to its explicit reservations succeeding. Session construction
later calls seal again (`lib.rs:10466`), which takes the already-sized fast path.

Consequently actual `qualifies(0/1/2)` is false. Invalid event ordinals also
return false by the method's `get`/`is_some_and` chain. In the unfiltered raw
graph, L→H and H→L put exactly L/H in a nontrivial SCC; D has no return path.
Thus the approved raw-graph eligibility comparison would be true for events
0 and 2, false for event 1. This is a partition/eligibility comparison, not a
claim that an actual retained type pair exists for either event.

The qualification method is consumed by production source paths:

* Source Apply execution in `shadow_apply.rs:4302–4399` constructs the negative
  Function demand, retains its NativeInterface/source registration, then
  admits slot 0 with that same recipe occurrence.
* `candidate_context_seed:3793–3813` joins the checking map and makes the
  singleton event source set when that actual slot is reached. The context
  retains its actual RelationId, sources and demand/scoped payload.
* `retain_extrusion_parent:305–365` tests the whole actual processing source set
  existentially with `references.qualifies`, appends a Parent with actual
  polar copy/parent endpoints, and marks it pending only when qualified.
* `finish_candidate_extrusion:368–386` computes group activation by the same
  test. `recapture_candidate_extrusion:390–421` uses the actual reused group's
  new source set and this test, retaining separate reuse identity.

Those are real consumer calls, not evidence that this packet executed them.
The complete event table now gives a stronger conditional fact than R269's
single-event observations: **for this isolated batch, any such existential
qualification returns false, whatever its actual source-set contents**.
Each valid event is false, and invalid indices are false too. No merge or
source-set union can manufacture a true value. This does not assert that any
selected Parent/slot is reached or that any particular extrusion is necessary.

## 7. Boundary, reused work and mutual TODOs

The approved top-level principles §1.1, value-to-type association and
parent-copy SCC decisions require actual source references without lexical
level filtering, actual origin/receiver association and actual produced polar
pairs, followed by consumed equality. The observed graph eligibility differs
at events 0/2, but the operation's actual-pair premise is still absent here.
No semantic change, source restriction or production repair is inferred.
`NO_SAFE_CODE_SLICE` remains: the inspected Graph::seal/qualifies and
retain_extrusion_parent/recapture owners supply no authenticated reached pair
whose required equality is lost.

`R271-ACTUAL-PAIR-JOIN-1` to Luna, same original parent: join one of e4/e9's
actual Apply actions to its successful source-seeded processing ancestry,
reached extrusion Ω, actual produced polar pairs and consumer. Inputs are
the frozen R/SR/e_i/L/H identities above and exact ordered processing inputs;
output is a witnessed actual-pair/qualification correspondence or the first
failure. Falsifier of a defect claim: no extrusion/pair is produced, a different
occurrence owns it, or an independent approved consumer path supplies the
required equality. An execution/provisional observer needs a separate exact
lease; none is written or authorized here.

`R269-SOURCE-NEED-CARRIER-1` remains to Luna: independently justify the exact
canonical c-bearing source obligation, then preserve every relevant selected
slot/history path and actual ordered opposite Replay inputs through the R71
square. This packet does not manufacture Need_D from graph membership or
from source-set nonqualification. Equality/transport/residual/provider/witness
lineages stay distinct. R70's bounded raw-prefix theorem and R267-r6's exact
Function-slot case retain their original premises; neither fills this join.

Reused within actual limits: R269-r4's reviewed LEVEL269 and ownership
characterizations (author `/root/sol_r269_source_need_r4`, independent review
`/root/r269_source_need_r4_review`); the R270/R271 earlier local prefix facts
by this author, now extended with cached ASCII/cursor/CST source owners.
Earlier `unwrap`/test assertions, graph-only source sketches and type-copy
vertex interpretations were rejected as authentication. R70/R71/R267/R268
historical artifacts were used only for their unchanged parent/gap definitions;
no quarantined output, R255 theory or withdrawn bypass is imported.

ENTRY-WF, drain/eventual Diagnostics, Q262-EPISODE, TEMP265/Z265 Effect temporal
simulation, permitted histories/rollback, diagnostic/helper coverage, complete
Call, full soundness, A/B, F1/FK1 and foreign continuations remain OPEN.

## 8. Pins, resources and freeze protocol

Direct manifests: R271-r2 contract
`dfab9720fea19807bca1ad386bffbe4bdb508bef222c5f6480001350be35569e`;
R271-r3 contract
`67f9423c61042798b9fb6a85efe9ecf74577d941fb64cf8f1fe2c77a291f20bc`;
additive readiness
`ef2b3f4c51e383722b458483ba3f5cf05e35ee8e4d918545c94294d0734a7871`.
Inherited R269-r4 contract
`a5f3bd1f3bc701ce75191ec234b72264d0dd9e73d7dfd31b88f0b8da0c6009ec`;
R255 manifest `f6138d36052934093328e34c01102fc9155ea9d8a0ccfd19182af6e7e2d946ef`.
Original approved source hashes and all source hashes are those exact manifests;
no new source authority is supplied by this note.

Initial r3 gates matched 139 local/r2 plus 68 additive external rows, 207
manifest rows total; 302 distinct inherited/direct pinned paths matched.
The seven new archive hashes match the pinned lock entries; the earlier three
reborrow/derive/seq archive checksums were also checked. Cached source/member
byte correspondence is reused from Luna's readiness audit, not independently
certified by this producer. Final gates and this artifact hash are in the
single frozen handoff/terminal receipt. Bulk source output incidentally included
in-file cfg(test) sections and some output was truncated; no test body is used
as a proof premise and no exhaustive third-party-library audit is claimed.

Requested registered prover Sol/high; observed effective model/effort and child
runtime UUID UNKNOWN. Exact identity `/root/sol_r270_source_qualification_auth`
was compared before fresh GO in session `01a1873a-a93b-7dc3-a8ce-028a7b543a80`.
R271-r3 cap 1,200 seconds, no reset/extension; all earlier Sol reservations
remain charged (R270 4,500; R271-r1/r2 3,600; cumulative with r3 9,300).
Actual active elapsed/CPU/RSS UNKNOWN. Observed UTC cuts include 13:42:52,
13:44:44, 13:48:32 and 13:49:16 on 2026-11-02.

No Lean theorem/axiom audit applies to this non-Lean trace. No tests, builds,
probes, Cargo, network, source/expectation edits, Git, nested CLI, descendants,
scratch/cache/generated outputs or other file writes. New paths are exactly
this theory and the one leased R271 inbox. After final pin/artifact hashing,
all reads and writes stop; fresh review/adjudication/state/Git belong to Luna.
