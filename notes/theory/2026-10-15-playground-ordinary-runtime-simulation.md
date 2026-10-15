# Private playground ordinary runtime: operational simulation

Date: 2026-10-15
Status: independently reviewed constructive ordinary completed-path simulation and final
frozen-source bridge; original counterexamples repaired and current no-adapter
premise derived at its registration owners; independent review passed
Claim class: local operational simulation for the validated constructed-program
envelope; no inference soundness, full source completeness or hygiene closure
Baseline: `cdfdb58bb244fecf0c895a6a1d65b2bdee06548c`
Production baseline supplied by primary: `266da3dd6`
Branch: `research/simple-sub-intrusion`
Exclusive producer lease: this file only

Independent closure: `runtime_semantic_review` checked the frozen artifact
`68c0435377e5baa96aa05787d93ad0ee5d665dff6091c3ad9f9a09aaa394a744`
and its final implementation dependencies with no findings. Promotion covers
only the local constructed-program ordinary completed-path simulation below.
The original full-source, effectful Call, hygiene, inference and production
parents remain open.

## 1. Frozen objective and authority

Construct the local execution invariant for the private ordinary evaluator, then
discharge its actual source/operational correspondence against frozen runtime
files. The primary owns verification, integration and independent review. The
runtime implementation is concurrently owned by a different worker. Its moving
files are not premises of this reference derivation.

Governing source decisions are source-call-scheduling-choice §§1, 1.1, 2A and 4
(Authoritative whole-argument introduction and same-receiver Value entry), and
redesign-charter §21 (Authoritative source parameter roles). The existing
typed-computation-core-elaboration §§2–6 supplies the finite derivation-core,
Data/Normalize equations, local result binding and lexical interface premises.
That document remains Draft: its reviewed local construction is reused as
research mathematics, not promoted to implementation authority. The primary's
architect packet supplies authorization for a provisional internal arena,
environment and explicit continuation machine in the playground. Ordinary-
computation-semantics-package §3 supplies current-configuration closure/Force
equations. Its §§4–5 identify the additional hygiene/handler premises excluded
from this ordinary proof.

The inference top-level principles §§1–4 and compiler-engineering's
proof-obligation economy prohibit claiming that this execution derivation proves
native Simple-sub constraint generation, inference soundness or principality.

### Quantifiers, original identities and hypotheses

Fix any successfully formed immutable LocalSource family S from the baseline
opt-in HIR route; any selected expression occurrence e in S; one supplied,
well-scoped lexical interface assignment Gamma; any well-formed lexical runtime
environment eta related to Gamma; and a current execution configuration C.
Quantify over all finite ordinary execution prefixes, all completed evaluations
at their designated Result consumer, and all future ordinary calls/forces of
returned closures/carriers in related environments and current configurations.
No fixed bound on recursion depth or number of later forces enters this
semantic quantification. Resource-bounded implementation outcomes are separate.

Original expression identities are (DefinitionRootId, LocalSourceIndex), with
the occurrence/source/range retained by that exact immutable artifact. Original
binders are the disjoint ModuleDef(DefId), Parameter(HirParameterId),
Local(HirLocalId) and CatchBinder identities, never their spellings or arena
ordinals alone. A recursive reference targets the existing binder/code label;
it does not unfold its body. Endpoint variables in Gamma and original annotation
positions remain universally fixed inputs. Any admissible endpoint substitution
must preserve source interface tags, binders and corresponding paths. No
independent marginal choices of endpoints or witnesses are allowed.

The hypotheses are:

1. S really comes from successful baseline formation, with authentic parsed
   source provenance and owner-checked read APIs. Arbitrarily forged graphs are
   not covered by the source-to-formation bridge.
2. Gamma assigns known source interface tags and declared receiver roles at the
   lexical/declaration owners. Ordinary parameter roles come from charter §21;
   body use and solved type shapes cannot change them. Source data/read and
   result/consumer judgments are distinguished exactly as typed-core §6.
3. eta supplies each dynamically reached resolved binder's actual related
   value/cell. A module environment is an input here; no unspecified module
   initialization rule is assumed. A missing read produces an explicit failed
   observation, never a fabricated related value.
4. Ordinary source operations used by a completed derivation have their
   independently admitted semantics: literals, selection, grouping, permitted
   ascription erasure, lexical closure, application and local sequencing.
   Handlers, request receipt/dispatch/resumption and profile activation are
   separately pending. Any call requiring them must not be certified complete
   by this ordinary derivation.
5. A concrete implementation source bridge must establish its own constructors,
   mode changes, continuation transitions and completed-outcome decoder. These
   are proof goals, not assumptions that frozen runtime code satisfies them.

Required conclusion: every actual ordinary Completed result covered by the
bridge is the result of the designated source computation, with related latent
values/environments, preserved lexical binding and source roles, the same
execution ordering, and no extra execution of latent data. Every related
semantic finite ordinary prefix has corresponding machine transitions before
implementation resource exhaustion. The conclusion does not assert that every
source input completes, or that an Unavailable/exhausted outcome is a source
value, source divergence, source rejection or type error.

Excluded conclusions: whole-program startup/order; full source admission;
catch/handler/hygiene; requests and raw resumptions; typed boundary/profile
transport; effect support accuracy; arbitrary ascription/conversion coherence;
native inference soundness, principality, generalization and production cutover.
These exclusions leave the original parent gates open; they add no source
restriction or permission to discard required behavior.

## 2. Actual immutable source owners

At this baseline `yu-hir/src/shadow.rs::lower_module_with_local_source` calls the
opt-in source-owning lowerer. `HirModule::local_source` checks exact artifact root
ownership before exposing a retained carrier. In `module/local_source.rs`,
`LocalSource::expression` checks its index's DefinitionRootId before indexing.
`LocalSourceExpr` retains occurrence, source node, range, scope and constructor;
`LocalSourceParameter` retains its original ID and annotation. Thus one must
construct code addresses from the exact owner plus ordinal, not ordinal alone.

The actual constructors consumed by ordinary execution are Unit, Integer,
Boolean, String, Name, Apply, Group, Ascription, Lambda, Block and If.
Operation and Catch exist in the same source sum and must be explicitly pending
where operational evidence is missing. Runtime incompleteness does not remove
them from the source language.

Formation's `form` registers root formal IDs before its work loop. A named
local `Work::Initializer` temporarily publishes its own Local ID only when it
has parameters, then publishes those parameter IDs; parameters may shadow the
self spelling. `Work::Publish` restores the initializer bracket and publishes
the same Local ID for subsequent statements. A nonparameterized RHS does not
gain a new self binding. `block` records initializer ordinals in source order
and pushes them in reverse onto LIFO work, followed by the final expression.
This proves the lexical ownership/visibility supplied to runtime resolution;
it does not by itself prove RHS execution or any module startup semantics.

Identifier formation chooses the latest lexical entry, else the unique module
definition, else Unresolved/Ambiguous. The resulting resolution enum is the
runtime lookup input. Runtime must not resolve a successfully formed Name
again by spelling. This is stable under alpha-renaming that transports the
same IDs. Inline lambda formation similarly creates its exact fresh parameter
ID and brackets its body with lexical Restore.

`SourceAnnotationType.effects: Option<SourceEffectRow>` retains the *outer*
annotation distinction. `Some(row)` includes an empty or wildcard row and
selects Computation entry; None selects Value entry for the ordinary forms.
Nested Function annotations are not a license to classify the outer parameter
by a nested effect or the runtime representation of the result.

## 3. Reference construction and central invariant

Write V(e,eta) for inert source Data and N(e,eta) for the designated
Result/Normalize computation. Write I(e) for the source interface generated
from Gamma. Their defining equations are:

```text
N(e,eta) = Return(V(e,eta))                    if I(e) = Value(A)
N(e,eta) = Force_p(V(e,eta), current C)        if I(e) = Computation(E,A)

V(literal,eta) = its literal value
V(Name(x),eta) = eta[resolved x]
V(Lambda(P,b),eta) = Closure(label(b), P, eta)
V(Apply(f,a),eta) = Delay(label(Call(N(f), N(a))), eta)
V(Block(bindings,b),eta) = Delay(label(SequentialBind(bindings,N(b))),eta)
```

Grouping preserves the child's original interface. An admitted static
ascription may use the same inert computation only where its source checking
rule erases without an adapter; this does not prove arbitrary casts. If is the
existing conditional source operation, delayed until its own result consumer.
Its conditions run left to right until true, only the selected body executes,
and the else branch executes only after all conditions fail. With no else a
normally completed taken body is discarded and the result is Unit, following
the reviewed omitted-else source owner; no synthetic body occurrence is needed.

Code labels describe finite templates and original child links. Allocate all
labels before references are activated. A closure/carrier captures lexical
value/cell references plus code labels; it captures no current continuation,
call stack, future caller store, grant or active handler snapshot.

Use an explicit current command plus a finite stack K of continuations. Its
semantic interpretation plug(K,c) is defined by stacking the original pending
source suffixes. A continuation for local Bind means “receive this RHS value,
bind that exact Local ID, then execute remaining bindings/final expression”;
a Value-entry continuation means “receive argument result, rebind that exact
formal, run this body, then return from this invocation.” A callee continuation
means “receive callable, introduce the whole argument, then enter it.” This
notation specifies reference meanings, not a claim about uninspected enums.

**Central invariant R.** At every represented ordinary machine state:

1. Its current code address denotes the same original source occurrence or
   named administrative template under the same lexical binder environment.
2. Every runtime value is related to its source value: literals by value;
   closures by source body/role and captured environment; carriers by the whole
   designated computation label and captured environment; recursive cells by
   the same source binder and related current contents. This is a graph
   relation, so cycles are permitted without unfolding.
3. plug(K,current) is exactly the pending source computation. Argument code is
   under its Delay until receiver entry or another designated consumer. Pending
   RHSs, rebinds, bodies and returns appear once and in the original order.
4. Captured lexical environments and current execution configuration are
   separate. Force/call uses the saved lexical references and *current* C.
5. The current Data/Normalize mode is justified by the original source tag at
   its owner. A runtime value's shape supplies no additional source consumer.

## 4. Constructive derivation

### Inert introduction and lexical lookup

Allocating a descriptor containing code label and eta changes only private
representation storage. It executes neither its label nor any child code.
Thus each closure/Delay introduction preserves R and cannot emit a source
event or execute an RHS. Name Data returns the value/cell selected by the
stored resolution identity; related environments give related results. An
unbound or uninitialized read has no value-relatedness witness and therefore
cannot take a Completed transition.

For Normalize, case-split solely on the source tag. Value returns the related
Data unchanged, including a latent carrier/function. Computation applies its
one designated Force_p. The result A is kept as a value; even a latent A adds
no recursive force. Empty support E changes neither case. These two clauses
are disjoint and exhaustive for the fixed interface grammar. Endpoint
substitution preserving the tag commutes with them directly. In particular,
Comp-formal Name in result position uses Gamma(Name)=Computation and consumes
that port; merely retaining the formal at entry does not make its later body
consumer disappear. Conversely an inert Data read alone executes nothing.

### Complete ordinary call

The delayed application's executable clause is:

```text
N(f,eta) >>= fvalue.
  let t = Delay(label(N(a)),eta) in
  Receive(actual receiver, t, current C);
  if receiver P = Value:
      Force(t,current C) >>= v.
      Rebind(formal,v); N(body, eta_cl[formal := v])
  if receiver P = Computation:
      N(body, eta_cl[formal := t])
  ReturnFromThisInvocation
```

Here Receive/Rebind name the ordinary control/data positions. Full typed
receipt/Flow/Observe evidence is not supplied by their names. The actual
ordinary implementation bridge must identify those positions; the separate
hygiene bridge must provide its typed evidence.

Callee evaluation precedes Delay creation. Neither its continuation nor Delay
creation evaluates a prefix of a. Receipt is established before either entry
branch. Value entry places the unique rebind/body suffix on K and forces t;
no transition enters the body before the result v is received. Computation
entry stores the *same* t, with no force. Its explicit body consumers are N
and therefore retain their own source-tag justification. Different later
consumers may execute the carrier again: this proof adds no memoization or
once-ever force claim. “Once” here means the single selected Value-entry
consumer for one invocation, and the single selected RHS of one dynamic Bind.

For a closure the environment is eta_cl extended by the actual formal binding,
not the caller's lexical environment. The current C still comes from the
caller. Return removes the current invocation's pending delimiter only. This
is the §3 source rule with an explicit pending suffix, not a synthetic wrapper
invocation. A native operation additionally needs its independently declared
post-native-return result consumer; a carrier-producing operation result
cannot be called a completed source result by this ordinary argument.

### Sequential local binding and recursion

For dynamic Bind(x,r,b), execute N(r,eta) with one pending bind continuation.
On its one normal return v, extend the body environment by x:Value(A_r) and
v; then execute b. Advance the source-order cursor only at this transition.
Induction on that cursor gives left-to-right RHS execution, exactly one
evaluation of each reached RHS for this block activation, and final-expression
execution only after every preceding RHS normally returns. Failure or
divergence before a later RHS never executes that later RHS. Returning latent
data from an RHS stores it without an additional consumer.

For a parameterized self-recursive local, allocate the original self cell in
the initializer's lexical environment, create its lambda descriptor with that
environment, then publish the descriptor into the same cell. Lambda creation
does not execute the body, so every reached self read after application sees
the published value. This realizes formation's temporary self identity.
Nonparameterized RHSs retain formation's different visibility. Ordinary
recursive application jumps to the existing body label, constructing a new
environment and explicit pending suffix. It invokes no meta-level recursive
evaluation/unfolding rule. Induct on each finite execution prefix, not source
recursion depth. Termination of arbitrary recursive programs is not asserted.

### Force, current configuration and finite-prefix simulation

Force(Delay(label,eta_saved),C_now) switches the code/environment to
(label,eta_saved), retaining the existing caller's pending continuation and
threading C_now. It never restores C_at_creation. Each later force follows
this same equation. In the ordinary event-free fragment the source current
store/activity has no additional observable update; their preservation here
does not prove effectful owner re-entry or handler eligibility.

Prove preservation of R by cases on the displayed command/continuation rules.
Literal/Name return uses relatedness; closure/Delay introduction uses the
inertness lemma; callee completion uses the complete-call lemma; entry return
uses the unique rebind suffix; local RHS return uses the sequential lemma;
conditional continuations retain their remaining ordered conditions and
selected/discarded body mode; Force uses the current-configuration equation.
Each proper machine control step implements the corresponding source step;
finite label/mode administrative steps preserve plug(K,current). There is no
unbounded administrative loop without a source execution step: the only
cyclic code edges activated dynamically are actual recursive call/Force
steps, and finite child dispatch/continuation handling introduces finitely
many administrative transitions per displayed source step.

Initial relatedness and induction on finite transitions gives the required
finite-prefix simulation. With empty K, a normal Return(v) denotes exactly
the designated source result. Values containing closures/carriers remain
related by their captured graphs, so the same argument applies to any finite
history of their later ordinary uses. This is a direct local derivation of
the reference transition system. It is not yet evidence that runtime source
actually emits those transitions.

## 5. Implementation bridge obligations before freeze

The following must be filled with frozen owning functions and actual branch
coverage; source-form names alone do not discharge them:

| Obligation | Required concrete evidence |
| --- | --- |
| Code construction | Owner-qualified labels from authentic LocalSource reads; all child/binder links; finite nonunfolding traversal. |
| Environment | Distinct resolved binder keys; lexical capture; exact local self cell; no spelling-based fallback. |
| Source interfaces | Original Gamma tag survives Name/result/parameter paths; no runtime thunk-shape role selection. |
| Data/Normalize | Inert introduction for each computation form; exactly the designated consumer at Name/result and Value entry. |
| Call | Callee first; whole argument delayed; receive before force; force/rebind/body/return suffix. |
| Bind/If | RHS cursor advances only after normal return; omitted-else discard; ordinary condition selection. |
| Force | Saved lexical environment plus current execution configuration; no memoization added. |
| Outcome | Completed only after full pending suffix; Unavailable/exhausted have distinct decoders and no partial published value. |
| Literal | Unbounded decimal value retention and exact admitted string decoding; unavailable syntax is explicit. |
| Module startup | Separate source authority and execution owner; not entailed by local Bind or HIR item order. |

Unavailable for Catch/profile/request paths keeps their gates pending. It does
not prove hygiene by absence of successful effectful observations. A static
step budget proves only an explicit exhaustion outcome at its guard; it cannot
identify semantic divergence. Allocation panic/OOM, output formatting depth,
parser/HIR limits and literal resource exhaustion require their own owner
analysis; bounded interpreter fuel alone establishes none of those properties.

### Independent literal owner lemmas

The frozen Oracle is `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
Its `crates/infer/src/lowering/expr_syntax.rs::parse_number_lit` tests that every
character is an ASCII decimal digit, tries i64, then BigInt. Therefore for
every nonempty successfully admitted IntegerLiteral spelling s, its source
value is the nonnegative integer sum of digit(s[i])*10^(len(s)-1-i), without
an i64 bound. Retaining an arbitrary-length canonical decimal string denotes
exactly the same integer: removing leading zeros preserves that sum, and an
all-zero spelling denotes zero. This proves representation equivalence without
requiring arithmetic in the ordinary evaluator; it does not support floats or
invent signed-literal syntax. A bounded decoder must report exhaustion rather
than silently truncate or reject a large admitted integer as a type error.

For a successfully admitted, noninterpolated current StringLiteral, its source
owner retains the complete original token text. The frozen Oracle's
`string_lit.rs::plain_string_lit_text` concatenates StringText and decoded escape
parts, ignoring only delimiters. Its `simple_escape_text` maps n/r/t, backslash,
quote and 0 to their corresponding characters and preserves other escaped
scalars. `collect_unicode_escape_text` parses hexadecimal u32 and uses its
Unicode scalar, or U+FFFD on overflow/invalid scalar. A decoder implementing
these part equations has the same decoded string by induction on parts;
UTF-8 concatenation preserves their scalar sequence. No finite regex test
enumeration is needed for that lemma.

The current grammar, `yu-syntax/src/literal/mod.rs::scan_string_opener_token`,
uses one quote for a normal opener and an entire run of at least three quotes
for heredoc. `accept_string_close`/`is_string_close_source` terminates a heredoc
only at a quote run of exactly that width; a longer run is ordinary string
content. A source-byte decoder therefore needs the same maximal-run rule,
including escaped prefixes, not a generic triple-quote search. Ordinary
delimiter removal and escape scanning are sufficient only after this actual
grammar correspondence is established. Interpolation is a distinct source
constructor and is not claimed supported by this plain-string lemma.

### Frozen operational bridge, first snapshot

The primary froze the four runtime files and authorized inspection. Observed
SHA-256 exactly matched the supplied hashes:

| Runtime file | First snapshot SHA-256 |
| --- | --- |
| `program.rs` | `8362773f4452d78ea61d6400a59aca139b68df4f26be40963486f51814aef4c3` |
| `machine.rs` | `8bcb1cf86994f5b87bbd3a9aad0f52e1ddd2a748c1f747cd5f7041ddea043348` |
| `literal.rs` | `9220d608f6ba5eed97c83204eff06bae3579501d92b6674a430cfabe55cd95f1` |
| `mod.rs` | `79589d787f166cbe1b9a226565a1b5688323a50f34d493d8d05ea6487dd55f42` |

All four are under `tools/inference-playground/src/runtime/`. They were not
yet wired into the playground consumer. This audit covers their callable
private API, not an uninspected main/lib consumer.

**Construction.** `RuntimeProgram::from_hir` reads each actual HirItem::Binding
through `HirModule::local_source`. Its per-source offset plus owner-checked
ordinal gives a globally disjoint code label; every child label is validated
by `source.expression` before storage. It iterates the retained expressions
once to emit one Code per expression, cloning original resolution/parameter
IDs and SourceSite(definition,occurrence,range). Root references map by exact
DefId. Thus literal/Lambda/Name/child source links arise at the actual owner,
not an assumed checker transition. Catch arms retain their source metadata;
their execution remains unavailable.

The preceding iterative Walk searches only source ownership edges. Its
active set brackets parameterized initializers with Leave, and marks a
recursive local exactly when an actual resolved Local Name is encountered
inside that bracket. Successful formation makes those edges a finite
ownership traversal; visited indices prevent duplicate traversal. With no
actual self reference, omitting the unused self cell changes no lookup.
With a self reference, the initializer begins with the actual Lambda wrappers,
whose inert allocation precedes the first possible body lookup. This derives
the exact knot needed by the source, without classifying names from spelling.

**Source tags and executable labels.** The `roles` table in from_hir is built
from every actual Lambda parameter's outer annotation. A parameter Name gets
Execute iff that same original parameter has outer effects; other ordinary
Names get Observe. A supplied RuntimeEvidence entry may reject a mismatch;
it cannot install a contrary role. Runtime Lambda role uses the identical
outer-annotation predicate. Consequently the producer and consumer agree on
the source Gamma tag by construction. A local binding stores the completed
RHS result and therefore has Value tag; a module read returns its materialized
definition value under the separate module premise. CatchBinder has no
ordinary completed introduction while Catch is unavailable. Generic extra
Gamma data is not fabricated: this bridge covers the actual ordinary source
roles just constructed; a richer imported/provider interface still needs its
own original owner.

Each `State::Evaluate` label denotes N rather than arbitrary inert Data.
Evaluate(Literal/Lambda/Operation) constructs data, and Evaluate(Name) uses
consume with that fixed tag. Evaluate(Apply/Block/If) directly executes the
designated computation. This is the typed-core §6 same-context cancellation
of Normalize(Computation,reify(c)); it preserves lexical environment and all
pending suffixes and crosses no receipt/return delimiter. The only argument
introduction is explicit `ExecutableValue::Delay` construction in Callee.
The machine exposes no general Data(App) API, so no claim that such an API
has been implemented is necessary or made.

**Lexical and continuation representation.** `Environment` consists of a
parent arena index and at most one (Binder,cell). `Binder` distinguishes
Parameter/Local/Catch identity types; globals have a separate DefId map.
lookup follows parent indices and compares full IDs. extend always points to
an existing older environment, so lookup terminates. Closure and Delay store
only code plus environment indices. `cells` stores values; recursive knots
are integer indices, not Arc ownership cycles. The actual Frame sum supplies
Callee, ReceiverReturn, ValueEntry, Local, Condition, Root and GlobalRead.
These are the suffixes in R, now traced to actual constructors and consumers.

**Call.** Evaluate(Apply) pushes Callee with argument label and caller lexical
environment and evaluates only the callee. Callee return allocates the Delay
before entering the actual closure. It then allocates a fresh receiver ID,
pushes it to active_receivers and pushes ReceiverReturn. Value entry pushes
ValueEntry and calls execute(delay); that execute switches to the argument
code. Only ValueEntry return binds the formal as Value and enters the body
in the captured closure environment. Computation entry instead binds that
same delay as Computation and enters the body immediately. ReceiverReturn
checks/pop-matches its exact activation and returns the result as Value.
Thus receipt/control order, single entry consumer and no pre-entry prefix
follow from the concrete branches. The fresh integer/control stack is not
full typed receipt/Flow/Observe evidence; that separate hygiene premise is
explicitly unproved.

**Bind/recursion.** begin_local allocates one cell, preextends the self binder
only for an actual recursive initializer, pushes Local(next=ordinal+1), and
evaluates exactly its initializer. Local return fills that cell as Value,
extends the ordinary nonrecursive binder if needed, and calls begin_local
with the saved next cursor. It never reevaluates that initializer. Final
expression evaluation is the no-remaining-binding branch. Recursive source
calls use Evaluate labels and explicit frames. No evaluate/return_value path
calls step, run or itself recursively; begin_local/begin_root schedule a
state rather than executing it. Execution and environment knot destruction
therefore do not recurse through the source call graph in Rust. This does
not certify parser/HIR destruction, allocation-failure handling or formatter
depth outside these runtime structures.

**Force and outcomes.** execute accepts only an existing Delay executable
and switches to its saved lexical code/environment. It does not store or
restore frames, active_receivers, cells or globals. Therefore Force uses the
current machine execution configuration. The Delay-kind check validates an
already source-selected consumer; it does not select a consumer by shape.
consume(Execute) additionally requires the retained Computation interface.
Every step error permanently becomes Stopped(Unavailable), while empty-frame
normal Return becomes Completed. run's caller fuel ending returns
ResourceExhausted without replacing the live state; another run can continue
the same suffix. There is no finite fuel proof of divergence or global
allocator bound. UnhandledRequest is a reserved enum variant with no producer
in this snapshot. Operation calls return OperationConsumer; Catch returns
HandlerEvidence. Neither path supplies a false ordinary/hygiene completion.

### Two minimized actual obstructions and necessary repairs

The unrestricted completed-result claim for the first snapshot is **refuted**,
not established conditional on silently omitting the bad cases:

1. **Taken no-else conditional.** Frame::Condition on true directly evaluates
   the taken arm and lacks a discard suffix when else_branch=None. A selected
   source definition `my main = if true { 1 }` reaches Completed(Integer(1)).
   Source semantics instead discards the body and completes Unit. Both
   successful LocalSource formation and the exact transitions qualify the
   witness; it is a static source derivation, not an executed probe. The
   all-false branch's MissingElseInterface does not protect this taken path.
   Required owner repair: a pending discard-to-Unit continuation for each
   taken no-else body, and Unit for exhausted/no-arm no-else completion.
2. **Heredoc escapes.** literal::string detects a heredoc, strips delimiters
   and returns inner bytes without the normal-string escape decoder. An
   admitted heredoc containing the two source characters backslash+n therefore
   completes with those two characters instead of newline. The current
   grammar's common emit_string_escape handles both modes, and the frozen
   Oracle decoding owner decodes both. Required owner repair: share the exact
   escape decoder after normal/heredoc delimiter extraction, keeping current
   exact maximal quote-run termination.

Both were returned to the primary for its implementation owner. They are
different actual consumer defects, not repeated restatements of a missing
premise. No source-domain narrowing, new representation or stronger typing
assumption repairs either counterexample. The parent local simulation claim
remains open until the fixed bytes and necessary delta correspondence are
inspected and independently reviewed.

### Module initialization: supplied authority and precise remaining premise

The primary subsequently supplied the frozen Oracle specifications
`spec/2026-06-13-computed-fetch-value-restriction.md` (metadata construction and
top-level demand, particularly lines 158–172) and
`spec/2026-06-13-mono-vm-contract.md` (lines 69–91). They prescribe source-ordered
computed binding roots and bare-expression roots, cached materialization of
each instance, and ordinary value definitions only when reached. This is
separate from no-memoization of a delayed argument.

The actual start(selectedDef,execution_roots) API validates supplied IDs and
duplicates; it does not derive correct roots/order from S. begin_root scans
that supplied order, skipping cells already materialized by dependencies.
Root and GlobalRead save one completed result in the exact global cell;
GlobalRead rejects recursive initialization via initializing_globals. This
implements the owner-supplied demand list plus a final explicit observation
of selectedDef. It does not prove the list has every and only the actual
source roots. Bare expression HIR items are currently refused in from_hir.
The needed next premise is the primary-owned source root constructor, not
another proof of local Bind.

The module extension of R relates a global cell to either the same unstarted
definition, that definition's pending materialization suffix, or its saved
completed value. A module reference uses the specification's GetDefinition
operation: return the saved value, or evaluate the original definition under
one pending cache-write suffix and then return/save its value. This is
definition materialization, not Force of a first-class computation by runtime
shape. GlobalRead and Root are its actual consumers. Induction on their
transitions preserves this extended cell relation and implements source
materialization once; each later reference takes the saved-value branch.
The pure lexical `V(Name)` equation in §3 applies after obtaining the lexical
value; the separate module GetDefinition can execute the defining computation
at its specified demand. It cannot be used to make local/parameter Data
lookup execute latent data. In particular delayed argument code does not
even reach a module read before its selected consumer runs.

Static fetch classification must use BindingFetch/Evaluation rather than
source Comp role, inferred effect rows or inference SCC order. In the frozen
Oracle, `lowering/name_ref.rs::lower_name_at`/`lower_local_name` return
Computation::value for bare refs; lambda boundaries similarly remain Value.
An Apply executes a computation; control.rs::build_nested_if_cases uses
Evaluation::Computation. `expr/block_local.rs::lower_block_items` with only
its final expression returns that child's Evaluation, whereas a preceding
binding uses prepend_block. Thus not every syntactic Block is automatically
a computed module root, and a bare alias must not inherit its target's
classification by an invented transitive/SCC rule. This audit does not
adopt old inference/generalization policy; it distinguishes the exact source
startup input required by the current provisional evaluator.

The exact finite mapping for the currently retained source constructors is:

| Retained form | Frozen BindingFetch classification and actual owner |
| --- | --- |
| Unit | FetchValue; tail.rs::unit_expr returns Computation::value. |
| Integer | FetchValue; block_local.rs::lower_number returns Computation::value after parsing. |
| Boolean | FetchValue; block_local.rs::lower_bool. |
| Plain String | FetchValue; string_lit.rs::lower_plain_string_lit calls block_local.rs::string_value. Interpolation is not this form's admitted plain path. |
| Name | FetchValue; name_ref.rs::lower_name_at and lower_local_name return Computation::value, including known local effect slots. Fetch metadata of the target does not rewrite this expression's Evaluation. |
| Operation | FetchValue for the retained resolved operation reference; block_local.rs::lower_resolved_value_ref_at returns Computation::value. Its later Apply is separate. |
| Lambda | FetchValue regardless body; expr/lambda.rs returns Computation::value for the constructed function. Named-parameter wrappers are the same function boundary. |
| Apply | FetchComputation; tail.rs::make_source_app/make_app construct the actual application as Computation::computation. Callee/argument classifications do not make the application Value. |
| Group | The sole child's classification; block_local.rs::lower_paren forwards one expression unchanged, with empty parentheses Unit. |
| Ascription | Child's classification if no registered effect upcast applies; otherwise FetchComputation. tail.rs::lower_type_annotation_tail returns the result of method_body.rs::apply_effect_annotation_upcasts, which folds actual make_app wrappers over the distinct registered upcast definitions for concrete outer annotation paths. |
| Block with no preceding bindings | Final expression's classification; block_local.rs::lower_block_items returns its single final head unchanged. |
| Block with at least one retained preceding binding | FetchComputation; each preceding binding uses prepend_block, and prepend_block unconditionally returns Computation::computation, even for a literal/function RHS and a Value tail. |
| If | FetchComputation for authentic nonempty arms; control.rs::build_nested_if_cases sets Evaluation::Computation at each case. The current source constructor has at least one actual if arm; it does not invent an empty conditional. |
| Catch | FetchComputation for the retained unlabelled scrutinee handler; control.rs::lower_catch_with_scrutinee returns Evaluation::Computation. A labelled catch lambda is a separate Lambda boundary, not the retained Catch form. |

This is a finite structural induction on the outer lowered expression, not
an execution algorithm or inference fixed point. Stop at a Lambda. Forward
Group and empty-bind Block. Each nonempty Block introduces a computation
constructor regardless of the induction values of its children. A Name is a
Value expression even where fetching its target later materializes that
target; thus a chain of aliases creates no recursive classification problem.
Known local effect contents do not change lower_local_name's Value
classification. Ascription requires the *actual registered upcast list* from
its owner: testing annotation.effects.is_some(), an empty effect row or the
child's erased solved type is not an exact substitute. Existing source
annotation/adapter gates remain open where that original input is missing.

The primary's source root constructor can consume this mapping in retained
HirItem source order, without inference SCC traversal. It must independently
establish the current no-upcast premise or supply actual applicable upcasts
before applying the Ascription row. The runtime's unconditional Forward for
Ascription has the same erasure premise; merely selecting it as a root does
not implement a missing adapter. This is a specific original-owner premise,
not grounds for making ordinary source annotations illegal.

### Repaired snapshot: conditional completed-result theorem

The primary supplied and froze this second snapshot. All four observed hashes
match the supplied snapshot; the first-snapshot counterexamples above remain
historical refutations of those original bytes, not of the repaired bytes.

| Runtime file | Repaired SHA-256 |
| --- | --- |
| `program.rs` | `94f65432cb82380cf7ae1f1aa1ade92300ccff17c88dd465c965642b89bd5365` |
| `machine.rs` | `92de4f5cbbcfae07d19e518c6f151fbaceab9496ac1985be6b600054c826af3a` |
| `literal.rs` | `8dfd2538070a3854c7a56dd8631bcae94999011bb8134cee7e71fb6a32ae46a1` |
| `mod.rs` | `79589d787f166cbe1b9a226565a1b5688323a50f34d493d8d05ea6487dd55f42` |

**No-else repair.** Frame::Condition now pushes DiscardToUnit before entering a
taken body when else_branch=None. Its return consumer constructs Unit using
the original conditional SourceSite. If that body does not return normally,
the discard continuation remains pending and cannot publish Unit early.
Exhausted false conditions now construct Unit; the no-arm/no-else branch also
constructs Unit (though successful source formation supplies actual arms).
Explicit-else conditionals retain the selected body result without this
continuation. Add to R the clause
`plug(DiscardToUnit(site)::K,c) = plug(K,c >>= (_ => Return Unit))`.
The body induction hypothesis followed by that exact return consumer proves
the omitted-else source equation for every normally completed branch. This
discharges the first concrete counterexample and all its nested ordinary
continuations, rather than patching only a literal output case.

**Heredoc repair.** literal::string now chooses only the delimiter extraction
branch before one shared scalar/escape loop. Both modes use the same exact
escape equations recorded in the literal lemma. Successful HIR formation
rejects StringInterpolation in local_source.rs's StringLiteral branch, so
the stored raw spelling is on the admitted plain path. The quote-run opener
and full current-grammar terminator entail that strip_prefix/strip_suffix
remove only that literal's delimiters; longer interior quote runs remain in
inner and are copied. The loop's invariant is that result is the decoded
prefix of the consumed source parts, with the unconsumed suffix untouched.
Ordinary scalars and simple escapes preserve it immediately; the Unicode
loop's checked accumulator equals the parsed u32 or is None exactly after
overflow, yielding the same scalar/replacement equation. At exhaustion of
inner it gives the whole source string. This discharges the second concrete
counterexample without changing the original arbitrary-decimal integer lemma.

**Ascription change.** from_hir now emits AscriptionPending(child), not
Forward(child), for each actual expression ascription. evaluate returns
AscriptionEvidence at that node. execution_roots likewise returns that
explicit unavailable result when its classification walk reaches the node.
Thus no completed execution silently erases a reached expression ascription.
The source form and child are retained; this is a pending implementation
consumer, not a claim that such source programs are illegal. Source-to-machine
completeness through that pending node remains unproved, even where a source
ascription would happen to erase. It is not closed by the completed-result
direction proved here.

**Source root constructor.** RuntimeProgram::execution_roots now iterates its
definitions array, follows Forward and zero-binding Block to their child,
stops at Lambda and other Value forms, classifies Apply/If/Catch/nonempty Block
as computation, and returns AscriptionEvidence rather than guessing. Each
forwarded edge is a proper original source child, so the walk terminates;
there is no recursive definition traversal. Applying the finite fetch table
above by induction proves the classification for every successful walk,
subject to the declared-result annotation premise below. No effect support,
Name target fetch or SCC order is inspected.

The actual ordering bridge is now established at immutable module.rs:
lower_module_with_counters enumerates root.children into plans in source order,
then iterates those plans and pushes one item each; namespace construction
does not reorder the plans. Runtime from_hir iterates items in that order and
appends definitions in that order. execution_roots takes a subsequence in
the same order. Therefore a successful execution_roots result is the actual
source-order computed-binding demand subsequence for this retained inventory,
under the same annotation premise. It does not claim handling of bare
top-level expressions: from_hir explicitly refuses those items, preserving
that unsupplied source case as unavailable.

**Effect declaration placeholders.** from_hir now permits only nonempty
HirItem::Error lists whose every ID is both in the original source effect
declarations' placeholder_errors and has actual HirErrorKind::UnsupportedItem.
The immutable source owner module.rs attaches those IDs only while processing
that same ActDeclaration plan, and source_annotation.rs::declarations supplies
its declaration after recovery/shape checks. Other unsupported/error items
cannot pass this guard. Skipping those declaration placeholders adds no
executable body and preserves binding order. This supplies the real root
inventory bridge rather than ignoring arbitrary HIR errors.

**Inert selection.** definition_named scans source binding names to choose one
exact DefId or returns MissingDefinition/AmbiguousDefinitionName. It executes
no body and changes no machine state. This is an external observation selector,
not runtime re-resolution of source Names; runtime Names still use original
resolved IDs. The theorem fixes its selected DefId after this lookup, so it
does not make source semantics depend on the CLI selector spelling.

**Theorem for repaired completed paths (conditional derivation).** Fix S,
Gamma and original identities as in §1. Suppose all declaration-level result
annotations on reached code have their actual admitted erasure/no-applicable-
adapter premise, and suppose `roots = program.execution_roots()` succeeds.
For any `start(selected,roots)` machine, every finite ordinary execution that
actually returns Completed(v) simulates the source computed-binding roots in
source order, followed by observation/materialization of selected, with v
related to the designated source result. Every earlier actual Running prefix
preserves R, extended by global materialization and DiscardToUnit. The
relatedness preserves the exact closure/carrier code and captured binder
graph, so it applies again to every later ordinary use which the evaluator
actually completes. The original local call/Bind/Force/role claims hold in
each such execution. An equal independently proved root vector can replace
the constructor output; arbitrary caller vectors cannot.

Proof: initialize all global cells in the same source-unmaterialized state;
apply the first-snapshot constructor/control/environment lemmas, the two
repaired cases, and the proved successful-root classification/order bridge.
Root/GlobalRead transitions maintain the same unstarted/pending/completed
global cell and single cache-write suffix. R preservation follows by the
concrete State/Frame cases already traced, including the newly added
DiscardToUnit case. AscriptionPending, OperationConsumer and HandlerEvidence
have no outgoing successful source-execution transition and hence cannot
occur as executed nodes in a Completed derivation. They remain explicit
unavailable exits, not invented normal returns. Empty pending suffix or a
completed selected global is therefore exactly the source observation named
by the theorem. Induction on the finite actual run proves the conclusion;
no type solution, request handling, inference soundness or totality premise
is imported.

This is the completed-result direction of the original operational objective,
with its original admitted-annotation premise exposed. It is not a new theorem
obtained by declaring the unsupported source forms absent. The stronger
source-prefix completeness statement in §1 remains conditional on every
activated consumer being implemented; reached Ascription, operation execution
and Catch still have explicit missing operational owners. The repaired code
does not establish that source-completeness direction for those cases.

### Annotation-owner premise still open at the second snapshot

Expression AscriptionPending is not a proof for declaration annotations.
LocalSource::annotation() and LocalSourceBinding.annotation are retained
separately and are not consumed by runtime compilation or execution_roots.
The frozen Oracle's expr/lambda.rs routes declared result annotations through
method_body.rs::connect_type_method_result_annotation (including the no-
remaining-parameter case); that owner calls apply_effect_annotation_upcasts
before returning the body. If a real registered upcast applies, a declaration
annotation can therefore change executable code/Evaluation even though no
LocalSourceForm::Ascription node occurs. Pure outer parameter-role selection
also does not prove all nested/result annotations erase.

Consequently, **at this second snapshot the unconditional claim for all accepted
annotated completed inputs remained open** at that annotation/adapter owner. The exact
missing premise is either (a) an original-source proof that no applicable
executable adapter exists for this admitted playground source environment,
covering declaration as well as expression annotation positions, or (b) its
actual retained adapter construction and corresponding runtime consumer.
No concrete counterexample with an actual applicable source upcast instance
was constructed in this bounded delta; absence of that instance is not proof
of (a). Merely adding an annotation-based rejection would not discharge the
original ordinary-source requirement. The primary retains that parent gate
and its implementation decision; this note neither adopts a source restriction
nor certifies whole ordinary execution closure.

### Owning registration evidence: no applicable upcasts in this envelope

The primary supplied a complementary source-inventory result locating the
actual missing producer premise. The following bounded owner inspection
independently grounds its application; it is not a third equivalent assumed-
erasure lemma. The source inventory changes what is known about the same
original input envelope, rather than imposing a new annotation restriction.

**Registration invariant.** At the frozen Oracle, CastTable::new is Default
with an empty map (`casts.rs:13–20`); AnalysisSession's initialization installs
that table (`analysis/session/lifecycle.rs:60`). The complete production
`insert_effect_up` call inventory has two callers: generated ErrorDecl up
helpers (`lowering/body/error_decl.rs:365–397`) and seeding supplied imported
`poly.cast_rules` (`analysis/session/lifecycle.rs:169–181`). The lookup
`effect_up_defs_for_target` (`casts.rs:121–130`) returns only stored effect_up
entries whose target matches; it has no built-in or type-directed rule that
manufactures a callable on an empty table. The mutation body of insert_effect_up
only appends the supplied registered rule to that table. Tests are not used
as production registration evidence.

**Original-source exclusion of both producers.** Successful current runtime
from_hir accepts only authentic retained bindings plus the precisely checked
ActDeclaration UnsupportedItem placeholders described above. HIR plan_root
(`module.rs:1270–1318`) classifies all nonbinding/nonexpression items as
UnsupportedItem. Its direct-expression form is refused by runtime from_hir;
its non-Act unsupported items cannot satisfy the exact declaration-placeholder
guard. Therefore ErrorDecl, impl, cast and import root forms cannot reach
this constructor. LocalSource::block accepts only preceding BindingStatements
and a final expression, and the expression constructor sum has no nested
ErrorDecl/impl/import registration action. Parameterized local initializers
only introduce their existing named Lambda wrappers. Thus no allowed nested
source action can reach the ErrorDecl helper-registration caller either.

The admitted Act carrier is not such a helper: source_annotation.rs::declarations
(`133–307`) creates SourceEffectDeclaration/SourceOperationDeclaration entries,
family and operation namespace entries, and parsed annotation signatures.
Its members must be declaration-only BindingStatements without BindingBody;
it emits no generated executable up helper or cast rule. module.rs's Act
placeholder association records error IDs, not executable registration. This
distinction is established from the actual constructor, not its name.

For imports, SemanticImports (`module.rs:109–116`) is an opaque unit wrapper
with only empty() available, and lower_module_with_counters takes `_imports`
without reading an imported/poly payload (`923–925`). The current runtime
program is built from that immutable HIR and has no compiled/poly prefix
field or import seeding operation. The candidate's solve_mode preflight
(`shadow_apply.rs:271–310`) accepts the same retained-source/declaration-error
inventory and then constructs its native candidate batch/session; it does not
import frozen Oracle poly cast_rules. The CLI's prepare passes the actual
SemanticImports::empty() input. SyntaxEnvironment::empty() alone would not
prove this property; the semantic input and producer exclusions do.

Start with the empty table. Induct on the permitted original source
construction/registration actions: neither insertion caller is reachable,
so the relevant stored effect_up inventory remains empty. Target lookup
therefore returns [] for *every* annotation target path, not merely for the
examples inspected. In method_body.rs::apply_effect_annotation_upcasts the
up_defs loop is then empty, hence the returned Computation is the exact
original body, including its Evaluation. This applies equally to expression
ascriptions and every root/local/function declared result annotation routed
through connect_type_method_result_annotation. These annotations add their
static endpoint constraints; their absence of an executable adapter is now
derived, not assumed. Outer parameter roles retain the independent charter
§21 source predicate and are not erased by this lemma.

This establishes the previously missing no-applicable-upcast premise for the
original validated constructed-program envelope. It does not show that arbitrary
imported source environments have no casts, retire their adapter requirement,
or certify annotation type checking, effect profiles or handler permissions.
Adding a future ErrorDecl/helper/import registration constructor would change
this dependency and require its actual adapter path before reusing the lemma.

### Final snapshot and constructed-program ordinary simulation

The primary then froze the final runtime with source Ascription mapped to
Forward. Observed hashes match all supplied hashes:

| Runtime file | Final SHA-256 |
| --- | --- |
| `program.rs` | `753380b0697cf7bd5c484cfda149cd339ac2ef2908ba0394f22133ec43c7c0bb` |
| `machine.rs` | `4cc1897ca2acf0ec6efacbeba074fd155c4cb0482b7b78543b7b66f6a3e73b9e` |
| `literal.rs` | `8dfd2538070a3854c7a56dd8631bcae94999011bb8134cee7e71fb6a32ae46a1` |
| `mod.rs` | `79589d787f166cbe1b9a226565a1b5688323a50f34d493d8d05ea6487dd55f42` |

from_hir's Group/Ascription arm now emits Forward of the actual checked child;
the owning no-upcast lemma justifies that executable erasure and unchanged
Evaluation for declaration annotations. execution_roots follows Forward for
both forms and so consumes the now-established source fetch classification.
The temporary AscriptionPending consumer/error is removed. No role/Name
consumption predicate changes. The repaired conditional/decoder and all prior
ordinary frame cases retain the preceding proofs.

**Constructed-program theorem (unreviewed constructive derivation).** For
every authentic successfully formed S in the current from_hir envelope and
every selected definition d, let p=from_hir(S,evidence) succeed and let
roots=p.execution_roots() succeed. Fix all original binder identities,
source annotation/interface tags and the source environment from §1. For
every finite sequence of calls to run/step on p.start(d,roots) that actually
returns Completed(v), there is the same ordinary source execution of its
computed binding roots in source order, with cached definition
materialization and final observation of d, returning a related value v.
All its Running prefixes preserve R. Returned closure/carrier values retain
their original source labels, lexical references and entry roles, so the
same result applies to each subsequent ordinary invocation/force that is
actually completed. The statement has no additional assumed annotation-
erasure/upcast premise: that premise follows from the original source owners
just proved. It preserves the original completed-case scope and quantifiers.

Derivation: discharge the preceding conditional completed-path theorem's
last annotation hypothesis by the no-registration invariant, then apply the
actual Forward/source-fetch delta. The same invariant proves the exact
source-root classifier for annotations; module source-order construction and
single materialization prove the initial and global steps. Extend R through
Forward as an administrative step preserving code meaning, then use its
already established call/Bind/Force/conditional/lookup cases. Operation
execution/Catch cannot occur in an actual Completed trace because their real
consumers stop Unavailable. This derives what this ordinary machine completes;
it does not declare those source forms invalid or prove their future missing
execution. Ordinary source prefixes whose constructors/consumers exist match
the same transitions until normal completion, caller fuel pause, explicit
unavailable operation/handler evidence or a source dynamic error. No
unavailable/pause result is equated with a source value or divergence.

The actual CLI consumer was narrowly inspected at
`tools/inference-playground/src/lib.rs::execute`: it calls prepare, from_hir,
definition_named, the actual execution_roots, and start with *that exact*
vector, then publishes a value only after RuntimeOutcome::Completed. Thus
the complete root-vector hypothesis is enforced at the consumer, not supplied
by a prose checker. Its current inspected lib.rs hash is recorded below;
the primary retains final consumer integration/verification ownership.

This establishes the local constructed-program ordinary execution argument
and its exact source bridge as an unreviewed derivation. It does not promote
its own proof status or close full source completeness, effect hygiene,
complete effectful Call, native inference soundness/principality or production
cutover. Operations/Catch/typed Observe/Flow/resumption still require their
original executable owner evidence; ordinary completion supplies none of it.

## 6. Dependencies, checks and handoff

SHA-256 recorded before derivation; immutable source dependencies had no diff
against the pinned HEAD when read:

| Path | SHA-256 |
| --- | --- |
| `crates/yu-hir/src/module.rs` | `70678eb23bf50813f77b7be3f90442c3b3faea2c754593cf6f35d3f7c0fcf645` |
| `crates/yu-hir/src/module/local_source.rs` | `53e3b324cac9364ac7313e44f9cc739d876427c9018df2a22e5a88119c46c1f9` |
| `crates/yu-hir/src/module/source_annotation.rs` | `f8f8a1934d9961d443b2a0b55a79aa3272ec7cd820f7a40d9bd6217f3456ae38` |
| `crates/yu-hir/src/shadow.rs` | `676f003fb641a060e497c47ceb406a2fd1814a34d621758c34fc958c3b807612` |
| `crates/yu-solver/src/shadow_apply.rs` | `270ee70b331e4095f404fafafdf0731b57dd451c130cdf251aea2b5944d7cc6c` |
| `tools/inference-playground/src/lib.rs` inspected consumer snapshot | `89ee753e784203225e9d2ff51d1ce85fcf42f09065416d98661a64fe31f1a832` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-source-call-scheduling-choice.md` | `7b2d2556f4b6a93d7beb73a78f476bfea7d0f94de0c5f77649f6cd15ff69a530` |
| `notes/design/2026-10-02-ordinary-computation-semantics-package.md` | `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `crates/yu-syntax/src/literal/mod.rs` | `d54b4ef01cb3c9d46048b5638f9837eb050816a5e7edd35460f20cf1e557fd40` |
| `notes/progress/2026-10-15-conditional-without-else.md` | `4d02726404e669e7eba396f86a075598408fe71e370307ce6a8bfaa0721f6634` |
| Oracle `crates/infer/src/lowering/expr_syntax.rs` at `a58eefc31e22141574b6f20c6a5748151c6d79f1` | `3390673e476923c817512cc4f0705a71245f530143e6e814cdd03ffaa5da5085` |
| Oracle `crates/infer/src/lowering/string_lit.rs` at the same frozen commit | `d5d1bb1381687950d3f0e3cf1184d9e45ac3748d5f0f173b1d17266f0decbf66` |
| Oracle `spec/2026-06-13-computed-fetch-value-restriction.md` | `b3b53fd74256a212b06b8cfbdd8a2812d84f81ba5cc59d8fe37f0cdeec3bbac9` |
| Oracle `spec/2026-06-13-mono-vm-contract.md` | `9f88e1e21387ebe0ef42e2d857fcd37ba52d51acd1962cdb3cb6b80666819388` |
| Oracle `crates/infer/src/lowering/name_ref.rs` | `699c7dc84a2b4889355ffe9cd23b3e871c295957dbcb3fbad96ee9ee36470ede` |
| Oracle `crates/infer/src/lowering/expr/block_local.rs` | `661386fe559d8e207a9597962cfee3c11f05f21aa2888e22b2c0143825051898` |
| Oracle `crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| Oracle `crates/infer/src/lowering/expr/method_body.rs` | `3319db30fd3d6771eea156a2b902372c59db75ce1e27f64fcb44d987c3e52b74` |
| Oracle `crates/infer/src/lowering/control.rs` | `4253ea5e94b671271fe64b5d1956bb961215e2e5c1278c56d88f0c67caaa7963` |
| Oracle `crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| Oracle `crates/infer/src/casts.rs` | `4ec3e0ee44b398e300de7719cccb1f68c8dfec01a65cad6b5ed519e7f7c4c9a4` |
| Oracle `crates/infer/src/analysis/session/lifecycle.rs` | `196b0f1eeef891e3547bf77e3d00f5f0574399e24bc59c4697219df6ff93d5ed` |
| Oracle `crates/infer/src/lowering/body/error_decl.rs` | `93533e0f80101b581f555e93c8a3044052925f8ce5294540ccd7708bf5ca6a5d` |

Checks: read-only source/rule inspection, baseline/branch/status read,
source dependency diff read, all three frozen runtime hash comparisons, final direct
HIR/runtime SHA-256 recheck, and note whitespace/fence inspection (no trailing
whitespace, two balanced fenced blocks). No Cargo, test, executable
probe, network, Git mutation or child delegation. One proof producer; no heavy
process or performance sample. First pass budget: 30 minutes, followed only
by the primary-authorized bounded frozen-source bridge. No pair of failed
proof variants has repeated an unchanged premise.

Requested runtime: prover, GPT-6.1 Sol/high under normal role routing. Actual
model/effort metadata is unavailable to this leaf and is recorded unknown;
configuration inspection is not evidence of effective runtime settings. No
Astra escalation requested or claimed.

Next action: the primary assigns fresh independent review of the final frozen
constructed-program ordinary simulation, including the source registration
exclusion and actual root consumer. Effectful operations/handler/hygiene and
inference parents remain separate open work.

Commit packet (research checkpoint only): exact leased path
`notes/theory/2026-10-15-playground-ordinary-runtime-simulation.md`; baseline
`cdfdb58bb244fecf0c895a6a1d65b2bdee06548c`; unchanged baseline HIR/authority
dependencies above; all three runtime snapshots recorded separately;
unreviewed constructed-program ordinary completed-path simulation, actual
no-upcast/root-constructor/consumer bridge, no effectful or inference parent
closure; checks above; proposed
message `research: bridge repaired playground ordinary runtime simulation`.
Primary/curator deltas: record both source-qualified original defects and their
repaired consumer derivations, successful-root construction/order bridge,
source-owned discharge of the declaration-annotation premise and explicit
pending effectful consumer completeness. Preserve inference, hygiene and
production gates; promote this local theorem only after independent review.
