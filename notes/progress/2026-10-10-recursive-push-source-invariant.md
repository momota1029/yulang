# Actual source recursion carries PUSH and full left POP/PUSH pairs

Date: 2026-10-10
Status: source construction/admission independently reviewed; two minor corrections applied; compiler execution unrun
Role: researcher, source-construction producer
Frozen successor: `e3ddf9f19e08be74a8467a61b5415244f6f5ac0f`
Pinned Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Authority: selected annotation policy and existing Simple-sub/source hygiene contract
Owned output: this note; scratch fixtures/probe under
`/workspace/scratch/15155572c47b/recursive_push_source/`

## Result

Actual paired expression ascriptions construct a recursive PUSH component and
put an actual concrete `Pos::Row([io])` lower into it. No recursive source
binding, synthetic effect seed, same-variable weighted edge, callback scheme
instantiation, or extra source restriction is needed. A nested version supplies
both a PUSH loop and a POP loop and gives exact nonzero leading-POP and active-
PUSH counts on one concrete retained lower. The source-construction/admission
argument below therefore rules out the proposed universal **debt-only** source
invariant. It does not infer that result from a finite trace.

For these two exhibited programs, the complete recursively reachable
nonterminal contextual component before generalization is left-only, with one
attachment ID and fixed family `{io}`. This is stronger than saying that four
selected primitive edges happen to be left-only: every possible incoming
Function port of these particular programs is classified below. Thus the
existing exact left-word/full-pair observer decision procedure can be applied
to these actual recursive PUSH sources, subject to its own proved hypotheses.
This note does not establish that all source programs share that separation.

This is a direct constructor and admission derivation against the pinned
source. Neither program was parsed or run here: the session has no retained
Oracle harness and no Cargo/Rust compiler. No successful public type,
production acceptance, runtime result, or global termination claim follows.

## Minimal nonrecursive source

```yulang
act io:
  pub ping: () -> ()

my witness = ((\x -> io::ping ()) as (int -> [io; 't] ())) as (int -> [; 'e] ())
```

Expression ascription uses **`as`**, not `:`. Pinned
`parser/src/expr/scan.rs:233` selects `ExprLedTag::As`, and
`parser/src/expr/tail.rs:208–223` makes its `TypeAnn` child. A colon spelling
would be a different source construct and is not evidence for this route.
`annotation/builder.rs:120–143,151–188,271–295` reads the parenthesized Function,
its return row, and the symbolic tail after the semicolon. There is no wildcard.
`['e]` would instead place a variable among the row items; `[; 'e]` is the
required variable-only row tail.

Let `V` be the actual provider lambda's Value variable, `Q` its body Effect,
and `K+` its actual positive Function shape. Let `A+/A-` be the first annotation
pair and `B+/B-` the second pair.

The first ascription is a **nonparameter** annotation. Its canonical inner
Effect owner is a fresh variable `r`, not automatically the written `'t`:
`annotation/constraints.rs:450–470` allocates `r`,
`:637–655` connects `r` and the written tail `t` by identity edges, and
`:590–598` registers the declared source fact `(r,i,{io})`. The fresh
subtraction ID `i` is allocated by `:657–691`. The second return row takes the
variable-only branch `:430–439` and uses its one symbolic Effect variable `e`
directly, without another attachment ID.

The annotation pairs therefore have these relevant ports:

```text
A+ = Fun(int-, NegRow([],Top), Stack(r+,PUSH_i[{io}]),
         NonSubtract(unit+, POP_i / filter{io}))
A- = Fun(int+, Bot+, filter{io}(r-), unit-)
B+ = Fun(int-, NegRow([],Top), e+, unit+)
B- = Fun(int+, Bot+, e-, unit-)
```

These are produced by `annotation/constraints.rs:363–389,395–401,424–470,
492–500`. The declared fact is an annotation authority record, not the concrete
seed. The actual seed is supplied separately by the operation producer.

## Same actual Value owner; no intermediate scheme or drain

`lowering/expr/tail.rs:53–82` lowers an expression `TypeAnn` by calling
`connect_computation_detailed` on `acc.value` and returning the same
computation. `lowering/expr/block_local.rs:18–21` preserves that computation
through parentheses. `apply_effect_annotation_upcasts` does not change this
route: `lowering/expr/method_body.rs:1822–1826` only discovers target paths when
the annotation's **outer** form is `AnnType::Effectful`; both annotations here
are outer `AnnType::Function`.

Consequently both ascriptions use exactly `V`, with no generalized use between
them. `annotation/constraints.rs:132–143,223–252` emits

```text
K+ <: V-                          actual lambda producer
A+ <: V-    and    V+ <: A-        first paired ascription
B+ <: V-    and    V+ <: B-        second paired ascription.
```

Ordinary bound replay compares every available positive Function lower with
both annotation uppers. In particular `A+ <: B-` and `B+ <: A-` occur at
identity. Their return-Effect children normalize to the primitive edges

```text
r --left PUSH_i[{io}]--> e
 e --identity------------> r.
```

The second edge checks/registers the original `{io}` negative wrapper before
its weight is consumed. Its retained context is identity. Lower wrapper
normalization is `machine/propagate.rs:11–24`; upper wrapper checks and
normalization are `:36–60`; Function children are `:207–271`.
The additional `r <-> t` identity aliases preserve written-tail correspondence
without identifying their allocation identities.

Unlike the earlier local `my a = f` route, this source has no local binding
whose generalization could drain before the second annotation is built.
`lower_type_annotation_tail` performs no `drain` or scheme snapshot. Both
ascriptions are part of one initializer. The operation and actual lambda may
still have queued reference-resolution work, but their source producers and
both annotation pairs have been constructed before the enclosing solve/drain.
The resolved Act reference also has an eager producer: `name_ref.rs:7–37`
calls `lower_resolved_value_ref_at`, which invokes
`constrain_act_operation_ref` at `expr/block_local.rs:990–1047,1066–1091`.
It constructs the operation's positive signature and constrains the reference
Value immediately, independently of the queued ordinary scheme resolution.
Pinned `machine/entry.rs:970–984` drains FIFO with `pop_front`; an infinite
newly generated tail of work cannot overtake already enqueued primitive work.
No earlier nonterminating local-generalization stage is needed to reach the
circuit.

## Actual concrete Effect seed and its complete route

The source has an **Act** family, not only `type io`.
`lowering/body/act.rs:26–31` registers the family; `lower_act_operation_type`
and `act_operation_signature_type` at `:147–193` build the operation signature.
`body/signature_helpers.rs:217–256` inserts the resolved `io` family as an
actual return-effect item. `lowering/signature_effect.rs:78–107` lowers that
positive return row to

```text
C = Pos::Row([Pos::Con(resolved_io,[])])
```

rather than an annotation PUSH or a declared subtraction fact.
The ordinary call `io::ping ()` has a real application demand and fresh call
and result Effect variables (`expr/tail.rs:543–563`); its call return Effect
is forwarded into the application result Effect (`:621–630`).
The operation is not a local `Def::Arg`, so the unannotated-local-call special
attachment producer returns the bare call Effect (`:746–762`). It supplies no
additional `SubtractId`. The eager `constrain_act_operation_ref` route already
supplies the operation's positive callable signature at this source occurrence.
Ordinary reference resolution may also supply its scheme; the monomorphic
nullary family item has no annotation POP to erase this concrete effect.

The operation reference may use the ordinary top-level generalized scheme
instantiator. That is a finite source occurrence (two in the nested fixture),
not an absent scheme operation. Any ordinary signature variables can freshen
at that occurrence; the nullary `io` Row remains a concrete item, and this
operation signature contains no contextual attachment ID to freshen. The
claim that no callback scheme is invoked concerns the same actual lambda
Value `V` receiving the two ascriptions.

`lowering/expr/lambda.rs:349–365` creates `K+` with the actual body Effect `Q`
as its return-Effect port. Comparing `K+` with `A-` gives

```text
Q+ <: filter{io}(r-)   ->   Q+ <: r-
```

and comparing `K+` with `B-` gives `Q+ <: e-` at identity. Hence the concrete
`C` reaches both `r` and `e` by ordinary lower/upper replay. The filter accepts
the actual resolved family `io`; it also accepts the active stack's `{io}`
family. `bounds.rs:3174–3255,3285–3360` performs current checks and retains
future-lower checks. No invocation of the callback variable, no synthetic
concrete input, and no caller-generated higher-order demand are needed.

Generic `Neg::Var` insertion retains the whole positive Row
(`propagate.rs:157–169`). It does not first flatten the Row into a terminal
Value constructor. Furthermore, even the row's `Pos::Con(io,[])` is not a
terminal erased constructor when its Act path is registered:
`entry.rs:1783–1816` excludes registered effect-family paths from that rule.
A plain `type io` cannot be assumed to have this Act registration
(`annotation/constraints.rs:829–831` registers only Act declarations). The
whole-Row seed already suffices; the Act declaration makes the concrete-family
and filter correspondence explicit too.

## Exact recursive PUSH admission

The primitive endpoints `r` and `e` are distinct allocations. The first direct
`r <: e @ PUSH_i` child is admitted at its exact canonical key; its nonempty
support cannot be suppressed by a weight-empty alias. The direct `e <: r`
identity child is likewise admitted. A later duplicate may refer to its first
surviving record. Nothing in this argument needs a compressed self-edge or a
larger-count alias variant.

For any retained concrete lower `C <: r @ PUSH_i^k`, replay with those two
unchanged primitive uppers yields

```text
C <: r @ PUSH_i^k
  -> C <: e @ PUSH_i^(k+1)
  -> C <: r @ PUSH_i^(k+1).
```

The seed supplies `k=0`, so every natural count occurs. This is a source-
derived inclusion subderivation; other source consequences need not equal
this progression.

Every admission owner relevant to this recurrence has been checked:

- `entry.rs:1092–1117` omits equal **Var–Var** endpoints. `C` is a Row, so the
  concrete return to the same Effect owner is not omitted.
- `bounds.rs:4274–4317,7204–7233` support-subsume a lower only when its positive
  endpoint is `Pos::Var`. They cannot support-subsume `C` at two different
  PUSH counts.
- `bounds.rs:3814–3830` makes evidence-only frontier-path skipping require
  both endpoints to be Vars. None of these concrete replay steps qualifies.
- `entry.rs:1783–1816` does not erase Row-to-Var weights.
- `bounds.rs:630–739` stores an exact bound semantic key, replays new semantic
  insertions, and does not change the weight into a support key.
- `bounds.rs:3450–3470,3620–3645` composes the concrete lower with its upper;
  `constraints/mod.rs:3595–3612` preserves these exact counts. The right
  context is identity, so directed mix does not change this left word.
- `bounds.rs:4523–4544,4701–4727` extrusion returns the original endpoint IDs
  and lowers levels in place. It does not equate `r` and `e` or copy away the
  recurrence.

Filters are consumed but their checks remain retained. Along the recurrence
only Var uppers are compared with `C`; no negative concrete-head consumer
splits the Row or changes `{io}` into a residual family. The family is fixed.
The natural-count argument is distinct from Oracle's finite-width `u32`
arithmetic, including pending-count saturation and ordinary active-count
addition, and proof-store resource failure.

## Nested actual source admits full pairs, including mixed replay parents

```yulang
act io:
  pub ping: () -> ()

my witness = ((\x -> { io::ping (); \y -> io::ping () }) as (int -> [io; 't] (int -> [; 'h] ()))) as (int -> [; 'e] (int -> [; 'e] ()))
```

The first annotation allocates the same kind of boundary-owned outer `r` and
one ID `i`, and uses a distinct direct symbolic inner return-Effect `h`.
The second annotation intentionally shares one symbolic `e` across its outer
and inner return rows. Its variable-only rows allocate no ID.
The paired `A+ <: B-` comparison now normalizes the actual positive returned
Function's `NonSubtract` with a **left prefix** POP and then descends into its
return-Effect. The primitive source component is

```text
r --left PUSH_i--> e       e --identity--> r
h --left POP_i---> e       e --identity--> h
r --identity----> t       t --identity--> r.
```

The provider's outer operation seeds `r/e`; its actual returned inner lambda
has its own operation Row lower, which seeds `h/e` via its comparisons with the
original and added inner Function uppers. These are actual registered effect
contributions. They are not lower inputs inferred from the annotation alone.

Let `(p,n)` denote the exact left word `POP_i^p PUSH_i^n`. The right word here
is identity. From a concrete Row lower at `h` the primitive path

```text
h --POP_i--> e --identity--> r --PUSH_i--> e
```

gives `(p,n)=(1,1)` at `e`. `POP PUSH` does not cancel. Repeating
`e -> h -> e` first and `e -> r -> e` second supplies every pair
`(p,n)` in `N^2` at `e`, using its identity seed for zero cases. These concrete
records bypass exactly the same Var-only guards checked above. Raw pending
and active counts can both be positive; replacing this with signed depth
would delete a real source distinction.

The previous bounded symbolic callback trace had no logged mixed parent.
That observation does not contradict this witness. Its source supplied no
corresponding concrete Row seed. Var-only compressed aliases may be dropped
as equal-endpoint consequences, support-suppressed, or retained only as
frontier evidence; the concrete rows here propagate along the surviving
primitive bounds independently. This is an explanation of why a graph walk
alone did not certify its earlier admission, not a claim about unseen events
in that old trace or a proof that its suppression is sound.

## Complete recursive grammar of these exhibited sources

For these programs the full **pre-generalization** nonterminal contextual
component stays in the left-only exact-word class, for source reasons:

1. The finite nonterminal Value shapes are the actual provider lambda(s),
   the two annotation Function pairs on the same source Value owner, and the
   operation-signature/application-demand Functions. The operation comparisons
   occur at identity and have no contextual feedback from `r/e/h`.
   Their comparisons are at identity, except the original nested positive
   return `NonSubtract`, which gives a single left POP for the corresponding
   inner annotation comparison. The Effect component never points back into
   a Value Function port.
2. Swapping the latter context on its argument Value port ends at the nullary
   `int` constructor. The terminal canonicalizer erases that right POP before
   a retained contextual bound is created. Annotation argument-Effect children
   have positive Bot and are canonically trivial.
3. Actual unannotated provider lambda(s) have negative Bot argument-Effect
   interfaces. Their `both_from_right` branch executes only at identity,
   so both produces identity. Ordinary operation calls execute at identity
   too. No right debt is fed into the recursive Effect component.
4. The only concrete effect lower is a nullary `io` Row. Argument and lambda-
   creation Effect variables are exact-pure upstream sources; they do not
   receive a reverse alias from `r/e/h`. Empty negative rows on those pure
   owners cannot consume an `io` lower in the recursive component.
5. The recursive owners have Var uppers and the consumed `{io}` filter, not
   negative concrete row heads. There is no residual gamma allocator or
   changing active family on this component. There is no parameterized effect
   payload, generalized callback use, intrusive copy, handler, or recursive
   binding that could add another incoming four-port comparison before the
   enclosing drain finishes.

Additional admitted compressed Effect aliases do not weaken these facts:
left-word composition of two right-identity contexts remains right-identity;
all resulting words use the same fixed source ID/family. Thus the actual
recursively reachable grammar is a finite left-word replay grammar over the
source owners, with exact full `(p,n)` states. The original variant generates
unbounded active PUSH; the nested variant generates full-pair growth. Both
fit a theorem for arbitrary left-only independent-child grammars. This does
not close full general mixed recursion or establish a global source
restriction: changing the Value ports, symbolic argument Effects, body Effect
annotations, recursive call structure, or future uses can change the incoming
context classification.

## Exploratory right-context falsifier remains separate

Scratch `right_debt_push_scc.yu` uses a curried version of the earlier actual
Value-debt circuit and writes the same formal symbolic tail `'t` in the body
result annotation `[; 't] 'r`. It additionally reannotates a callback extracted
from the first formal tuple, before the debt-bearing second formal is used.
`connect_type_method_result_annotation` at
`expr/method_body.rs:1715–1749` reuses the formal annotation maps, and
`annotation/constraints.rs:504–520` connects the actual body Effect to its
variable-only tail in both directions. This is an actual potential route
returning a right-context call Effect to the original PUSH owner.

This fixture is an exploratory proposed falsifier, not a proved admitted
right-context cycle. Its curried skeleton exposes shapes earlier than the old
anonymous-returned-lambda source, and its pure second argument-Effect branch
can additionally forward the actual argument computation with `both_from_right`.
Exact first surviving aliases, Value circuit, callback-source ownership, and
body/call-Effect attachment must be checked together. No global separation
claim in this note relies on accepting or rejecting that exploratory fixture.
The complete left-only classification above applies only to the two corrected
nonrecursive `as` sources.

## Exact minimal instrumentation and verification handoff

A source-identified ordered trace of the two primary fixtures needs these
retained facts, not a new solver relation:

- At each TypeAnn: source range, lowerer origin, `acc.value`, the paired positive
  and negative Function IDs, and every `(AnnTypeVarId,name,TypeVar)` allocation.
  At `lower_ret_effect_bounds`: its boundary-owned inner `r`, direct tail `e/h`,
  fresh `i`, declared family, and exact wrapper IDs. The first ascription's
  `r <-> t` aliases must be reported separately from equality.
- For the real Act operation: resolved family path, actual positive operation
  Function ID, actual positive Row/Con IDs, reference/use output, call Effect,
  and application-result Effect. Then the actual lambda return Effect(s),
  proving that this Row is the concrete lower arriving at `r/e/h`.
- One monotonically increasing event sequence for canonical enqueue attempts,
  concrete/alias bound dispositions and first surviving bound IDs, with
  exact pre-/post-filter weights and structural or binary replay parent IDs.
  Print the four primitive source bounds once and then stop after concrete
  PUSH counts 1,2,3; for the nested source additionally require one admitted
  concrete lower at left `(1,1)` and an actual replay using that record.
- Stage markers before/after both ascriptions and before the enclosing drain.
  The expression producer must not be reported as a local generalized use.

A bounded trace proves those events only, not natural-count unboundedness;
this note's fixed-primitive induction supplies the latter. A source guard
rejection or mismapped owner would invalidate the stated producer derivation
and must be reported, not normalized away. No source modification that changes
annotation authority or adds a count cap is proposed.

The seven scratch source fixtures are frozen. The two `nonrecursive_ascription`
fixtures are the primary minimized witnesses; inline-application and recursive
variants are fallback construction routes, and `right_debt_push_scc` is
explicitly exploratory. A narrow Python transcription checked eight PUSH
circuit iterations (16 distinct concrete keys), the concrete `(1,1)` path,
and 25 mixed full pairs. It ran once with a 30-second timeout and a 256 MiB
address-space limit:

```text
timeout 30s python3 /workspace/scratch/15155572c47b/recursive_push_source/check_source_circuits.py
PASS: 16 distinct concrete bound keys; nested mixed (1,1); 25 mixed normal forms.
```

The probe establishes arithmetic consistency only; it is not Oracle source
execution or independent source review. Source inspection was read-only via
`git show` at the pinned Oracle; no Cargo/build, compiler write, Git mutation,
child agent, source count cap, public scheme claim, or shared-record edit ran.
Primary owns independent review, any later harness/build, and record/Git
integration. Global source separation, general mixed recursion, changing
families/residual endpoints, all future generalized uses, and successor
conformance remain separate open obligations.

## Independent source review

`recursive_push_source_referee` checked frozen producer SHA-256
`8ba04d71b715079253f25129b121a7e53cf79efc5fc4c2cb014e94b12c5cdd84`
against the pinned Oracle and successor. The review found no blocking or major
defect in the primitive recurrence, concrete admission, or complete
pre-generalization left-only closure of these two fixtures. It ran no compiler
or Python process. The mathematical observer theorem and its executable
implementation were separate review scopes.

Two minor corrections are incorporated above: include the eager Act-operation
signature producer and finite application-demand Functions in the complete
inventory; describe finite-width pending saturation and ordinary active-count
addition accurately. The primary checked the owning source and the textual
delta. These corrections add no source restriction or successful-execution
claim. The broader source/generalization/production exclusions remain intact.
