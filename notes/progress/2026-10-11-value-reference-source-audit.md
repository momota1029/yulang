# Value-reference source audit

Date: 2026-10-11
Status: Frozen, unreviewed independent source audit; research only
Gate/method: constructor and semantic correspondence; discriminating symbolic source traces
Yulang baseline: `3fa72e768c5a31e12ff44061d119102efca9aef3` on `research/simple-sub-intrusion`, supplied by primary
Original reference: `9bae772624c23b52a93c1b226157e16898b4d9db`, supplied by primary
Exclusive lease: this file only

## Finding and its scope

Original Simple-sub does not define the proposed choice between a graph of
source free names and a graph of runtime providers. It defines a third object:
an inference representation containing mutable type variables, their stored
lower/upper type bounds, and Function/Record constructor children. Its source
typing function creates and returns these objects. The reference contains no
provider/capture identity in these inference constructors, and no intrusion
operation or SCC qualification in the inspected inference implementation.

The approved Yulang operation selects Value variables as vertices, references
in their values as edges, retained extrusion parents, and equality when a
parent/copy pair belongs to one SCC. It expressly rejects treating comparison
judgments or parent metadata themselves as edges. This does not identify Value
variables with runtime provider IDs or source binder IDs. The original
reference's constructor content is therefore an essential candidate to check
before presenting a static-name/runtime-provider choice to the user.

There are concrete graph differences, rather than just an absent proof:
`let rec g = λx.({keep=0,drop=g}).keep in g` has no recursive type-content
cycle through its recursive owner in the original inference representation;
a closure constructor retaining lexical free-variable references has a
provider self-cycle. The exact derivation is below. This discriminates those
two graph constructions under the stated closure premise. It contains no
extrusion parent/copy pair and is not a counterexample to intrusion equality.

No inspected authority equates the complete Call witness, actual output
provider, lexical free-name set, and native Value-row content. The unresolved
correspondence is the assignment of actual reference targets to a native
Value variable at its constructor, together with transport through use and
extrusion. This report does not infer that a new language decision is needed
merely because that bridge remains unproved. It does not adopt a graph.

## Governing sources and terms

The direct authorities read were:

- `2026-10-10-parent-copy-scc-intrusion.md`, “Selected operation and compiler
  responsibility”, “Value-reference SCC clarification”, and “Retained boundary”.
- `2026-10-11-yulang-inference-top-level-principles.md` §§1–5 and “Authority
  and integration”: mathematical Simple-sub, proof-derived implementation,
  deterministic inference and necessary abnormal-path safety.
- `2026-09-29-scc-intrusion-redesign-charter.md` §17's lexical references for
  reification, §18's result interface forwarding, and its variable-level direction.
- `2026-10-08-contextual-function-membership-definition.md` §§2–3, including
  its selected positive immutable recursive pair: same actual callable,
  immutable captures, same-value/provider Return, and `my f x=g; my g y=f`.

The original paper distinguishes term variables `x` from type variables `α`
(§2.2, Figs. 1–3, pp. 4–5). Its informal “values” support a meaning for types
as sets of values; this is not a definition of a runtime heap/provider graph.
Its inference representation is explicit in §3.1.2, p. 8 and Fig. 6, p. 17:
VariableState has lower/upper lists; Function has input/result children;
Record has named type children. “Variable references” on p. 9 describes term
lookup in the typing context, not graph edges from a closure object.

Reference implementation locators in
`shared/src/main/scala/simplesub/Typer.scala`:

| Meaning | Actual constructor/consumer |
| --- | --- |
| Term Name | 62–63: instantiate its context scheme |
| Lambda | 64–67: fresh parameter type and `Function(param,body_ty)` |
| Apply | 68–72: constrain callee against `Function(argument,res)`; return fresh `res` |
| Record / projection | 75–80: named type children; constrain only requested fields |
| Recursive let | 48–55: monomorphic RHS owner, RHS-to-owner constraint, then scheme |
| Stored constraints | 105–127: structural decomposition, stored bounds and opposite-bound replay |
| Extrusion | 134–159: polarity-specific copies and one-sided parent links |
| Scheme use | 166–188,201–207: preserve low variables, clone high variables and their bounds |
| Internal objects | 209–227: Function/Record/Primitive/Variable; no provider or capture field |

Paper Figs. 6–7 and implementation agree on those distinctions. Neither alone
proves Yulang's selected SCC graph or qualified equality theorem.

## Discriminators with explicit hypotheses

All reference traces here are hand derivations of the actual pinned
`typeTerm`/`constrain` cases, not executed programs. Unless recursion or use is
named, work at one level with fresh variables and a valid monomorphic context.
For graph descriptions, expose each variable's stored bound objects and each
Function/Record object's children, then contract intermediate constructors if
only variable vertices are desired. This is a defined candidate graph, not a
claim that the user has approved every such pointer as Yulang adjacency.

### Projection discards a typed field, while a lexical closure retains its name

Let `Γ(g)=γ`, where γ is an existing same-level monomorphic type variable.
Infer `λx.({keep=0,drop=g}).keep`:

1. Lambda creates fresh α for x.
2. Record typing returns `Record(keep:Int,drop:γ)`.
3. Selection creates fresh β and compares that record with `Record(keep:β)`.
4. The Record comparison iterates only fields requested by the RHS. Its sole
   recursive comparison is `Int <: β`, so `β.lowerBounds=[Int]`.
5. Lambda returns `Function(α,β)`. Neither α nor β has a reference to γ.

Thus there is no path from the returned Function type through γ. The original
record expression did contain γ, but that constructor is not a child of the
returned type. Under a lexical free-variable closure constructor, the lambda
captures g even though its body eventually returns 0. This gives a lambda-to-g
reference in the closure graph. The original paper does not specify that
closure implementation or require preservation of an unobservable capture
after optimization. These are distinct explicitly hypothesized constructions.

### Smallest recursive variant changes SCC membership

For `let rec g = λx.({keep=0,drop=g}).keep in g`, original recursive-let
construction creates ρ at the RHS level and binds g monomorphically to ρ.
The same projection trace gives α and β with `β.lowerBounds=[Int]`, and does
not constrain ρ from the discarded field. Recursive-let closure then stores:

```text
ρ.lowerBounds = [Function(α,β)]
ρ.upperBounds = []
α.lowerBounds = α.upperBounds = []
β.lowerBounds = [Int]
β.upperBounds = []
```

ρ reaches α and β, but neither reaches ρ. There is no nontrivial cycle through
ρ. The let-body use freshens quantified variables and preserves this shape.
By contrast, a closure retaining free g stores a reference back to that same
recursive closure, yielding `p_g -> p_g`. This is a finite source-generated
witness distinguishing SCCs of type content from SCCs of lexical providers.
It establishes neither a production capture requirement nor a parent/copy
merge result. Removing the unused lambda parameter changes it into a
recursive record/value initializer, so this witness is minimal for the
requested lambda/projection family, not globally proved minimal.

### Other requested cases

| Case | Reference inference content | Runtime/source interpretation and discrimination |
| --- | --- | --- |
| `id = λx.x` | `Function(α,α)`; no capture field or body Name node survives | A closed identity closure has no free-name capture. The two type ports still refer to α. A parameter-type reference is not a runtime closure capture. |
| `konst = λx.0` | `Function(α,Int)` | A closed constant closure likewise has no free-name capture. The α input port remains despite the body ignoring x. |
| `id g` | Instantiate id as `Function(a,a)`; generate `type(g) <: a`, then `a <: b`; replay supplies lower bounds to result b | For a genuine returning Value-entry source invocation, the output provider is g's provider; it is not id's provider. This semantic forwarding does not turn b into a runtime provider ID. |
| `konst g` | Instantiate `Function(a,Int)`; generate `type(g) <: a` and `Int <: b` | A returning source invocation produces the literal provider. It still forces an ordinary Value argument according to Yulang's approved entry rule. Whole-Call operands remain evidence, but are not thereby result-value references. |
| `invoke = λf.f 1` | Fresh α,β; store `α.upperBounds=[Function(Int,β)]`; return `Function(α,β)` | The closed lambda has no free-name capture. Type content has an actual α-to-β route through a Function bound. A graph of only captured runtime providers misses it. No selected provider is known when ordinary inference constructs that bound. |
| Same descriptors, different captures | With monomorphic a and b both bound to `Function(Int,Int)`, `λx.a x` and `λx.b x` each generate fresh input with upper Int and fresh result with lower Int; their returned type graphs are isomorphic | A lexical capture graph targets a versus b. Type shape does not recover capture identity. If distinct actual providers satisfy the same complete descriptor, same-provider Function membership forbids switching between them merely because the descriptor matches. |
| Selected mutual pair `my f x=g; my g y=f` | Structural result references can be cyclic; the original reference has one recursive binder per Let, so this literal simultaneous source form is not in its syntax | The selected two-closure construction has reciprocal captured references and reciprocal returned providers. Both candidate constructions can have a cycle here, so this example alone cannot select a graph. Its selected scope must not be expanded to arbitrary mutual recursion. |

For the reference's actual syntax, encode returning mutual recursion as
`let rec r={f=λx.r.g,g=λy.r.f} in r`. Let its recursive owner be ρ, parameter
types a,c, and projection result types b,d. Before closing recursion:
`ρ.upper=[Record(g:b),Record(f:d)]`. Closing installs
`ρ.lower=[Record(f:Function(a,b),g:Function(c,d))]`; replay then installs
`b.lower=[Function(c,d)]` and `d.lower=[Function(a,b)]`. Thus b and d share
a type-content SCC through result ports. ρ reaches that SCC but is not on a
return path from it. A lexical closure/record graph can instead include the
record and both closures in one capture SCC. Different node ownership is
visible even where both constructions contain recursion. This is an original
syntax encoding, not evidence that Yulang native collection implements it.

### Positive and negative routes are distinct from edge direction

For a reference variable p above the extrusion target, positive extrusion
creates c with `p.upperBounds ::= c` and copied lower bounds in c. Negative
extrusion creates c with `p.lowerBounds ::= c` and copied upper bounds in c.
Both mutations store a pointer from p to c. Logical subtyping direction is
`p <: c` in the first case and `c <: p` in the second; it is not the direction
of a bound-container reference in the second case. A graph whose edges are
comparisons gets that case wrong. A graph that reads only the positive lower
bounds also omits the real positive-extrusion parent-to-copy upper pointer.

Function extrusion flips polarity in input children and retains it in result
children (Typer.scala:144). A negative route is still a reference route if the
chosen Value representation contains that child. Coalescing at 239–255 uses
polarity-selected bounds to print a type; this is a different operation from
enumerating all stored references. No arbitrary future reverse edge or
invalid level-violating store is assumed here, and no source-qualified
parent/copy SCC is fabricated from these one-sided links.

## What Yulang's inspected constructors actually provide

`candidate_source.rs:212–217` uses the parameter endpoint directly for a
parameter Name; other source expressions use component positions. At
445–459 it forms a LambdaRecipe containing parameter, root, body-value and
effect endpoints. `lib.rs:11233–11261` resolves the input and body result
ports; 11342–11362 constructs and constrains the positive Function at its root. The fields
are inference endpoints, not an enumeration of every free Name in the body.

Source binding ownership must also be distinguished from expression result
ownership. Original Simple-sub creates a special monomorphic owner for a
recursive binding RHS; an ordinary nonrecursive binding instead stores the
type returned by its initializer in a scheme. It does not allocate one Value
variable for every expression: a literal returns Primitive, a lambda returns
Function, and a Name returns the instantiated scheme object. Apply and
projection each create their own fresh result variable. Those result variables
are neither source binders nor automatically the owners of the callee's or
argument's syntax/captures. Native Yulang collection does allocate a component
position for every expression (`candidate_source.rs:187–188`), then reuses
parameter endpoints and some aliases. An Apply's `result=pos.value` is thus
an expression-owned inference endpoint, whereas its `owner` is the enclosing
definition root. Treating the enclosing binding's capture graph as adjacency
for every such expression result adds a law that these constructors do not
provide. The `konst g` case makes this difference concrete.

Apply collection retains callee/argument/result and source occurrence
(`candidate_source.rs:394–411`; `candidate_call.rs:29–58`). Admission forms a
negative Function with the actual inference argument/result ports
(`shadow_apply.rs:1331–1383`). This is recognizably the original structural
typing construction extended with effects. It supplies no runtime provider
identity in `ValueEndpointKey` (`lib.rs:734–745`).

Current SCC extraction (`candidate_intrusion.rs:375–484`) reads both stored
Value bound sides, both Effect bound sides, view tails, and Function's four
ports. It then tests retained parent/copy component equality. Its parent
metadata is not itself an edge. This is concrete inference-representation
adjacency; its mixture of Value/Effect vertices and paths still needs a
correspondence to the selected graph whose vertices are Value variables.
It is not a source lexical-capture inventory or a runtime-provider heap.

`candidate_extrusion.rs:90–125` creates the lower-level copy, retains the
original parent, and inserts the one-sided source link before replaying the
selected side of the bounds. This agrees with the reference's polarity law;
it does not decide which Value-content interpretation validates an SCC.

The smallest remaining question for the owning construction is therefore:
which of these actually retained inference references count as references
in a native Value variable's value, including constructor ports and any
paths through effect structure? Establishing that correspondence may be a
representation/proof task under the existing decision. Choosing a runtime
provider graph would require an explicit map and transport law; no inspected
source supplies that identification. Conversely, copying free source names
into all result rows contradicts the original projection/constant type traces
unless it is explicitly a separate retained certificate rather than type
content. No new semantic choice is recommended from absence alone.

## Evidence, resources and unverified scope

Commands were bounded `cat`, `rg`, `rg --files`, `nl`/`sed`, `pdftotext -layout`
to stdout, and `sha256sum`. Read windows covered original paper pp. 4–6,
8–11,16–18; actual Typer.scala constructors; selected source authority;
native Lambda/Apply/extrusion/SCC constructors. Some combined reads truncated;
decisive source windows were subsequently read narrowly. An initial guessed
`yu-hir/src/candidate_*` path was absent; actual owners were located in
`yu-solver/src`. No repository-wide absence claim is made.

No executable oracle, checker, random seeds, ranges or mutation execution
was used. The hand traces share the pinned source transition rules; they
characterize those source cases and do not independently prove the original
rules sound or prove all source-generated stores. The lexical closure
comparisons explicitly assume retained free-variable captures; no original
reference evaluator was invoked or claimed. Hypothetical comparison-edge,
polarity-only and descriptor-identity shortcuts were analyzed, not mutated.

Zero code/test/build/format/Git commands and zero child delegation; one leased
research artifact written. No compiler execution, Yulang parse/admission,
complete Call, general effects, mutable State, diagnostic/rollback lifecycle,
all-source soundness/principality, or qualified parent/copy equality was
verified. Up to four lightweight read processes were batched; no heavyweight
process ran. The 60-minute wall budget was not exhausted; precise CPU/RSS
and reasoning wall time are unknown. No independent reviewer has certified
this report. The primary-owned interpretation draft was not read or edited.

Recommended next action: have the owning proof/construction lane test the
selected Value-reference graph against the actual retained inference content
using these discriminators, explicitly mapping Value vertices and any effect
paths; request a new user decision only if two source-grounded alternatives
remain after that map is made explicit.

## Frozen dependency snapshot

SHA-256:

```text
parent-copy authority 2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0
top-level principles edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389
SCC charter 547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed
paper 5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698
Typer.scala f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9
syntax.scala f26f19f6905d42c247198c45da9b1675b22619dd59749047023efe5f7ee3c60f
candidate_source.rs 13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49
candidate_call.rs 79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35
candidate_intrusion.rs aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0
candidate_extrusion.rs fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0
shadow_apply.rs 230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6
solver lib.rs c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94
contextual Function authority 0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0
Call semantic realization fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a
simultaneous immutable introduction a5efa7056b12f931892548ecf3366d66156627ec44577c99d20ca48596438ae6
```

## Commit packet

- Exact leased path: `notes/progress/2026-10-11-value-reference-source-audit.md`.
- Baseline SHA: `3fa72e768c5a31e12ff44061d119102efca9aef3`; original reference
  commit `9bae772624c23b52a93c1b226157e16898b4d9db`, primary-supplied.
- Dependency changes: none caused by this worker; hashes above. Git/live
  baseline verification remains primary-owned because Git commands were excluded.
- Claim/review: bounded source characterization and conditional graph
  discriminators; unreviewed research checkpoint, no theorem or semantic approval.
- Checks already run: source/PDF window reads, symbolic constructor derivations,
  dependency hashes and a read-only artifact inspection (zero trailing-whitespace
  lines; four fence markers); no executable or compiler verification.
- Proposed message: `research: distinguish Value type content from provider captures`.
- Shared deltas intentionally left to primary/curator: add the inference-content
  third candidate and recursive projection SCC discriminator to the graph gate;
  retain source/native graph mapping and parent/copy preservation OPEN; do not
  publish a static/runtime user choice from the missing bridge alone.
- Artifact frozen; writing stops before review submission.
