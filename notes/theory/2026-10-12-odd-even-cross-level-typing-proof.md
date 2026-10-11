# Exact cross-level odd/even: the admission premise before typing

Date: 2026-10-12
Status: frozen, unreviewed bounded source characterization; exact typing bridge OPEN
Baseline: `e001972b31b7143c5f8318c48ebb47948d089fca`
Branch: `research/simple-sub-intrusion`
Lease: this file only; static constructive leaf, no delegation

## Frozen statement

The assigned source is exactly

```yulang
my odd n = my even n = if n <= 0 { true } else odd(n - 1); even(n - 1)
```

Its intended binding structure has one outer recursive definition `odd`, one
nested local function `even`, and two distinct formal binders with spelling
`n`. Write these binders `O`, `E`, `a`, and `b`, respectively. Inside `even`,
the comparison and subtraction use `b`; the recursive call resolves `odd`
to `O`. The final outer call resolves `even` to the published `E`, and its
subtraction uses `a`. `E` is not a same-level sibling of `O`.

Required local conclusion: obtain an authentic source derivation, then trace
its native generation, bound accumulation/replay, levels, extrusion and local
generalization under the original Simple-sub judgment and selected Yulang
ownership. The original supported-source domain is retained. A proof about
`odd(n)` with the conditional/arithmetic deleted cannot meet this conclusion.

For every successful proposed bridge, it must preserve those original binders,
their scopes, the conditional and arithmetic meanings, the two original Calls,
and all required effect/evidence relationships. The parent intrusion obligation
still quantifies over every supported source/history and actual retained Value
parent/copy pair: qualification is two-way reachability in the selected Value
reference graph before the proposed equality; the required conclusion includes
soundness and required principality. This note establishes no equality result.

Method: inspect the actual admission constructors first. Falsifier: a governing
source rule and reachable constructor that forms this exact nested source,
including its conditional and infix expressions, with the stated identities.
Stop at the first missing construction rule. No added primitives, translation,
source restriction, eager-solving rule, witness choice or weakened theorem is
assumed.

Authority: top-level inference principles §§1–5; parent-copy SCC decision,
**Value-reference SCC clarification**, **Apply-result source-fragment
ownership**, **Nested Apply membership**, and **Definition-root Value
ownership**; local self-recursive binding, **Selected source behavior** and
**Proposed source-to-solver seam**. All are under `notes/design/`. Repository
rules read: design authority, compiler engineering, agent orchestration,
research laboratory, orchestration budget and Git concurrency. The prover skill
and actual role configuration were inspected. No new decision is adopted.

## First missing rule: form the exact nested body

The literal one-line source has `my` immediately after the outer `=`. Current
syntax `declaration/binding.rs:328–360` selects the inline expression path when
there is no introduced body indentation; `:376–405` sends its first expression
item to `expr_from_nud_normalized`. Expression NUD selection
(`expression/operator_chain.rs:143–376`) has special owners for rule/string,
case/catch/if, parentheses and braces, but no nested declaration owner for
`my`. A normal identifier takes `emit_identifier_core` at `:302–316`.
`lexical/lexer.rs:705–719` separately lists `my` as a statement keyword, not a
contextual expression NUD keyword. This path therefore does not construct the
intended nested `BindingStatement` merely from the one-line spelling. No exact
parser run or particular recovery output is claimed.

If the one-line spelling abbreviates the previously supplied indented source,
the earliest HIR obstruction is independently explicit. The syntax constructor
at `declaration/binding.rs:328–337` produces an indented statement block.
`yu-hir/src/module/local_source.rs:223–255` requires the binding body's sole
child to be `OperatorChain`; `:319–321` applies that requirement before visiting
the body. `IndentedStatementBlock` fails it. The ordinary resolved-body path
in `yu-hir/src/module.rs:1596–1611` explicitly produces
`UnsupportedExpression` for that child. This is an implementation admission
absence at the body owner, rather than an unknown constraint solution.

These two representations must not be silently exchanged. Neither supplies
an authentic exact-source `LocalSource` on this baseline. The exact missing
premise is:

> There is an admitted lowering of the assigned source to the intended nested
> function/body tree, with `O`, `E`, `a`, `b` and their stated resolution and
> publication boundaries, preserving the conditional/arithmetic computation.

Owners: syntax binding-body/expression formation for the literal inline form;
ordinary HIR body lowering and LocalSource formation for the indented form.
The selected definition-root ownership rule does not implement this premise.

## Independent inner obstruction, without changing the source

Even granting the intended outer body tree, the intrinsic conditional cannot
be formed by the current carrier. Syntax constructs `IfExpression` at
`yu-syntax/src/expression/if_expr.rs:50`; the carrier's complete
`LocalSourceForm` declaration (`yu-hir/src/module/local_source.rs:107–137`)
contains Unit, Operation, Integer, Name, Apply, Group, Ascription, Lambda and
Block. `Builder::expression` at `:487–695` handles those admitted shapes and
rejects `IfExpression` through `:694`. There is no conditional desugaring in
that constructor. Consequently, assuming a direct conditional CST reaches
this visitor, `form` returns `StructuralProjection` before producing a
complete carrier. This implication follows by the match; it needs no solver
experiment and says nothing about a possible future faithful desugaring.

Arithmetic is another concrete formation gap. Syntax infix construction emits
`InfixOperatorUse` (`expression/operator_chain.rs:913–920`). LocalSource chain
formation permits only annotation and ML/Call/colon application tails
(`local_source.rs:507–532`), so an infix tail is rejected. The exact operator
environment, declarations, and typed meaning of `<=` and `-` are not supplied
by this source or the inspected carrier. `true` has no distinguished Bool
carrier constructor: a Name uses lexical/module lookup at `:636–657`.
No unprovided Yulang primitive signatures are assumed.

Thus the missing evidence is not simply a proof that stored bounds activate.
The source constructor cannot emit the required intrinsic computation in this
carrier. Replacing it with the smaller recursive Call skeleton would skip the
first premise and leave this assigned statement unproved.

## What the original judgment supplies, and where it stops

The original paper is Parreaux, *The Simple Essence of Algebraic Subtyping*,
local PDF `/home/momota1029/rust/simple-sub-reference-paper.pdf`. Printed p.4,
Fig.3 gives T-Var, T-Abs, T-App, T-Sub and T-Let; §2.2.1 explicitly represents
booleans/conditionals by primitive combinators. Its T-Let checks a recursive
initializer with a monomorphic binder, then generalizes variables not free in
the enclosing context. Figs.6–9, pp.17–21 give levels, freshening, extrusion,
and native constraint propagation. The imported proof note
`2026-10-11-parreaux-simple-sub-proof-import.md` is navigation and proof-scope
evidence; the original PDF and implementation were read directly here.

The pinned original implementation is
`/home/momota1029/rust/simple-sub-reference`, commit
`9bae772624c23b52a93c1b226157e16898b4d9db`. Its `syntax.scala:6–14` has no
Yulang source constructs. `Typer.scala:23–33` supplies `true`, `false`, `not`,
`succ`, `add`, and polymorphic `if`; it supplies neither `<=` nor `-`. A
translation plus primitive context could support such a source, but no
source-preserving translation/context is established for the assigned Yulang
term. This is a source bridge absence, not a counterexample to Simple-sub.

The following are **conditional prefix consequences**, not a completed run.
If authentic lowering exposes the intended outer recursive binding at level
0 and a nested let initializer inside its Lambda, original
`Typer.scala:48–55,64–67,81–83` implies:

1. Outer recursion gets monomorphic root `o` at level 1, and outer formal `a`
   is level 1. The nested initializer is inferred at level 2; its formal `b`
   is level 2. The inner reference to `odd` uses `o` itself because
   `SimpleType.instantiate` is identity (`:201–207`). Lexical capture does not
   instantiate the active enclosing recursive binder.
2. If the inner initializer succeeds with type `tE`, it is generalized at
   boundary 1. Variables above 1 are freshened coherently at a later use;
   the retained level-1 `o` is shared (`:166–189`). If it is treated as a local
   recursive initializer, the original extra monomorphic expectation is also
   level 2. Nothing in this prefix identifies that expectation with `o`.
3. An actual Apply generates `callee <: Function(argument,result)`
   (`:68–72`). Appending a bound and replaying existing opposite bounds, and
   extrusion upon a violated level guard, are the consumers at `:88–159`.
   No complete inner type or demand exists here without the missing source
   rules, so this packet cannot infer a particular extrusion event, copy,
   activated replay, final scheme, or principal type for the exact source.

The Yulang scheduler's corresponding level structure is explicitly present
in `candidate_source.rs:254–307`: start at 1, preserve level through Lambda,
raise local initializer level, and visit the final expression at the enclosing
level. Local installation preserves the initializer root and boundary
(`candidate_scheme.rs:1316–1334`). Those functions require a formed carrier;
they do not discharge its absence. Paper §5, p.24 restricts the proof sketches
to the non-let-polymorphic fragment; footnote 15 does not prove this nested-let
extension merely by suggesting duplication at use sites.

## Ownership conclusion and economy audit

Under the selected source resolution and definition-root law, `even` owns the
Name occurrence targeting `O`, and `odd` owns the final Name occurrence
targeting `E`. Hence `E → O → E` crosses lexical/inference levels. This is a
direct application of the approved source-owner definition, conditional on
those resolutions; it is neither a emitted-row trace nor a subtype statement.
The Apply law separately assigns its result rows the Names in their operands.
It does not equate those result rows with O/E, Lambda/Block rows, use facades,
fresh-use rows or extrusion copies. No new graph adjacency comes from
`callee <: Function(argument,result)`, stored bounds, containment or a parent
record. A source-owner SCC cannot qualify an unspecified parent/copy pair.

The earlier port derivation and native ownership discriminator do not repair
the exact admission premise. The present method inspects its owning constructor
instead of reconstructing another SCC model. Under the economy audit, admission
and faithful ordinary generation are A/B; recovering discarded Name/owner facts
from bounds would be D. Current evidence is missing construction, so retaining
incidence alone cannot fix it. No parent status is promoted or reclassified.

One next action: the primary assigns the exact admission/elaboration seam to
its HIR/syntax owner, carrying this source and binders unchanged and requesting
a faithful conditional/infix construction rule. Resume the typing derivation
after that source premise is supplied. Complete Call, effect hygiene,
copy/reference transport, qualifying intrusion, soundness, principality and
public/F5 cutover all remain unverified.

## Checks, resources and commit packet

Checks: static `rg`, `nl`, `sed`, `cat`, PDF-to-text reads; reference HEAD;
byte/SHA-256 comparison of 14 direct dependencies with the pinned baseline;
all 14 match. Dependency set: the three cited Authoritative designs and proof
import; syntax `binding.rs`, `operator_chain.rs`, `if_expr.rs`, `lexer.rs`; HIR
`module.rs`, `local_source.rs`; solver `candidate_source.rs`,
`candidate_scheme.rs`, `candidate_call.rs`, `candidate_intrusion.rs`.
`git diff --check -- <lease>` passed; because the note is untracked,
`git diff --no-index --check /dev/null <lease>` also ran with no whitespace
diagnostics (exit 1 denotes its new-file difference). HEAD moved to
`cd53f2241473f49c93953c89bae7a43ef0de394d` during the assignment; the 14
dependencies were rechecked and still match the pinned baseline.
No tests, builds, Oracle calls, executable
probes, benchmarks or Git mutations. At most three parallel static read
commands; no heavy process. CPU/RSS and exact reasoning wall time unmeasured;
work stayed within the 45-minute static budget.

External SHA-256: paper
`5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698`;
Typer.scala
`f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9`;
syntax.scala
`f26f19f6905d42c247198c45da9b1675b22619dd59749047023efe5f7ee3c60f`.

Requested settings: ordinary Sol/high proof leaf; registered prover has no
model/effort pins and configured defaults are `gpt-6.1-sol/high`. Observed
effective role/model/effort metadata is unavailable here: unknown. No Astra
request, model override, child launch or independent review occurred.

Commit packet: exact lease
`notes/theory/2026-10-12-odd-even-cross-level-typing-proof.md`; baseline
`e001972b31b7143c5f8318c48ebb47948d089fca`; changed dependency hashes: none.
Claim/review: unreviewed bounded source characterization and conditional level
prefix, not theorem closure. Proposed checkpoint:
`research: locate exact odd-even typing obstruction at source admission`.
Shared-record delta left to primary/curator: assign the exact-source body,
conditional and infix formation premise to the admission owner; retain the
selected cross-level root SCC and every native typing/transport/equality gate
as separate evidence requirements. No shared record was edited. Writes stop
at submission.
