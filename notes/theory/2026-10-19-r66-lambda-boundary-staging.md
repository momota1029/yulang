# R66: Lambda staging at the whole binding annotation

Status: candidate source-rule factorization and first unsupported instantiation
premise. This is neither a completed derivation for the fixed binding nor a
source/native correspondence, reviewed theorem, semantic choice, or production
authorization. Sole author: `/root/r66_lambda_staging_proof`; no descendants.
Session: `current-conversation-2026-10-19-r66`. Contract revision 1 SHA-256
`7ee35d3d66b2acd0c5115a75e7a8125bd136df98308dfc61dbc6d205a8e433e4`;
Luna-reported activation baseline `253f08169` (contract baseline parent
`64f63ff01577155b892e658c5fbeb090dd4c451b`);
the exact 26 direct dependencies in that contract matched before this write.

## Parent and original source objects

The parent is computation-forwarding preservation §§1,6–7 with its original
source domain, one shared assignment `xi=(nu,K,D)`, every finite prefix,
repeated and simultaneously live receiving entries, and independent receiver
and foreign-continuation obligations. Simple-sub A/B remain OPEN 0→0 and R50
remains NOT ADOPTED. This local binding analysis discharges no F1, FK1, mapped
FreshUse, runtime receipt, handler or generalization quantifier.

```yu
act io:
    our tick: int -> int

my forward (t:[io] int): [io] int -> [io] int = t
my outer (q:[io] int) = forward q
```

Use the original resolved `io` family `I`, definition `d`, retained Lambda
`L`, formal `t`, and direct body Name `n`. The formal annotation `a_t` owns
`p_t`; the distinct whole binding annotation `a` owns negative Function
argument occurrence `p_A` and positive result occurrence `p_R`. These are
source occurrences, not row-equality classes or observed native IDs. The
incoming formal computation effect `E_t` remains open. The joint context
retains the original provider, permissions, ordinary constraints, captures,
body/result evidence, scopes and any source checking alternatives.

HIR `local_source.rs:598–630,714–720` constructs the retained formal Lambda
chain and stores the whole annotation separately on `LocalSource`; its
`1016–1037` Name resolves to the original parameter. The arrow parser at
`source_annotation.rs:450–500` retains separate argument/result type syntax.
These facts justify the occurrence inventory, not a completed typed operand.
R64 D0–D2 already establishes this inventory, formal RootPermit/NamePermit in
its actual formal scope, and the distinct polarity meanings. Reuse it only
there: `p_t` does not license `p_A`, positive `p_R` allowance is not inflow,
and no Catch here performs subtraction.

## Bidirectional source-rule cut: what follows from the pinned grammar

The adopted source Generalize grammar (`source-generalize-definition-and-proof`
§§3.1–3.2, 4, 6, selected by `source-generalize-definition` §2) gives a
useful **structural cut for an already supplied derivation**. Its Annotation /
final-formation rule checks the actual completed operand against the written
target, retains both endpoints and prior/local evidence, and selects the target
as final root. Its Lambda rule requires the actual formal entry, captures,
body checking, body consumer and complete invocation. `Build` conjoins a rule
instance's premises and local clause at their original binders; SRC inverts or
reconstructs that *same* local rule program. None of these rules is a successful
native query or a free-standing `Sol_src` atom.

Write `D_L` for the *complete original* Lambda premise, with its actual body
checking and invocation proof, and `D_a` for the *complete original* whole
annotation target/checking premise, including its `p_A/p_R` children and every
admitted local proof or conversion choice. This notation names the premises of
the selected rules; it does not assert that either has been constructed for
the displayed source. Both are in the **one original scoped context** `C`:

```text
whole-annotation rule at (d,a):
  C |- L : U [D_L]       C |- check(U, target(a)) : T_a [D_a]
  -----------------------------------------------------------
  C |- d : T_a [D_L, D_a]       FinalRoot(d) = T_a
```

**Original to cut.** Invert an actual final-annotation rule instance at `d`.
Its premises supply precisely `D_L` and `D_a`, with the same `xi`, source
provider, original endpoints and witness strategy; no separate Lambda solve
or target-directed witness selection is allowed. Invert `D_L` through the
actual Lambda, Parameter, Name and Result constructors only to the extent
their own rule tags and premises permit. The cut records its operand `U` but
does not replace its body-checking subderivation.

**Cut to original.** Given those *same* original-scope `D_L` and `D_a`, apply
the Annotation/final-formation rule once at `d`. It retains prior evidence and
all checking alternatives, exposes `T_a`, and leaves the source provider
unchanged. SRC §6 constructs the corresponding `Build` rule node with exactly
their conjunction. On this restricted pair of identical proof trees, the
map is identity on original coordinates, scopes and typed substitutions;
any merely fresh local proof coordinates may be alpha-renamed at the same
binder with their witness dependencies transported together. Thus the cut
does not itself create a circular context or require solved `xi`.

This is a rule-instance rebracketing, not yet the proposed **ordinary Result-A
Lambda staging**. It says neither that every original derivation uses the
Result-A body route nor that the displayed binding has complete `D_L` and
`D_a`. Treating `D_a` as an opaque success predicate would conceal exactly
the R64 argument clause and correlated result work; this note makes no such
source-solution or permitted-substitution claim for the fixed binding.

## Attempt to construct the ordinary symbolic operand

At the authentic formal, the reviewed formal construction yields
`Gamma(t)=Computation(E_t,Int)`, the local `I` permission at `a_t/p_t`, and
NamePermit on `Resolve(n)=Parameter(t)` in that formal's scope. The selected
source-result law (`source-result-synthesis-choice` §4) therefore applies to
**Name synthesis**: `Synth(n)=Computation(E_t,Int)`. It adds no pure layer,
Force, input cap, provider change, result polymorphism or solved effect.

The next displayed law in that decision is
`Synth(lambda(P,body))=Fun(P,Result(I))`, with
`Result(Computation(E,A))=Comp(E,A)`. The decision fixes this for an
**unannotated function result** and expressly leaves explicit/nested result
checking and its selected typed path to be derived. The actual source has a
whole written Function annotation whose result occurrence is `p_R`. Although
the HIR keeps `a` outside the Lambda syntax and `n` has no expression
ascription, neither that syntax fact nor source Generalize §3.2(6) states
that the *Lambda body-checking premise of this whole-annotated binding* is
the unannotated Result-A synthesis judgment. Source Generalize §3.1 names
body **checking**, complete invocation and their original telescopes; it
does not replace that check with Name synthesis. A Function check may retain
nonidentity domain/observation proofs (§3.2(4)), and the whole annotation
must retain those original local choices.

The first unsupported step in the proposed stronger factorization is therefore
**`R66-LAMBDA-RESULT-STAGE-1`**:

```text
At the original whole-annotated (d,L,a), derive from the applicable
Lambda/body-result rule that its complete source operand U and prior evidence
are formed using Result-A on Name(t), or prove an exact same-context
bidirectional correspondence between every allowed original body-checking
derivation and that Result-A operand followed by the original Function check.
Preserve the one original xi, all body/invocation premises, p_t/p_A/p_R,
provider, checking alternatives, ordinary constraints and typed substitutions.
```

This is a rule-applicability/commutation premise, not a request to solve the
Lambda first. If the actual original rule checks the body under information
from the written Function result, moving to independent Result-A synthesis
may lose permitted joint assignments or evidence; if it uses Result-A before
the boundary, the direct source-rule derivation must exhibit that scope and
full premise tree. The pinned clauses do not decide that step. No two
compatible applicable source derivations with different original observables
are demonstrated, so this is **not** a semantic-ambiguity result.

The question can be falsified by an authentic selected Lambda/whole-binding
rule that supplies this exact operand and proves both directions under the
same original context; or by an actual applicable body-checking derivation
whose original solution/evidence has no staged Result-A counterpart. Merely
constructing a native Function term, erasing `a`, equating the interior
operand with the final root, or choosing a new witness after solving does not
answer it. Even after this step, `R64-SRC-ANN-ARG-1` still asks for `p_A`'s
typed interpretation and own permission on the original incoming carrier;
`p_R`'s correlated result interpretation, complete `Sol_src`, `Corr`, actual
`Q`, both native solution directions and legal whole-judgment transport remain
downstream under `R61-SOURCE-ASCRIPTION-FORMATION-1`.

## Source/native evidence and parent application

Current source/native owners illustrate the boundary without supplying the
missing source rule. `candidate_source.rs:451–460,603–615` preflights the
whole annotation and rejects its concrete negative `p_A`. Its definition
schedule at `:1450–1468` retains the body endpoint, annotation, root target,
occurrence and level as an `Action::Annotation`. `candidate_effect.rs:1605–1703`
constructs negative checking and positive exposure signatures before its
value links; `:1934–1935` independently rejects concrete negative variance.
`shadow_apply.rs:1436–1476,1578+` retains Lambda recipes and source actions.
These are producer/consumer locators, not evidence that an actual admissible
source derivation emits this fixed pair or that native constraints establish
`R66-LAMBDA-RESULT-STAGE-1`. The current guards remain intact. No safe code
slice follows from this packet.

Applied to the parent, the new pinned source grammar removes a possible
*structural* worry: final annotation checking can be read as a cut over one
prior Lambda premise in the same context, with the target retained as final
root and all evidence preserved. It does **not** discharge R65's completed
current operand, because replacing that prior premise by ordinary Result-A
staging has the exact unsupplied clause above. R64 and R61 stay OPEN; no
source/native or production gate changes. Historical R64/R65 prefix and
reviewed bounded failure are reused within their actual premises. Rejected
methods are a separate unannotated solve, RootPermit on `p_A`, positive
allowance as inflow, a native comparison as a source constructor, assumed
`xi/Q/Corr`, or a narrower ordinary-inference domain. Simple-sub generation,
accumulation, propagation, levels, extrusion, intrusion and generalization
remain the selected algorithm, untouched here.

## Mutual TODO and freeze boundary

`R66-LAMBDA-RESULT-STAGE-1`, source owner: the original Lambda/body-result
typing and whole-binding Annotation/final-formation rules (`source-generalize`
§§3.1–3.2; `source-result-synthesis-choice` §4). Required input: original
`d,L,t,n,a_t,a`, one joint component context and all local rule choices.
Required output: an applicable Result-A Lambda derivation plus both directions
of typed-evidence/solution transport, or the first actual failed rule premise.
Exact falsifier: an original permitted derivation/evidence tuple that the
staged judgment loses, or an applicable pinned rule that already gives the
complete same-context staging. Luna owns source-rule adjudication and any
new dependency or semantic decision; no producer can certify this candidate.

Downstream `R64-SRC-ANN-ARG-1` and parent
`R61-SOURCE-ASCRIPTION-FORMATION-1` retain their owners and full scopes.
Code-evidence TODO, only if Luna later authorizes a minimal provisional
slice: inspect the original source Lambda/annotation action interface and
test whether it supplies a completed body-checking operand *before* the
negative-`p_A` guard, while leaving that guard and publication behavior intact.
The falsifier is a constructor path that relies on annotation target evidence
to fabricate the supposedly prior operand. This is not implementation approval.

Checks: static inspection of the exact 26 pinned files and SHA-256 verification
only; no compiler run, test, build, probe, instrumentation, code or semantic
change. The direct manifest in the frozen R66 contract records their paths and
hashes; original document authors/provenance remain those stated there and
within the pinned documents. Requested worker model/effort `gpt-6-sol/high`;
observed model/effort UNKNOWN/UNKNOWN. Assignment cap 900 seconds charged in
full; actual elapsed/CPU/RSS UNKNOWN; no carryover or descendants. New paths
are only this artifact and `tasks/agent-loop/inbox/20261019-r66-proof.md`;
scratch paths NONE. Independent review and intake belong to Luna. The writer
stops at the frozen handoff.
