# R221 — original literal carrier/readout obstruction

Status: **NO_ADMITTED_CARRIER_INTERPRETATION**. Frozen producer result,
`R221-ORIGINAL-LITERAL-READOUT/r1`; fresh review and Luna adjudication pending.
Author: `/root/original_literal_readout_r221_proof`.
Baseline supplied by Luna: `yulang3/d39ec2532e424526d8808dc6fd4ba13b95113766`.
Requested model/effort: Sol/high (`gpt-6-sol`/high in current state).
Observed model/effort: **UNKNOWN/UNKNOWN**; no runtime metadata authenticates
either setting. No in-place model change is claimed.

## Parent and result

The unchanged parent is `YulangClosure.SourceProblem.InferenceSoundness`,
`Contracts.lean:128–130`:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

The required literal application uses that same `a`, the original occurrence,
context, root, event, scope and joint witness. There is no admitted concrete
carrier/readout in the frozen inputs connecting R220's graph/reference solution
to the original source assignment. This packet delivers **no new theorem**,
no checked proof term, and **parent-premise delta 0**. It establishes neither
a source-qualified counterexample nor semantic inconsistency. Its result is
the exact missing interface below, at the contract's obstruction stop condition.
This is a missing admitted model input in the inspected dependency envelope;
it is not a claim that no construction exists elsewhere, that the source
meaning is underdetermined, or that a new semantic decision is required.

## Prior source-owner gate and later L1 adoption

Luna directed inspection of `tasks/agent-loop/history/r203-outcome.md` and
`tasks/agent-loop/history/r205-outcome.md` during this packet. R203 required
the primary to identify or define the original all-payload SG literal relation
before solver reflection, freezing the original rule, generator/solution
equations and shared `sameScoped` witness. R205 sharpened that order: compare
the payload-preserving intrinsic introduction against the selected SG local
alternatives, guards and L1/L2 Return/effect/world obligations; show an
existing-rule derivation or a real semantic commitment before proposing any
meaning change. Its independently reviewed result was a **missing model
input**, not absence of source semantics or a mandatory new user choice.

The later Authoritative L1 adoption fixes the eight intrinsic payload/type/value
introductions and original-root pure Return, and expressly preserves all
independently admitted checking alternatives and enclosing obligations. Thus
R205's earlier *unadopted intrinsic introduction* status is historical and
cannot reopen that choice. The still-active source-owner task is to authenticate
or construct this adopted relation in the actual original semantic carriers,
with its SG alternatives and L1/L2 obligations, before solver reflection uses
it. L1 expressly does not supply generation, satisfaction, readout or
`sameScoped`. R220's structural theorem does not replace this source-owner
gate. No theorem assuming the relation supplies the missing authentication.

## Existing equations and the literal payload

The Authoritative L1 adoption fixes the following payload-preserving map into
the existing paper syntax. This table expands its `p(l)` notation; it does not
instantiate `OriginalSourceInterpretation.Sorts` or introduce a new semantics.

| `OriginalSource.Literal` | `p(l) : PaperTypes.Literal` | `τ(l)` | R220 code |
| --- | --- | --- | --- |
| `.unit` | `.unit` | `.base .unit` | 0 |
| `.bool b` | `.boolean b` | `.base .bool` | 1 |
| `.int i` | `.integer i` | `.base .int` | 2 |
| `.floatBits bits` | `.floatBits bits` | `.base .float` | 3 |
| `.string text` | `.string text` | `.base .string` | 4 |
| `.bytes bytes` | `.bytes bytes` | `.base .bytes` | 5 |
| `.path path` | `.path path` | `.base .path` | 6 |
| `.character grapheme` | `.character grapheme` | `.base .char` | 7 |

Here `τ(l) = PaperTypes.literalType (p(l))` and
`v(l) = PaperTypes.Value.literal (p(l))`. Raw constructors are at
`OriginalSourceSyntax.lean:40–49` and `PaperExecutionSyntax.lean:20–28`;
`literalType` is at `PaperExecutionSyntax.lean:576–584`. No payload is decoded
from the constructor code. For example, distinct integer payloads share code 2;
the original literal remains an input to R220.

L1 fixes, at the original `(q,r,e₀,ξ,ω)`:

```text
LitRow(q,l,r,e₀) = ⟨Value(τ(l)), v(l), r, e₀⟩
Return(LitRow(q,l,r,e₀)) = ⟨Comp(empty,τ(l)), v(l), r, e₀⟩.
```

`Value(τ(l))` and `Comp(empty,τ(l))` here are L1's original descriptor
notation. They are not constructors of the abstract Lean type `s.Descriptor`
or `s.Interface`. The existence of `PaperTypes.Value.literal` does not supply
a function into `s.Value`.

The actual source generator has the equation
(`OriginalSourceGeneration.lean:85–89`):

```lean
sourceRules context (.literal mark value) =
  annotated mark context
    (.rule .lit mark.site context
      [.atom { (atom .literalDeclaration mark.site context) with
        literal := some value }] .nil)
```

This is a rule-tree equation read from the constructor definition, not a new
Lean theorem checked in this packet. It retains the full payload, site and
context. It does not allocate Simple-sub variable identities or emit R220's
three structural store clauses. `annotated`, lines 35–43, retains its real
formation atom and boundary from `⟨site,synthesis⟩` to
`⟨site,writtenTarget⟩`. The ports are separate constructors
(`OriginalSourceSyntax.lean:359–368`). There is no equation equating either
port with `finalRoot`.

R220 supplies exactly the following existing theorem, with namespace
`YulangClosure.AbstractGeneratorDenotationR220` and the imported Simple-sub
names opened:

```lean
theorem literal_structural_readout (graph : Graph) (refs : References)
    (valueVar effectVar : Nat) (literal : OriginalSource.Literal)
    (satisfied : StoreSatisfied graph refs
      (literalStructuralFragment valueVar effectVar literal)) :
    graph.lookup .value (refs .value valueVar) =
        some (.atom (literalCode literal)) ∧
    graph.lookup .effect (refs .effect effectVar) = some .bottom
```

Its source is `AbstractGeneratorDenotationR220.lean:116–122`; its store,
lines 31–36, has both value bounds and the effect upper bound to bottom.
The pinned R220 outcome reports a successful Lean 4.35.0 checker run and the
complete axiom list **`[propext]`** for this theorem (and each of its five local
helpers). This is inherited checker evidence, not an R221 rerun. The theorem
does not equate graph reference indices: duplicate equal atom nodes remain
permitted. Its `valueVar` and `effectVar` are caller-supplied numbers.

## Exact first missing carrier/readout equation

Write `A` for the original `SourceAssignment s`, avoiding confusion with the
parent's uninstantiated solution `a`. The existing fields and definitions are
(`OriginalSourceInterpretation.lean:830–850`):

```lean
structure SourceAssignment (s : Sorts) where
  event : Event s
  descriptor : OriginalSource.Endpoint → s.Descriptor
  value : OriginalSource.Endpoint → s.Value
  root : OriginalSource.Endpoint → s.Root
  binding : OriginalSource.Name → Option Nat

def SourceAssignment.row (assignment : SourceAssignment s)
    (site : OriginalSource.Site) : ValueRow s :=
  ⟨assignment.descriptor ⟨site, .finalRoot⟩,
   assignment.value ⟨site, .finalRoot⟩,
   assignment.root ⟨site, .finalRoot⟩, assignment.event⟩

abbrev LiteralDeclaration (s : Sorts) :=
  OriginalSource.Literal → ValueRow s → Prop

def LiteralAtom (inputs : Inputs s) (declarations : LiteralDeclaration s)
    (assignment : SourceAssignment s) (atom : OriginalSource.Atom) : Prop :=
  ∃ literal, atom.literal = some literal ∧
    declarations literal (assignment.row atom.site) ∧
    inputs.valueForm (assignment.descriptor ⟨atom.site, .finalRoot⟩) = .ground ∧
    inputs.ground (assignment.row atom.site)
```

`Sorts`, lines 23–50, contains only abstract types. `Inputs`, lines 324–371,
contains the independently supplied `valueForm`, `ground`, `traceForm` and
other operator inputs. Neither record contains the actual graph-to-descriptor
interpretation, an embedding of `PaperTypes.Value`, or a source endpoint
allocation. `SourceAssignment` contains no graph, reference assignment or
equation relating its descriptor function to either.

The missing equation must be provided by the existing source interpretation
owner, **Luna**, with the independent generator/solution model owner. For the
unchanged literal induction case it must establish all of the following from
the same generated solution, without assuming a source judgment:

1. Identify the actual allocated value/effect coordinates for that original
   literal occurrence and port, and show its generated store includes the
   R220 fragment. `sourceRules`'s literal atom is not this identification.
2. Give the admitted interpretation of the exact atom code/bottom into the
   original descriptor/effect carriers, and connect it to `A.descriptor` at
   the actual intrinsic literal port. Give the payload-preserving original
   value interpretation and connect it to `A.value`. Preserve the original
   `A.root` coordinate `r` and `A.event = e₀`, including its fiber, scope and
   shared witness. These are data equations, not consequences of `RegularSub`.
3. At the row consumed by the authentic literal rule, derive
   `declarations l (A.row q)`,
   `inputs.valueForm (A.descriptor ⟨q,finalRoot⟩) = .ground`, and
   `inputs.ground (A.row q)` from that admitted interpretation. The
   `finalRoot` read must be justified; it cannot replace the intrinsic port by
   naming convention. For annotated literals, retain the separate source and
   target rows and their actual boundary/conversion transition, rather than
   demanding the final converted descriptor always equal the intrinsic one.
4. Interpret the same literal Return as the adopted pure
   `Comp(empty,τ(l))`, with unchanged value/root/event; retain joint world and
   incidence premises. R220's `.bottom` is an Effect graph node, not by itself
   a `TraceRow`, an interface or `Inputs.traceForm = .pureReturn ...`.
5. Relate the resulting original source witness to that very solution through
   the concrete parent's `sameScoped`, retaining all enclosing checks, uses,
   futures and contextual effects. `Contracts.SourceProblem.sameScoped` is
   an abstract relation, not an existing endpoint-equality theorem.

These are the missing construction obligations, not proposed additional
theorem hypotheses or new semantics. No choice of a new `Sorts`, replacement
assignment, endpoint alias or exhaustive literal-checking policy was made.

## Two construction directions and why neither supplies the equation

**Graph outward.** Apply R220 to its same graph/reference assignment. This
gives the exact coded atom and bottom nodes. `RegularPublication.References`
is `Kind → Nat → Nat` (line 12); `decodeTerm`, lines 65–86, returns `Option Nat`.
`findNode` finds an existing graph node. None returns a source descriptor,
value, root, event or source endpoint. It cannot manufacture the missing
codomain maps or determine which source port supplied a Nat variable.
Reading a node index as `s.Descriptor` is not well typed for abstract `s`.
Reading the atom code as a payload loses data. Selecting the first equal node
would not justify equality with the assigned reference. This attempt leaves
the source carrier equation untouched after using R220's full conclusion.

**Original frames inward.** The existing environment construction has an
actual ordered decoder, but its `Root.assignment` is already a supplied
`SourceAssignment` (`OriginalSourceEnvironment.lean:239–245`).
`Root.decoded`, lines 319–320, carries it forward. Logical frames install
supplied descriptor data; runtime object frames install supplied values and
roots (lines 346–376). `RuntimeReadout`, lines 286–292, supplies actual event
fields, not a Simple-sub decoder. `foldedLiteralKernel`, lines 963–970,
still requires `LiteralAtom inputs declarations state.assignment atom`.
`folded_generated_literal_membership`, lines 981–1002, extracts its already
assumed form/ground facts. Thus composing this decoder with R220 also lacks
the graph-to-original assignment equation. It supplies no independent repair.

The concrete Bool `Sorts` under `OriginalCheckingAdmission.Discriminator`
(lines 643–674) explicitly identifies itself as an admission-plumbing
discriminator, not a complete Yulang instance. `OriginalFunctionFuture`'s
event discriminator has the same explicit limit. Reusing either as the
original carrier would change the accepted meaning and erase payloads.

There is a precise parameter-level falsifier of the tempting unrestricted
bridge: hold `graph`, `refs`, the literal and the original assignment fixed,
and take the free argument `declarations := fun _ _ => False`. The R220 store
and readout are unchanged, while `LiteralAtom` unfolds to a conjunction
containing `False`. This is a mathematical interface-separation argument,
not an executed Lean counterexample and not an admissible authentic L1
declaration or a source-qualified counterexample. It shows exactly why the
generic API alone cannot prove that bridge. L1 fixes a real declaration;
its admitted realization in these carriers is the missing input.

## Parent application and reuse boundary

`generated_literal_membership` (`OriginalSourceInterpretation.lean:896–913`)
has the exact premises `inputs`, `GroundLaw inputs`, a supplied
`LiteralDeclaration`, original kernel, original environment/context/site/raw
literal, and

```lean
OriginalSource.Satisfies
  (literalKernel inputs declarations original site literal) environment
  (OriginalSource.Build context (.literal ⟨site, none⟩ literal))
```

Its conclusion is
`Meaning inputs (.value (environment.root.row site))`.
It consumes source-formula satisfaction, not R220 `StoreSatisfied`. Its proof
extracts `valueForm = .ground` and `ground` from the literal atom, then applies
`ground_membership`. `GroundLaw.hereditary` propagates an already known
ground fact to compatible events; it does not introduce that fact or identify
its descriptor. Source reconstruction retains all rules, but does not equate
the two independent satisfaction notions.

A new theorem with the desired `LiteralAtom`, source `Satisfies`, or an
unproved “readout law” as a hypothesis would leave the literal induction
premise in its assumptions. Defining the bridge as that premise would be
circular for this assignment. R220 and original reconstruction cannot be
composed at this seam until the carrier and generation equations are supplied.
Even successful value membership would still require the pure Return and
same-scoped original witness application. No such application is claimed.

Reuse: R220's two-sided atom and bottom rigidity, original payload types,
L1's root/event/pure-Return decisions, and existing source reconstruction.
R214's one-sided `.top` countermodel is retained only against its original
one-sided candidate; it does not refute R220. R215's equivalence-class
proposal supplies no adopted original carrier and is not a dependency proof.
The adopted 2026-10-08 contextual interpretation expressly retains independent
ground meanings and foreign descriptor embedding obligations; its Return
constructor preserves an already supplied same tuple, not a graph readout.
No historical claim is enlarged to discharge this premise.

Full source forms, structural/annotation/method/adapter checking alternatives,
intrinsic versus contextual effects, actual inflow, residuals, Call effects,
provider/witness lineages, and the same joint scope remain unchanged.
R219's `NO_SAFE_CODE_SLICE` is not reopened. There is no Rust/native execution
evidence in this packet and no production authority.

## Frozen dependencies and execution receipt

All nine assignment pins were read and SHA-256 checked, with exact matches:

| Input | SHA-256 |
| --- | --- |
| R221 contract | `bdaa51efd7aecb2a0e291e256cec4749fc0ad78ca0623e4b1cc7b08bf8a49876` |
| R220 module | `bbd73afe54030cf3e4378a379a58a6836da1b44c9fd227b0bb8b372329f8a254` |
| L1 adoption | `f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8` |
| OriginalSourceInterpretation.lean | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| OriginalSourceGeneration.lean | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| OriginalSourceSyntax.lean | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| PaperExecutionSyntax.lean | `d0dc9871c382ca945059167b8b9e05f8f672170208a994f081e29760a207b87d` |
| Contracts.lean | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| R220 outcome | `eac0414232cd2afa93b2a10e7f2a6280db6e3489d026baccdb69dca3305c940a` |

Additional inspected existing source boundaries, not newly admitted external
dependencies:

- `SimpleSubRegularPublication.lean`: `18fc6f138204e1529dcd0bb9c01a20de7444a26e4dadc87677460ccd8ac9fc99`.
- `OriginalSourceEnvironment.lean`: `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132`.
- `2026-10-08-contextual-function-membership-definition.md`: `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0`.
- `2026-10-08-source-generalize-definition.md`: `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`.
- `2026-10-08-source-generalize-definition-and-proof.md`: `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`.
- `2026-10-08-call-semantic-input-realization.md`: `fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a`.
- `2026-10-08-simultaneous-immutable-root-introduction.md`: `a5efa7056b12f931892548ecf3366d66156627ec44577c99d20ca48596438ae6`.
- `tasks/agent-loop/history/r203-outcome.md`: `d17f2c1f40e1e2d7c092add2a972ed5c84af50d58e33b81db685aac103fb4bb1`.
- `tasks/agent-loop/history/r205-outcome.md`: `9047ffe6fae59bd1d6e51609e87f2f4c8ac8752d659218f5a7039bdb83199fc7`.

Checks performed: read-only `cat`, `sed`, `rg`, `sha256sum` and tool clock;
all assignment-pin comparisons matched. Two initial focused lookups named
nonexistent guessed module paths (`OriginalSourceProblem.lean`,
`PaperTypeSyntax.lean`, `TypeSyntax.lean`, `PaperTypes.lean`); later searches
used the actual owning files. No proof or failure conclusion relies on those
absent paths. The project's files were read: pin Lean 4.35.0, no external
Lake packages, `-j1 -M1024`. No Lean/Lake/build/cache command, tests, Cargo,
Git, network access, subprocess worker or descendant ran. No newly delivered
theorem has a type-check or axiom audit; the only reported axiom evidence is
the explicitly inherited R220 audit above.

Writes are limited to this note and
`tasks/agent-loop/inbox/original-literal-readout-r221-proof.md`. No scratch
file or directory was created. Source and central records were not edited.
The handoff records the final time, artifact hash and writer-stop receipt.

Next in-scope action for Luna: inspect this exact obstruction, then supply an
already admitted original carrier/endpoint/solution interpretation if one
exists, or return the missing construction input to its semantic owner before
admitting any new model or checker packet. The minimal falsifier for such an
input is a same-solution literal whose allocated intrinsic port does not read
the adopted descriptor/value/root/event, whose pure Return loses its world
incidence, or whose annotated boundary incorrectly aliases the distinct ports.
Producer TODO: none before the missing model input is supplied. Luna TODO:
adjudicate the missing original interpretation and assign fresh review; this
producer cannot independently certify its result. Parent closure remains open.
