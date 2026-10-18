# R64: first unsupported argument clause in whole-ascription derivation

Status: candidate maximal partial source derivation and isolated unsupported
clause; no complete source solution relation, Corr, semantic-ambiguity theorem,
reviewed theorem, implementation adoption or production authority.
Sole author `/root/r63_whole_ascription_formation_proof`, session
`current-conversation-2026-10-19-r64`; no descendants or coauthors.
Contract revision 1:
`tasks/agent-loop/sprints/whole-ascription-derivation-20261019-r64.md`, SHA-256
`2f008cc535a4db8da53fc40acac6ae5750d25083be6d6abe4a5ee35f318576bf`.
Baseline `e5e0ac4e5b72c51406fac82ed82986d734bf3552`, Luna-reported;
no Git inspection. All 22 direct dependency byte hashes MATCH before writes.

## Parent application and exact outcome

The derivation stops at the **typed argument-position clause of the written
whole-definition ascription**. The available premises identify its original
definition/Lambda, the Lambda's computation formal, that formal's own licence
and direct Name route, and the ascription's negative argument occurrence.
They do not yet derive that occurrence's typed interpretation on the Lambda's
actual incoming computation carrier, with its own permission provenance and
the original component context. This is the first unsupported new rule
application below, before source solution collection, native Corr or Q.

The isolated request is **R64-SRC-ANN-ARG-1**, a child clause of the unchanged
`R61-SOURCE-ASCRIPTION-FORMATION-1`. It asks for the argument-position
interpretation itself, not a native auxiliary inequality or a complete
preservation theorem supplied as a premise. This gives Luna a smaller exact
rule/consumer question than R63's general unresolved whole-ascription relation.
It does not establish that the clause cannot follow from settled semantics.

Original computation-forwarding preservation §§1,6–7 and Simple-sub A/B stay
OPEN 0→0, with the original source domain, every finite prefix, repeated and
simultaneously live receiving entries, one shared assignment, and distinct
receiver/foreign-continuation quantifiers intact. No F1/FK1 or other independent
quantifier is discharged. R50 remains NOT ADOPTED.

## Derivation order: source operands before native equations

```yu
act io:
    our tick: int -> int

my forward (t:[io] int): [io] int -> [io] int = t
my outer (q:[io] int) = forward q
```

The identifiers below denote original source objects, not equal row labels or
new native allocations. No parser/lowering ran, so concrete allocated IDs are
UNOBSERVED. `I` denotes the original resolved io family, `d` forward's definition,
`L` its single retained Lambda, `t` its formal and `n` its direct body Name.
`a_t` is the formal annotation; `a` is the distinct whole-definition annotation.
Their row occurrences are respectively `p_t` and `p_A,p_R`.

**D0 — source ownership and type syntax.** `SourceEffectId` identifies a family
by module/declaration, and `parse_row` retains the exact row SourceNodeKey and
resolved declaration vector. `SourceAnnotation` retains its source root and
annotation position. The root `LocalSource` keeps `a` separately from the
annotation on its actual retained parameter. Its parameter loop records the
parameter ID, Lambda index, scope and annotation and installs that binding
before forming the Name (`source_annotation.rs:33–36,68–101,531–585`;
`local_source.rs:598–630,714–721,1017–1038`). Thus lexical ownership and direct
Name resolution can be traced without inferring identity from spelling.

**D1 — authentic formal source case.** Apply the reviewed formal construction
note §§2–3 only in its stated source context. Its role rule binds
`Gamma(t)=Computation(E_t,Int)` with open `E_t`. Its RootPermit premises are
`OwnsParameter(k,L,t,a_t)`, the original outer `[I] Int` row at `p_t`, computation
role and that formal's own entry coordinate. Here `k` is the original receiving
binder `(d,L,t)`. The selected negative annotation policy supplies the local
licence for exactly `I` on this root computation position. Resolve(n)=Parameter(t)
then instantiates NamePermit, giving the original carrier-use correspondence
`RootComp(t) -> n.computation` for this same licence.

This reuses a reviewed licence-introduction result, parametrically under its
one original source context `xi=(nu,K,D)`. It does not claim that the complete
ascribed definition's joint xi has already been generated or solved. `E_t`
here is a source coordinate in that rule instance; it is not an observed native
row. The source result licenses no closed `E_t <= {I}` cap, concrete contribution,
Force, automatic subtraction, handler selection or permission on another
annotation. There is no Catch in this body, so no residual transform is
introduced by D1. Existing ordinary constraints and source evidence are retained.

**D2 — whole annotation syntax and polarity.** The authentic arrow parser
constructs `a.ty` as Function(argument,result), with argument row `p_A`, result
row `p_R` and no root computation row (`source_annotation.rs:450–500`). At the
positive definition root, composed Function polarity reverses at the argument
and is retained at the result. Annotation integration §1 therefore selects a
local `I` permission meaning at `p_A` and a concrete `I` allowance meaning at
`p_R`. D2 derives these policy meanings at their own source occurrences. It
does not identify their typed effect coordinates, equate `p_A` with `p_t`, or
make `p_R` an inflow or residual. The three concrete vectors contain the same
family `I`; their original source nodes and authority lineages remain distinct.

## D3 — the attempted argument clause and its missing supplier

The next structural case would interpret the negative argument component of
`a` on the typed argument of the very provider introduced by `L`. Its attempted
premises are:

| Attempted premise | Evidence and exact limit |
| --- | --- |
| `a` belongs to definition `d`, whose root source expression is `L` | D0; actual source owners and retained root Lambda chain. This is lexical ownership. |
| `L` receives original formal `t` as a computation at open `E_t` | D1's reviewed formal source rule, under its actual context premises. This is not an executed native registration. |
| The body `n` resolves to `t` and retains that formal carrier-use/permission lineage | D1 NamePermit; no fresh receiver or row-equality argument. |
| `a`'s argument is `[I] Int` at distinct negative `p_A` | D2; resolved syntax plus composed polarity. |
| All clauses use the original relevant source component and its one joint xi | Required by call-view authority §2 / approved answer a2 items 4–5. The complete whole-ascription context is not independently constructed by D0–D2. |

Requested next output, written as an **unproved obligation label**, not an
inference rule or a definition of source solutions:

```text
R64-SRC-ANN-ARG-1(d,L,t,a,p_A,E_t; xi):
  the whole-ascription argument position p_A has its source-licensed typed
  interpretation on L/t's original incoming computation carrier E_t;
  its local permission witness originates at a/p_A in the legitimate scope;
  this relation belongs to the original component's joint typing constraints
  and preserves the prior p_t/Name evidence and every ordinary constraint.
```

No applicable pinned rule produces this output from the available premises.
`OwnsParameter` in RootPermit requires the actual parameter annotation `a_t`;
it does not accept an arbitrary negative descendant of `a`. Replacing `a_t`
with `a`, or its root row with `p_A`, changes that rule's hypotheses. A common
definition/Lambda and a single formal establish the syntactic pairing but are
not themselves the typed interpretation judgment requested here. The general
policy says what a licence at a resolved position means; it does not supply
this missing typed resolution by assuming the position is already resolved.

Call-view authority §2 requires typed paths/Flow/ownership from resolution and
typed elaboration, original correlated nu,K,D from the same source component,
and comparison-independent formation. It expressly leaves exact judgments
open. Section 4 retains current-endpoint annotation comparison and export
with local realization evidence; neither rule direction specifies D3's
argument interpretation or supplies the completed joint context. Section 5.1
requests callback contract formation. Applying that request as an already
proved whole-ascription rule would introduce its conclusion as a premise.
Approved answer a2 items 4–6 has the same limit.

Annotation integration §4 requires preservation of original annotation
position/boundary separate from canonical row identity and says that typed
transport carries original witnesses. That constrains a D3 derivation; it
cannot be used to create the initial typed correspondence that transport
requires. The reviewed formal rule is already reused in D1 and need not be
reproved. No new semantic choice has been established by this stopped attempt.

**Stop:** D3 is unsupported within these pinned inputs. In particular the
complete joint source context is still an unfulfilled part of D3, not an
independently supplied existential witness. D0–D2 are a partial derivation;
they are not a complete source constraint set for `forward` or the related
`outer` call. The `p_R` typed result/correlation branch follows D3 in this
attempt and is not silently filled in from its allowance meaning.

## Consequences for solutions, substitution and native evidence

Because D3 has not been derived, there is no complete derived constraint set
from which this packet can construct `Sol_src`. Taking the partial D0–D2
requirements as that set would drop the whole-ascription argument clause,
its correlated result obligations and actual ordinary constraints. Taking the
desired checking/exposed equations as that set would reverse the prescribed
derivation order. Neither construction is used.

Accordingly neither solution direction nor a legal typed-substitution theorem
for this complete source judgment can be attempted as an established statement.
No `Corr` or actual `Q` is presumed. In particular no syntactic absence of row
variables proves independence from inferred auxiliary/evidence coordinates;
R60's scalar lift remains inapplicable. The NamePermit reuse preserves its
actual source lineage within D1; it is not the missing whole-ascription
substitution theorem. Any later substitution argument must preserve one joint
K,D, same provider, positions, scopes, permissions, ordinary constraints and
correlated result evidence through actual generalization/transport.

The source stop precedes native design selection. As a separate owner check,
`candidate_source::preflight` refuses this root annotation at concrete negative
`p_A` (`:459–460,603–615`); `candidate_signature_effect` independently refuses
concrete negative variance (`candidate_effect.rs:1933–1935`). These facts do
not define the permitted source solutions and are not evidence for D3.

The actual native definition action retains the root Lambda/provider endpoint,
annotation, target component, occurrence and level
(`candidate_source.rs:1450–1468`). `candidate_annotation_pair` constructs the
checking and exposed signatures before either value link, then admits slot
40, processes root computation effect/slot 42 if present and admits slot 41
(`candidate_effect.rs:1627–1704`). The preceding negative-empty bundle remains
part of that order. No completed pair, admitted native derivation, mapped bound,
FreshUse or actual `Sol_nat` is obtained for the fixed source. No prospective
native schema is imported into D0–D3.

## Reuse, mutual TODO and stop receipt

Reused within premises: the reviewed formal licence/Name construction for
`a_t/p_t`; selected polarity and open-inflow distinctions; original forwarding
source/template results without promoting their conditional native part;
R60's dependency condition; R63's reviewed source-owner boundary and corrected
constructor order. R63's API witness is not repeated as a derivation method.
Rejected: RootPermit with changed ownership hypotheses, lexical pairing as
typed interpretation, existing transport as initial formation, callback
formation requested by authority as an established whole-ascription rule,
native inequalities as source constraints, Q independence and semantic
ambiguity from missing documentation. No bypass or ordinary-inference
weakening is restored.

Mutual TODO **R64-SRC-ANN-ARG-1**, parent
**R61-SOURCE-ASCRIPTION-FORMATION-1**, owner Luna to allocate source typing/
annotation elaboration: provide the authentic rule deriving D3 from the exact
premises above, including the original joint-context formation premise, or
provide its actual failed premise at the owning rule. Required inputs: fixed
source, authentic definition/Lambda/formal/Name, distinct `a_t/p_t` and
`a/p_A/p_R`, open E and ordinary component constraints. Proposed output:
argument-position source constraint and its typed permission/ownership
interpretation, before native representation or Corr. Falsifier: the rule
changes providers/positions, borrows `p_t` permission for `p_A`, caps or
injects effects, invents joint xi, omits ordinary constraints or requires a
comparison result to create evidence. If the necessary rule lies outside the
22 pins, return its exact proposed dependency to Luna before reading or using
it; this lease grants no dependency expansion.

Native mutual TODO **R64-NATIVE-PREREQUISITE-1**, owner Luna/native lane:
`candidate_source::preflight` and
`candidate_effect::candidate_annotation_pair/signature_effect` give
**NO_SAFE_CODE_SLICE** before source D3 and subsequent result interpretation
are established and independently reviewed. A code-evidence proposal must be
minimal/provisional, name the established source clause and exact consumer
falsifier, and return to Luna; no production code is edited here.

No next derivation stage is authorized past this first unsupported clause.
Fresh independent review belongs to Luna; this producer cannot certify its
result or the combined packet. No complete source derivation, semantic
underdetermination or parent closure is claimed at the finite stop.

Checks: static source/authority inspection and byte hashing only. The frozen
contract contains all 22 direct path/hashes and dependency author provenance;
all pins MATCH before writes and are rechecked at freeze. No new semantic/source
dependency, parser/solver/compiler execution, tests, builds, probes, runtime,
instrumentation, measurements, Git, code/semantic edits or external contact.
Workflow rules/skills previously read continue to apply. Requested model/effort
Sol/high (`gpt-6-sol/high`); observed UNKNOWN/UNKNOWN. 600-second grant charged
in full; elapsed/CPU/RSS UNKNOWN; no expansion/carryover. Only this note and
`tasks/agent-loop/inbox/20261019-r64-proof.md` are new; scratch/other paths NONE;
no descendants. STOPPED / WRITES_STOPPED / NO_DESCENDANTS at frozen handoff.
