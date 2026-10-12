# Two-use intrusion witness: supported source candidate and admission obstruction

Status: frozen, independently reviewed research checkpoint; source-grounded
candidate and precise evidence obstruction. No Yulang semantic counterexample
or theorem closure is claimed.
Baseline: `e5e7b5878ced01b8cc4682492b6187c3907fd014`, branch
`research/simple-sub-intrusion`.
Current source revalidation: `5cb4ba6f9cc8fa65d347c3b53b6d4e6e5196d02f`; all 15
recorded source dependency hashes match.
Lease: this file only. Method: static constructor/source audit, one candidate.

## Objective and governing dependencies

Replace the Record/Bool witness in the independently reviewed conditional
[occurrence proof](../theory/2026-10-12-extrusion-occurrence-intrusion-proof.md)
§§3–7 with supported ordinary source forms; establish either original admitted
two-use behavior or the first exact missing source law. Preserve the selected
G-origin/F-receiver occurrence and its C=B equality.

Authority: [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5; [parent-copy operation](../design/2026-10-10-parent-copy-scc-intrusion.md),
Selected operation, Value-reference SCC clarification, Apply-result membership
and Definition-root Value ownership; [occurrence qualification](../design/2026-10-12-intrusion-value-type-association.md),
Approved extrusion-event qualification and Implementation/proof boundary;
[Source Generalize](../design/2026-10-08-source-generalize-definition.md) §§2–3,
selecting source construction §§3–5 of its linked proof. Root/Apply ownership
are accepted decisions, not new interpretations selected by this producer.

## One candidate and its resolved construction

```yulang
my answer = {
  my f x = {
    my g y = { my drop z = y; drop (f y) };
    my first: int = g 0;
    g ()
  };
  f
}
```

This uses Integer, Unit, Name, Apply, Group, Lambda and sequential Block;
`first` has an ordinary primitive binding annotation. There is no Record,
Bool, builtin `succ`, synthetic client inequality or unsupported branch.
It is structurally small: four local bindings, three bare formals and four
Apply occurrences (`f y`, `drop (f y)`, `g 0`, `g ()`). The unused annotated
`first` still requires its initializer check; evaluation/type formation does
not discard a binding because its value is unused.

The construction below is a static derivation from the lowering branches,
conditional on an ordinary recovery-free CST for this displayed text. No
parser was run; actual allocated identities or successful typing are not
reported as observations. Existing fixtures use precisely these binding,
application, Unit and annotation spellings, e.g.
`candidate_annotated_primitive_formals.rs:97–155` and
`simple_sub_local_source_retirement.rs:104–143`; those tests were read, not run.

Let Q be `answer`'s DefinitionRootId. `local_source.rs:710–828` scans each
block's declarations before descending into initializers, while `:329–374`
temporarily installs a parameterized local's own identity, installs its
parameters, and publishes it after its initializer. Thus its actual ID
constructors give the following static layout (numeric ordinals are relative
to this carrier, not identities in a running session):

| Binder | Constructed identity | Relevant resolved Names |
| --- | --- | --- |
| f | HirLocalId(Q,0) | `f` inside `f y`; final outer `f` |
| g | HirLocalId(Q,1) | both `g` consumers |
| first | HirLocalId(Q,2) | no uses |
| drop | HirLocalId(Q,3) | `drop` inside g's final expression |
| x | HirParameterId(Q,0) | unused |
| y | HirParameterId(Q,1) | drop body `y`; argument `y` in `f y` |
| z | HirParameterId(Q,2) | unused |

The Name rule at `local_source.rs:640–663` chooses the latest lexical entry,
then the module namespace. There are no duplicate spellings or external
dependencies here. In drop's initializer, y remains the enclosing g formal;
in g's final expression, drop has been published and f remains an active
outer initializer. Both g uses follow g's publication; the final f follows
f's publication. No recursive Name is retargeted during copying.

`candidate_source.rs:250–328` starts Q's body at level 1, visits Lambda bodies
at the same level, and increments the level only for local initializers:

| Construction | Level | Publication boundary |
| --- | --- | --- |
| outer answer Block; final f Name | 1 | Q's later module boundary |
| f initializer, x, f body Block | 2 | f: 1 |
| g initializer, y, g body Block, `f y`, wrapper Apply | 3 | g: 2 |
| drop initializer and z | 4 | drop: 3 |
| first initializer and `g 0` | 3 | first: 2 |
| final `g ()` | 2 | no local publication |

During `f y`, `active_initializers` contains f and g. The f Name produces
`Action::Link` to f's original initializer endpoint, rather than a fresh
local scheme (`candidate_source.rs:369–389,664–669`). During either g use,
g is installed and produces `Action::Local`. Local installation retains
root/boundary (`candidate_scheme.rs:1320–1340`); each Name separately captures
the graph and prepares a fresh use at its own level (`:1354–1380`). This is
actual candidate construction evidence for two distinct use events; it does
not prove Source Generalize's lawful allocation classification.

## Approved Value references and event endpoints

Apply the accepted definition-root incidence rule to actual resolved Names
in each declaration's own body, excluding nested initializers:

* F owns the final g Name, giving F→G. The earlier `g 0` Name belongs to
  First's initializer. F does not acquire drop's y Name or
  g's f Name by lexical containment.
* G owns `drop (f y)`, giving G→Drop, G→F and G→Y.
* Drop owns its body y, giving Drop→Y.
* First owns its initializer's g Name, giving First→G.
* Q owns the final f Name, giving Q→F.

In particular F→G→F establishes SCC(F)=SCC(G) without any type-bound edge or
assumption that a Block/Apply row equals a definition root. Additional actual
Value edges cannot destroy this mutual reachability. The two inner Apply
results respectively own references to F/Y and Drop/F/Y under the approved
nested Apply rule. No edge is inferred merely from containment of the inner
Apply result in the outer Apply.

The attempted demand is still generated in G while referring to the active F
root. Its normative extrusion occurrence therefore uses the selected origin
G and receiving F. If its actual retained pairs include `(C,B,+,2)` and
`(D,R,-,2)`, SCC qualification equates C=B and D=R. The shifted level 2
replaces the earlier level 1 because f is now a local initializer under Q.
This is an application of the selected event meaning, not an observed
compiler event record: current ApplySourceInput carries Q as owner and lacks
the G/F event endpoints. It cannot authenticate that record from `owner`
alone (`candidate_source.rs:401–410`, `candidate_call.rs:30–47`).

## Constructor equations and conditional discrimination

The actual candidate source owners supply the following value constraints;
facade rows are retained rather than silently identified:

1. Integer/Unit formation gives `int+ <: V_0 <: int-` and
   `unit+ <: V_unit <: unit-`, plus pure expression-effect bounds
   (`candidate_source.rs:336–351`). Parameter Names use their actual parameter
   endpoint directly (`:210–217`).
2. Each Lambda admits a four-port Function, with its negative formal and
   positive body result. Bare formals force their argument computation at
   entry; entry and body effects flow to a distinct return-effect row
   (`lib.rs:11233–11347`). No body/invocation port equality is assumed.
3. Each Apply requests
   `callee+ <: Function(argument+,argument_effect+,invocation_effect-,result-)`;
   callee evaluation and invocation effects flow to application effect
   (`shadow_apply.rs:1335–1443`). Group/Block result facades retain directed
   child-to-result links (`candidate_source.rs:437–473`).
4. For `first:int`, annotation formation parses `int` as the authentic Int
   constructor (`source_annotation.rs:307–330,399–421`). Preflight admits this
   primitive annotation (`candidate_source.rs:83–138`). Local annotation
   construction checks the original initializer against the negative target,
   then exports its paired positive target; initializer effects remain on
   the block edge (`candidate_effect.rs:1126–1177`). Hence the actual first
   consumer supplies `V_firstcall <: int-` before its local publication.
5. Negative extrusion reverses the Function argument polarity and preserves
   result polarity (`candidate_extrusion.rs:210–250`); a younger row is copied
   with its actual parent retained and one directed source link (`:95–126`).

These constructors motivate the native value projection below, with B the
g formal, S the g body result, R the recursive f-call result, and o the f
root. This projection is a **candidate assumption**, not a complete Call law:

```text
o <: Function(B,R) at level 3
  => B <: C, D <: R, o <: Function(C,D) at level 2
drop's value behavior: Function(Z,B)
drop (f y): R <: Z_use, B <: S
g publication: Function(B,S), boundary 2
use 0: int <: B0 <: S0 <: V0 <: int
use 1: unit <: B1 <: S1 <: V1
f completion: Function(A,V1) <: o
```

The wrapper's ignored argument separates returned B from recursive result R.
The extra local drop generalizes only its fresh Z above boundary 3; its
captured B at level 3 is kept. This differs from pretending the discarded
call is a nested unused binding: that different source owner would remove
G's own direct f reference and needs a different SCC derivation.

**Conditional fixed-anchor implication:** if original source admission yields
this correlation, if C is fixed at g publication while B/S are templates, and
if C=B is active before both uses with equality preserved to that same C,
then `unit <: B1=C=B0 <: S0 <: V0 <: int`. The distinct primitive comparison
is incompatible (`lib.rs::incompatible_value_shapes`, lines 14045 onward).
Source Generalize's whole-frame substitution gives this implication only
after the exact fixed/template and active-program premises are established.
Numeric levels alone do not establish them.

The projected constraint program without equality has an algebraic assignment:
`C=A=int|unit`, `o=(int|unit)->unit`, `D=R=Z_use=unit`, original `B=S=bottom`,
first fresh `B0=S0=V0=int`, second fresh `B1=S1=V1=unit`.
This checks value-level consistency only. It does not demonstrate operational
success, complete Yulang source typing, lawful source witnesses, actual
publication classification or effect/receiver correctness.

## First admission obstruction and ordinary-envelope boundary

The candidate belongs to the intended ordinary **source-form envelope**:
resolved recursive locals, independent local uses, small sequential blocks,
bare flexible parameters and a primitive annotation. Selected Source Generalize
§3.1 supplies precisely Literal/Parameter/Lambda/Bind/Call/recursive schemas.
No selected rule restricts this shape because recursion may diverge during
evaluation. The top-level principles require natural inference for supported
ordinary behavior. This establishes envelope relevance, not original typing.

The first missing original typing evidence is the innermost `f y` Call,
encountered before the wrapper Call in source evaluation/constructor order.
`CandidateSourceCall` explicitly presents native fields as pending inputs,
not original typing; `candidate_call.rs:83–124,215–250` still requests for
**every** Call:

* OriginalGenCall0 (all original B/X/Xi/Delta/declaration/argument/registered-root/
  complete-demand/beta/lexical-use/call/checking/output/ElimOrigin coordinates);
* ArgumentReifyAndWholeCarrier;
* ReceiverDispatchAndCompleteResultFutureInterfaces.

Here callee f resolves to a local, so `formal_name` is absent: this specific
Call does not request the extra *lexical formal-callee* supplier trio. The
unconditional three suppliers remain. In Source Generalize's selected §3.1
Call schema, the corresponding absent premise is the original whole inert
argument, actual receiver/receipt and entry/consumer/invocation return law.
The stored four-port demand is not that proof. No checked source rule was
found that **rejects** this candidate; the obstruction is missing admission
evidence, not an invented source restriction.

Even completing that Call leaves the exact simultaneous recursive introduction
and g publication's Internal/Established/Desc classification and extrusion
equality transport premises to be established. This artifact therefore stops
at one candidate plus the first precise obstruction. It does not refute the
selected intrusion operation or close the parent A/B gate.

## Checks, resources and frozen dependency snapshot

Commands: bounded `sed`/`rg`/`cat` source reads; `git rev-parse HEAD`,
`git branch --show-current`, `git status --short`, `git diff --name-only`;
SHA-256 snapshots and final path/whitespace integrity. No parser, runtime,
test, build, experiment, benchmark, seed enumeration, mutation or Git mutation.
Coverage: one source candidate and its direct producer/consumer seams.
There is no independent executable oracle; authority and candidate source
share the stated Simple-sub interpretation, while the original Call bridge
is deliberately left unproved. A fresh independent `compiler_referee` review
passed the bounded candidate/conditional-obstruction claim. Its minor finding
on the owner of the `g 0` Name is repaired above; the exact-baseline hash audit
found all 15 recorded source dependencies unchanged. Reviewer identity:
`/root/two_use_intrusion_current_baseline_review`; effective model/effort
unknown. Peak RAM/CPU and precise elapsed worker time were
not measured; shell work was lightweight and sequential except independent
read commands. Runtime model/effort metadata: unknown.

Direct dependencies (SHA-256; none edited by this producer):

```text
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389 notes/design/2026-10-11-yulang-inference-top-level-principles.md
0063b88d17104f85182439d80360e42f8f99a5af4793eab70640a66f955ede25 notes/design/2026-10-12-intrusion-value-type-association.md
6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b notes/design/2026-10-10-parent-copy-scc-intrusion.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38 notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 notes/theory/2026-10-08-source-generalize-definition-and-proof.md
08b963a7e2356a400dcb05b53c6fe6d3a917abe9e0df1582779c5c83858eb4f8 notes/theory/2026-10-12-extrusion-occurrence-intrusion-proof.md
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed crates/yu-hir/src/module/local_source.rs
a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb crates/yu-hir/src/module/source_annotation.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49 crates/yu-solver/src/candidate_source.rs
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35 crates/yu-solver/src/candidate_call.rs
cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411 crates/yu-solver/src/shadow_apply.rs
ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df crates/yu-solver/src/candidate_effect.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1 crates/yu-solver/src/candidate_scheme.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0 crates/yu-solver/src/candidate_extrusion.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94 crates/yu-solver/src/lib.rs
```

Recommended next action: route this exact `f y` original Call derivation and
its whole argument/receiver/entry/return premises to the owning constructive
lane. Do not count another native value projection as original admission.

## Commit packet

* Exact leased path: `notes/progress/2026-10-12-intrusion-admitted-two-use-witness.md`.
* Baseline SHA: `e5e7b5878ced01b8cc4682492b6187c3907fd014`.
* Dependency changes: none by this producer; the current-baseline review
  revalidated all 15 dependency hashes against `5cb4ba6f9cc8fa65d347c3b53b6d4e6e5196d02f`.
* Review status: independent bounded PASS; the minor ownership correction is
  closed by primary inspection. No theorem promotion, production conformance
  or semantic-counterexample status.
* Checks: static source correspondence, authority/hash/path and whitespace
  integrity only; no executable verification authorized or performed.
* Proposed message: `research: isolate supported two-use intrusion candidate and Call obstruction`.
* Shared-record deltas left to primary/curator: retain parent gate OPEN;
  record this Unit replacement and the specific original-Call admission owner,
  separate from fixed-anchor allocation and equality/frame transport. No
  task/index/theory-map/authority/question file changed.

Writes stop at handoff.
