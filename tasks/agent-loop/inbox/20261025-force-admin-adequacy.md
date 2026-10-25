# N — Force administrative trace adequacy, revision 1

Status: **FROZEN candidate interface and source characterization; O-NORM OPEN**.
No Lean declaration, compiler code, test, build, Git operation or scratch output
was written or run. This report is not independently reviewed or certified.

## Assignment and parent application

Sprint `FORCE-ADMIN-RESULT-DISCHARGE-20261025/r6`, contract
`tasks/agent-loop/sprints/force-admin-result-discharge-20261025-r6.md`, SHA-256
`972a6cd97e340e1d0d0564e0f76a21021cf1877b7ba21f1df1db7aa56ba1b581`.
Assignment/handoff ID `N-force_admin_trace_adequacy`, revision **1**.
Author `/root/force_admin_trace_prover_r6`, parent `/root`, session
`FORCE-SOURCE-REALIZATION-20261025/root-turn-1`. The received assignment and
subsequent primary messages establish this active source-only stage.
Requested model/effort: `gpt-6.1-sol`/`high`; observed model/effort: **UNKNOWN**.
No coauthors, descendants, reviewer appointments or delegated leases.
Baseline supplied by current contract state:
`9b945b0bb175e8e0919d388dc720babbdf0c2464`; no Git inspection was performed.
Sole leased/new/changed path: this file. Stage-two
`notes/theory/lean/YulangClosure/ForceAdmin.lean` remains **UNISSUED**.

The parent is complete Lean semantics/inference, with source-realization
O-NORM and O-RESULT, Call S/C, Call A/B and full closure OPEN. N applies to
O-NORM's administrative observation seam only. It does not assert a source
inference restriction, foreign-suffix theorem, Force result Flow row, finite
termination theorem, or production authority.

**Actual result:** an explicit independent recursive observation judgment and
a corresponding counted zipper expansion can be stated without Call typing or
projection-defined source successors. Their proposed two-way theorem concerns
finite successful observations of that syntax. Its essential remaining
source premise is the concrete whole-packet specialization of a peeled View
around a polymorphic head. The paper requires that operation, but the pinned
Lean modules do not encode it. A theorem parameterized by that operation is
an abstract administrative-machine theorem, not complete paper-to-Lean adequacy.
Malformed intermediate applications and missing graph references additionally
need independently specified error constructors before claiming all raw
observation-successor coverage. These omissions are explicit below.

## Frozen dependency receipts

All entries below were read and SHA-256 matched against r6. The table is a
byte receipt, not a claim that unchecked declarations in those files are proved.

| Input | SHA-256 |
|---|---|
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `tasks/agent-loop/inbox/20261025-force-result-flow-derivation.md` | `a849f178fbc55eb653c2fc4295e4b4675935e7c904cbef7da5100edb0b983212` |
| `tasks/agent-loop/inbox/20261025-force-source-input-equations.md` | `d7f8853e07cf2ec73fb99d3cbe045f3ab5b2e6f5626469417648a9fbfc313f88` |
| `tasks/agent-loop/inbox/20261025-force-source-mapop-correction-r5.md` | `203d55dc462046f0616eba027198c68224182fdf4ab03bf19ccb87548c691b8b` |
| `tasks/agent-loop/sprints/force-source-mapop-correction-20261025-r5-outcome.md` | `04e93d203dbf09f2421be4ef988328330ccecb5997b3e01564178d8b195ed823` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| `CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `CoreSubstitution.lean` | `fc73d6d60d28f2abb54049a5715751d27df47ad93dbeb8f52966cf98a747bd2f` |
| `ControlTyping.lean` | `e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f` |
| `ControlComposition.lean` | `9a48a5f2ef15eb947478757e0fa74457579183ccdbab90f2518886590e33fc40` |
| `CoreControlBridge.lean` | `30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a` |
| `CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |

Module paths in the final seven rows have prefix
`notes/theory/lean/YulangClosure/`. Toolchain content is
`leanprover/lean4:v4.35.0`; Lake sets `-j1` and `-M1024`. These were inspected,
not invoked. The proposed minimal imports are `YulangClosure.CoreSubstitution`
and `YulangClosure.Contracts`; no Control/Call declaration is a theorem premise.

## Source owners and exact scope

All source line numbers refer to the pinned operational paper.

* 258–269: closed capture-avoiding substitution; immutable finite value graph;
  observe one outer node by following references; typed guard supplies an
  additional termination argument. A raw graph is not assumed guarded.
* 301–307: only the active computation runs; Delay/lambda children remain
  latent; `Force(Delay M) -> M`; wrong required constructor goes to `Bad`.
* 316,321: actual type beta and counted type/View administration.
* 331–335: only let/scope/expose/handle/mapop/wait have an active computation
  child; its one step lifts through those frames with their payload unchanged.
* 472–483: current read interpretation acts on metadata; stored shared values
  remain unchanged; protocol responses are reads, not graph-memory lookups.
* 485–494: preserve View metadata; Force exposes the body; reference, type
  application and View outer removal are administrative steps; no traversal
  inside the constructor.
* 1241,1541: one type/dictionary instance acts on the entire packet, including
  row/profile/family/latent occurrences. 1244 stores Delay/lambda code and
  captures; 1245 and 1532 distinguish `force.effect` and `force.result`.

The following is an explicit candidate representation of those administrative
shells. It is not already an executable producer in the pinned modules.
`Raw` below is `YulangClosure.Original.Raw`. Every opaque child, type argument,
metadata packet and binder body is retained, including its original identity.

```text
V ::= ref r | app V A | abs b | view chi V | node k
r : Nat; A,b,chi,k : Raw
Head ::= abs b | node k
H : Nat -> Option V                         -- supplied immutable finite graph
beta : Raw -> Raw -> V                      -- body, argument -> substituted body
inst : Raw -> Raw -> Raw                    -- argument, complete View packet
W := List Raw                              -- outermost-to-innermost wrappers
```

`node k` is an outer-constructor barrier. Its payload is never recursively
observed. Delay, lambda, wrap, top, roll, both, tuple/record/variant, literal,
continuation and malformed raw arities remain full `k` payloads. `abs b` is
also a barrier until an actual enclosing type application consumes it.
This grammar must come with a disjoint, lossless source encoding: administrative
forms may not be hidden as `node k`. No pinned function currently supplies
that encoding for all source packets.

`beta` is deliberately not an arbitrary semantic reduction in the source
claim: its required realization is capture-avoiding substitution of the actual
type argument in the actual retained binder body, including all metadata.
`Original.substituteRaw`/`liftSubstitution` provide raw binder machinery but
not the missing complete decorated source encoding. `inst` is the distinct
whole-polymorphic-packet specialization required by 1241/1541. Merely applying
type index-0 substitution to a metadata Raw tree outside the type binder
does not establish that law. A packet descriptor/template representation and
its realization are required; neither operation is defined through execution.

## Independent source judgment and trace constructors

The finite successful source judgment has indices
`SourceObserve H beta inst v tr h W`, with `v : V`, `h : Head`, and
`tr : List Event`. It is defined by the following four constructors, directly
from source syntax/graph lookup, before any projection or zipper is defined.

```text
Event ::= ref r v | typeBeta b A v | peel chi | inApp A Event

head:
  SourceObserve (headValue h) [] h []

reference:
  H(r) = some v     SourceObserve v tr h W
  ------------------------------------------------------------
  SourceObserve (ref r) (ref r v :: tr) h W

view:
  SourceObserve v tr h W
  ------------------------------------------------------------
  SourceObserve (view chi v) (peel chi :: tr) h (chi :: W)

application:
  SourceObserve f tr1 (abs b) W1
  SourceObserve (beta b A) tr2 h W2
  ------------------------------------------------------------
  SourceObserve (app f A)
    (map (inApp A) tr1 ++ [typeBeta b A (beta b A)] ++ tr2)
    h (map (inst A) W1 ++ W2)
```

`H`, `beta` and `inst` parameters are fixed in all premises of each rule.
Reference events retain the exact returned value rather than only a reference
ID. Type events retain the binder, argument and substitution result. Peel
events retain the complete packet. `inApp` records the exact pending type
argument and the observed function position. Thus these are ordered, counted
events with retained provenance, not an unordered lookup log.

Wrapper composition is literal ordered concatenation. With `wrap` denoting
the unmodified syntactic View nesting,
`wrap [] v = v`, `wrap (chi::W) v = view chi (wrap W v)`, hence
`wrap (W1 ++ W2) v = wrap W1 (wrap W2 v)`. No commutativity, idempotence,
union, cancellation or metadata equality is assumed. In particular an outer
View around the *application* is not specialized a second time.

These are proposed source-realization equations, not paper-printed judgment
constructors. The reference, beta and peel order follows the outer observation
rules; the exact `map (inst A) W1` interpretation is the unestablished
source-owner law identified above. Leaving `inst` arbitrary makes only the
abstract correspondence below true. It cannot certify that this rule realizes
every source polymorphic packet.

## Concrete focus expansion and counted trace theorem

The separate candidate observation machine has state
`Focus = (current : V, pending : List AppFrame, wrappers : W)` where
`AppFrame = (argument : Raw, savedOuterWrappers : W)` and pending frames are
nearest first. The machine's rules are:

```text
focus [scheduling only, no source step]:
  (app f A, K, W) => (f, (A,W)::K, [])

reference [one counted ref event]:
  H(r)=some v
  (ref r,K,W) -> (v,K,W)

peel [one counted peel event]:
  (view chi v,K,W) -> (v,K,W ++ [chi])

typeBeta [one counted beta event]:
  (abs b,(A,W0)::K,W)
    -> (beta b A,K,W0 ++ map (inst A) W)
```

The event of a counted rule is lifted through pending frames:
`lift [] e=e`, `lift ((A,W0)::K) e=lift K (inApp A e)`.
For beta, lift through the **remaining** K after consuming A. For reference
and peel, lift through the unchanged K. The focus move is an equality of
representation focus, not a counted paper transition. A derivation may not
charge it a source step, and may not erase ref/peel/beta steps instead.

For example, observing `view c (app (view d (ref r)) A)` with
`H(r)=abs b` yields exactly
`[peel c, inApp A (peel d), inApp A (ref r (abs b)),
  typeBeta b A (beta b A)] ++ trBody`, with final wrappers
`[c] ++ [inst A d] ++ WBody`. The view c outside application is retained
without passing through inst. Delay body evaluation is absent from this trace.

Define `AdminMicro H beta inst : Option Event -> Focus -> Focus -> Prop`
by precisely these four rules. Define `CountedRun` inductively by reflexivity,
a silent focus edge that preserves the event list, and a counted edge that
conses its emitted event. A run is finite evidence; neither fuel nor a cycle
error is introduced. The proposed Lean declaration/signature is:

```lean
namespace YulangClosure.ForceAdmin
-- V, Head, Event, AppFrame, Focus, SourceObserve, AdminMicro,
-- CountedRun are the constructors specified above, not imported Call fields.
theorem force_admin_trace_adequacy
    (H : Nat → Option V)
    (beta : Original.Raw → Original.Raw → V)
    (inst : Original.Raw → Original.Raw → Original.Raw)
    (v : V) (tr : List Event) (h : Head) (W : List Original.Raw) :
    SourceObserve H beta inst v tr h W ↔
      CountedRun H beta inst tr
        ⟨v, [], []⟩ ⟨headValue h, [], W⟩
```

This is a precise two-way statement about all finite successful derivations
of the independently defined source relation. Neither direction has a typing,
Call, Delay, termination, projection-successor, or preservation assumption.
Its parameterization is visible: it proves no source law about beta/inst.

Proof plan: strengthen forward simulation to arbitrary pending K and incoming
W0. Observation from `(v,K,W0)` appends wrappers as `W0 ++ W`, emits
`map (lift K) tr`, and does not consume K; a phase delimiter or a run cut at
that endpoint states this local segment. Induct on SourceObserve. Application
uses focus once, the first induction hypothesis up to its abs endpoint,
the actual beta edge, and the second induction hypothesis, with associativity
of lists and map/append. Reverse simulation parses a successful finite run
using the top source constructor. For app, locate its first pop of the fresh
app frame; its only successful pop rule is beta. Split the run there,
invert the function segment and body segment, and rebuild application.
References/views invert their first counted event. The finite run and stack
discipline justify these splits; no existence of an observation is assumed.
The statement about K is a local observation-machine lemma, not FK1 or an
arbitrary source continuation theorem.

Useful auxiliary conclusions, applied to this parent seam: the number of
source administrative steps is exactly `tr.length`; focus contributes zero;
every emitted reference/beta/peel is present in order in both derivations;
every successful wrapper is retained in W or transformed once by an actual
enclosing type application. These facts remove the opaque one-lookup shortcut
from P's proposed finite spine, but only once its concrete beta/inst owners
and source encoding are supplied. No decoder may invent additional events.

## Force dispatch, context composition and missing raw cases

After successful observation, source Force dispatch is independent of Call
typing. If h is the actual well-formed Delay constructor with retained M,
the next principal Force step runs M with the retained effect exposure;
for nested wrappers the required syntactic nesting is outer-to-inner,
`expose effect(W[0]) (... expose effect(W[n]) M ...)`. The complete packets
remain associated with their distinct result specifications. This statement
does **not** construct Force-result transport or instantiate an abstract
`effect` selector from arbitrary Raw metadata.

If the observed h is any other outer constructor, the raw Force step is
`Bad(malformedForce)` by 303–307. In particular wrap is a callable constructor,
not a transparent thunk; top, roll, both, data, an unapplied abs and a
continuation are not recursively searched for Delay. No theorem
`CallStateTyped -> ...` is used to define either raw branch. A Delay whose
body later fails still first enters the actual body; observation does not
execute it. A malformed Delay arity is in the malformed branch, not Delay.

For external computation frames F from 331–335, `plug [] M=M` and
`plug (F::L) M=plug L (F[M])`; hence
`plug (L1++L2) M=plug L2 (plug L1 M)`. A counted source step at the current
Force position lifts through these exact retained frames, with no step for
decomposition. Full View frames retain metadata/saved ambient and source
payload; `Control.Frame.view identity` alone is insufficient. Enter/leave
ambient operations and result transport are later machine steps, not free
focus or administrative beta. The candidate theorem above does not certify
those operations or all possible outer continuation actions.

The present successful-observation theorem omits these cases explicitly:

1. `app f A` whose function observation reaches a non-abs head. This must
   produce a malformed-type-application Bad before Force dispatch, with its
   own error trace and retained pending packets. No terminal-Delay hypothesis
   repairs this absent raw constructor.
2. A missing/ill-formed graph reference or raw local. The paper specifies Bad
   for unbound locals; a lossless source decoder must keep them distinguishable
   from a valid graph edge and identify the exact raw-reference error owner.
3. Unguarded reference cycles: no finite observation is promised; no fuel or
   cycle-to-Fail transition is added.
4. Read interpretation: theta acts at actual source reads. It must be applied
   once before the corresponding packet enters this observation syntax.
   There is no unconditional extra counted `read` event, nor a protocol-to-H
   lookup rule. General protocol code remains an actual computation.
5. Complete metadata specialization/result-path interpretation, source-to-V
   encoding, and composition with View enter/leave. These are source bridges,
   not consequences of the abstract two-way theorem.

Typed terminal Delay/canonical forms is a **separate** obligation: from the
retained full source typing/graph-typing derivation of the operand at thunk
type, prove that successful outer observation ends in actual Delay, and prove
observation exists under the accepted guardedness assumptions. Existing
`Original.closed_thunk` covers only its older finite Val fragment, which lacks
graph/type/View constructors. It cannot supply either fact for this source
domain. Typed termination also cannot establish raw successor coverage.

## Prior work, mutual TODOs and stop receipt

Reused P's finite-spine requirement and separate effect/result accounting;
P explicitly left O-NORM open. Rejected treating its `enc(d)` as a proof that
source d exists, treating r9 Call fields/metadata IDs as packet provenance,
or treating fragment `closed_thunk` as a complete source canonical-form lemma.
The CLEAN r5 mapop correction remains binding for later context/native work;
this observation theorem contains no mapop continuation transformation.
F's result rows and PathRule.adapterMap supply no N premise.

* **N-META-INST-1**, owner Luna/source-decoration producer at paper
  1241/1541: retain the concrete polymorphic packet/template representation,
  body encoding and simultaneous substitution; derive `inst` and the displayed
  application wrapper equation. Output should be the smallest approved or
  provisional source-definition/proof packet, not compiler edits from N.
  Falsifier: `view c (app (view d (abs b)) A)` with distinct c,d and a d
  containing a delayed latent/profile coordinate affected by A. Incorrectly
  specialize c, omit that coordinate, or apply the instance twice, and the
  required wrapper/latent result differs. A test of an assumed inst is not
  evidence that the actual decorator constructs it.
* **N-RAW-ERROR-1**, owner Luna/source normalization producer at paper
  287–290,303,490–494: extend the independent source relation and zipper with
  precise malformed-application/reference/local error constructors and their
  counted traces, retaining pending metadata. Falsifier: Force of an app
  whose function is literal unit must reach Bad independently of Call typing;
  it must not stop successfully at that literal or enter a latent payload.
* **N-CANONICAL-1**, owner full source-typing/graph-typing lane: derive finite
  observation and terminal Delay from retained thunk typing/guarded graph,
  covering type/View/reference constructors. Output is a separate theorem;
  falsifier is any accepted typed thunk packet whose successful observation
  has a non-Delay head. This TODO does not assume that such a packet exists.
* **N-INTAKE-1**, owner Luna: independently review this frozen interface and
  decide whether the explicitly abstract successful-trace theorem merits an
  activated Lean lease while the source inst/error bridges remain OPEN.
  No interface below an opaque inst parameter closes O-NORM.

Checks performed: bounded source/module reads, constructor/consumer searches,
and exact SHA-256 equality for every r6 input and the contract. No theorem
checker, test, build, experiment, compiler/native execution or external source
was used. CPU/memory usage unmeasured. One observed clock receipt during work
was `2026-10-25 00:34:12 UTC`; no trustworthy launch timestamp was captured by
this worker, so total elapsed is **UNKNOWN** and the conservative resource
charge is the entire **1,200-second** assignment, with **0** unspent seconds
claimed. Luna may use its own actual launch receipt to reconcile elapsed;
this report does not infer a fresh budget. No Astra resource was used.

Stage-one stop condition reached: source candidate/proposition and exact
remaining premises returned. Writer state **STOPPED** after final artifact
digest receipt; no descendants or unresolved descendant leases. No new/scratch
paths besides this single inbox artifact. Independent source review and Luna
adjudication pending. Next in-envelope step is review intake; conditional Lean
writing needs Luna's explicit lease activation and remaining-resource receipt.
This producer is ineligible to certify this or a combined N/R result.
