# P — Source-indexed Force inputs and projection equations, revision 1

Status: **FROZEN research candidate; correspondence and independent review OPEN**.
Assignment: P, `FORCE-RESULT-SOURCE-EQUATIONS-20261025/r4`, contract SHA-256
`0574716388f51878a02d589780208746de292ea141a5e92f608dce1eba955e51`.
Author/runtime identity: `/root/force_source_input_research_r4`; primary `/root`
launched this packet in the current r4 session. Requested Sol/high; observed
model/effort UNKNOWN. No descendants. Sole write lease is this file.

## Objective, method and claim boundary

Give source-indexed input, resolution, context, saved-View, cut and suffix
equations, keeping F's Force-result relation unresolved. Method: textual
constructor audit of the frozen operational paper and current candidate Lean
carriers, with symbolic discriminators. No executable checker, theorem proof,
production implementation, or independent certification is claimed.

The equations below have three explicit statuses:

* **S**: transcription or direct structural consequence of cited source rules.
* **R**: candidate representation definition, requiring correspondence before
  adoption. It changes no selected language meaning.
* **O**: exact open input/equation. In particular, an R trace records source
  administrative derivations; it does not prove that these derivations exist.

The paper supplies the semantic owner. It supplies no ready-made Lean record
projection. The r3 capture is a rejected candidate, the typed-boundary file is
Draft, and the r9 Lean carriers are unchecked candidates. No equation below
uses the Draft as authority. No observable semantic ambiguity is established
by this packet.

## Frozen dependency receipt

Pinned baseline: `9b945b0bb175e8e0919d388dc720babbdf0c2464`; read-only
`git rev-parse HEAD` returned that SHA. The contract, rather than current.json's
older `5ef9f200096d47d864f21bc5b78a245b5804574c` field, supplies this packet's
baseline. This discrepancy was returned to Luna; no shared record was edited.
Every r4 file pin matched:

| Exact dependency | SHA-256 |
|---|---|
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `tasks/agent-loop/inbox/20261025-force-view-source-producer-investigation.md` | `90506b6c8cf98487690550b95255e37806a79ab527646d1bf12192dfb82dfc1c` |
| `tasks/agent-loop/sprints/force-source-realization-20261025-r2-outcome.md` | `520cf5cb0c716271b9a10872df0c376684d11b8c92df018e01c91f8dbe92e672` |
| `tasks/agent-loop/sprints/force-projection-design-20261025-r3.md` | `b9d7453a0ea6e782cbfd7f6a78e88bbb7a723546bc130a8b8990fdc6c1a56b29` |
| `tasks/agent-loop/inbox/20261025-force-projection-design-r3.md` | `a255b7c7e84ba608b0fa42372455560c90e9bc59428865f452e351f11e18de77` |
| `notes/theory/lean/YulangClosure/CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `notes/theory/lean/YulangClosure/ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `notes/theory/lean/YulangClosure/ControlTyping.lean` | `e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f` |
| `notes/theory/lean/YulangClosure/ControlComposition.lean` | `9a48a5f2ef15eb947478757e0fa74457579183ccdbab90f2518886590e33fc40` |
| `notes/theory/lean/YulangClosure/CoreControlBridge.lean` | `30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a` |
| `notes/theory/lean/YulangClosure/CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `notes/theory/lean/YulangClosure/CoreSubstitution.lean` | `fc73d6d60d28f2abb54049a5715751d27df47ad93dbeb8f52966cf98a747bd2f` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |

All paper line citations below refer to the first row's exact bytes.

## 1. Actual typed input and ownership

**S.** Paper 1180–1192: input is resolved typed syntax carrying declaration
identities, type instances, source annotation occurrences, lambda introduction
sites and selected member/adapter code, with remaining binders in Delta/Gamma.
It is not source text, a successful inference invocation, or a bare erased
type. Paper 1550–1562 requires the earlier derivation, decoration d, finite
Horn closure and all-output inclusions under every consistent joint eta.

**R.** An executable input envelope should expose these separately:

```text
I = (Delta, declarations, typed syntax T, derivation D,
     declaration/code-table derivations, shared instance substitution sigma)
Decor_F(I) = structural decoration of D and T, indexed by static labels
TypedMachineInput_F = (I, Decor_F(I), H, graph-typing witness Xi,
                      source configuration s, lineage witness L)
RawMachineInput = (declarations, H, source computation, concrete omega)
```

`D` is the actual finite syntax derivation; a purported `D` must have conclusion
the same T. Decoration is associated by construction/erasure equations,
not an unrelated `SourceDecoration` argument. `erase(Decor_F(I))` is the
paper's explicit code of T (1276–1290). Static labels are assigned to those
nodes (1233–1234), not fabricated later from runtime IDs. Sigma acts on the
entire instance, including ordinary conditions, row/profile/family witnesses
and all latent ports (1541, 1735–1755).

The subscript F records the one open Force-result relation in section 7. It
does not make unrelated rules depend on F. Raw configurations and raw steps
do not require I, D, L, `CallStateTyped`, or any successful typing witness.

For a labelled Delay introduction with D's premise `Gamma |- M : A`:

```text
delayPayload(ell,D,env) =
  (ell, exact body M, D's body subderivation, its decorated body graph,
   [(x, env(x), declared type/profile of x, body-use labels of x)
     | x is a free lexical binding of M])
```

**S/R boundary.** Retaining code/captured views, body force graph and shared
free packets is S (1244, 1531). Packaging subderivations and use labels into this
record is R. Closure allocation enters no executing View and does not pretend
creation-time activity is later force-time activity. No closed-body premise
is added: env packets may reference H and current interpreted views.

Packet lineage L is inductive source evidence, not a set of equal type IDs:

| Source producer | Required retained lineage / consumer |
|---|---|
| Delay introduction | Body subderivation, lexical packet bindings, force graph; later Force formation |
| Variable/binding | Actual original packet, fresh alias occurrence, identity Flow; Force operand/capture reader |
| Structural construction/projection | Actual components, executed prefix insertion/removal templates; component packet reader |
| Type/dictionary application | One simultaneous instance on the whole packet and retained templates; later body and port instantiation |
| Reference/protocol response | Actual response packet plus current read interpretation; later eliminator |
| Normal return | Actual returned packet and all latent ports, fresh output occurrence, licensed transport; enclosing consumer |
| Capture | Exact frame/packet spine and scope of bound names; resume formation |

These cases come from 553–558, 578–585, 1238–1257, 1528–1542. Dynamic
occurrences record actual operations, not merely equal underlying constructors.
Captured-binding `Receive` is made at actual execution entry in the current
invocation slot (1256–1257), using each captured packet's real transport.
Force creates no source Call receiver. If no source invocation slot is supplied,
one cannot manufacture a fresh receiving owner to complete this equation.
The source decoration/representation owner must expose the actual slot.

## 2. Raw Force observation and counted administration

**S.** Paper 258–261 and 263–269 gives closed substitution / finite immutable
graph references. Guarded typed graphs reach an observable constructor;
303–307 gives bare Force/Delay and malformed elimination; 316, 321 and
490–494 counts type/View/reference outer normalization as administration.
The body is not evaluated while resolving a value. General mutable reference
protocols are not H lookup: their explicit code must run and their returned
packet is read under theta (472–483).

**R.** Avoid the r3 opaque `resolveH(v)=Delay`. Retain a finite derivation
spine with one constructor per source administrative observation. A usable
result is `Resolved(trace, node, wrappedEvidence)` or `RawError(trace,reason)`.
The following are constructor equations for its *encoding*:

```text
enc(IdNode(k))                 = ([], k, [])
enc(Ref(r,H(r),d))             = prepend(ref(r,H(r)), enc(d))
enc(TypeBeta(alpha,v,A,d))     = prepend(typeBeta((Lambda alpha.v)[A],v[A/alpha]), enc(d))
enc(TypeCongr(v ->adm v',A,d)) = prepend(typeCongr(v[A],v'[A]), enc(d))
enc(ViewPeel(chi,v,d))         = prepend(viewPeel(View_chi(v),v,chi), enc(d))
enc(Read(ell,theta,d))         = prepend(read(storedView(ell),theta*storedView(ell)), enc(d))
enc(Error(reason))            = ([], RawError(reason), [])
```

`prepend` adds an ordered trace item and composes its interpretation/typed
transport on the carried packet; ViewPeel also retains chi in an ordered wrapper
spine. It never throws chi away. Read is an interpretation equation on an
actual variable/projection/protocol response; this record does not assert a
universal extra runtime read step or turn a protocol into a memory cell.
Reference/type/View source steps each remain separately indexed; `enc` is
not permission to contract their trace to one lookup. TypeCongr only transports
a source-provided normalization step, not an arbitrary reduction under latent
code. For a local variable, use the existing closed substitution; an unbound
local has raw Bad (287–290), rather than consulting an inference environment.

For a finite supplied source observation derivation d:

```text
resolveTrace(d, H, theta, v) = enc(d) with every row's source and target checked
terminal Delay(M): dispatch Force(Delay M) -> M
terminal k other than Delay after licensed outer normalization:
                  dispatch Force(k) -> Bad(malformedForce)
```

The dispatcher has no typing premise. In particular, Force of a function
`wrap(f,a,r)` is Bad; function wrap is not a magic transparent thunk wrapper.
`top`, `roll`, `both`, pairs, records, variants, constants, unapplied type
abstractions and continuations do not become Delay by recursion into their
payloads. Their own explicit eliminators must run first if prescribed by code.
The paper's inert thunk adaptation is actual `Delay(let z <- Force t in a(z))`
(368), whose body remains latent, not a new unspecified raw wrapper kind.

**S.** Interpreted outer View metadata exposes the forced body and retains
separate result-path metadata (485–494); decorated Force executes the forced
packet's `force.effect` View (1245, 1532). The wrapper spine above must therefore
feed that explicit exposure/decoration rather than get erased at dispatch.

**O-NORM.** The paper prints the type beta and bare Force beta equations, but
states reference/View outer observation and their instruction integration in
prose. It does not print a binary normalization judgment with all focus,
wrapper-composition and administrative scheduling constructors. The equations
above deliberately consume those source administrative derivations rather than
claim to prove them. They do not determine whether a particular implementation
uses an intermediate pending-exposure head or a normalized operand register.
An exact one-source-step/one-target-step theorem needs the normalization owner
to freeze this expansion and prove its adequacy to 258–261, 321, 490–494.
This is missing executable realization evidence, not a demonstrated semantic
choice. No alternative observable row systems were constructed here.

For malformed unguarded reference cycles, the guarded typed-input termination
argument does not apply. No arbitrary fuel limit, cycle-to-Fail rule or global
raw termination claim is inferred. A finite supplied trace can be encoded;
infinite raw administration remains outside that finite derivation claim.

## 3. Source context decomposition and segment boundary

**S.** The only active-child frames are bind, scope, expose/View, handle,
mapop and wait (331–335, 1012–1026, 1634–1646). A source context is neither an
unordered set nor a list of stored argument occurrences.

**R.** Choose a nearest-hole-first list. Frame payloads are full source data:

```text
B(x,N,env,D_N)       [ ] = let x <- [ ] in N
S(u)                [ ] = Scope_u [ ]
V(spec)             [ ] = View(spec.packet,spec.effectPort,[ ])
H(h,arms,env,D_h)    [ ] = Handle_h [ ]
O(w,codes,env,D_w)   [ ] = mapop_w [ ]
W(h,q,p,K,a,as,env) [ ] = wait_h(q,p,K;a,as;[ ])
plug([],M) = M
plug(f::L,M) = plug(L, f[M])
```

Types/derivations here are extrinsic optional annotations on raw frames;
absence never suppresses a raw step. V retains packet, typed effect path,
result specification, interpretation, source label and lineage. A running V
also retains dynamic occurrence j and saved outer ambient. A saved V does not
restore its former outer ambient on a future branch.

`dec` recursively descends only the one active child:

```text
dec(terminal or principal redex R) = (R,[])
dec(f[M]) = let (R,L)=dec(M) in (R,L ++ [fullFrame(f)])
```

Do not descend a Delay/lambda body or data component, inspect a pending wait's
old continuation instead of its active attempt, or select a handler while
decomposing. The reconstruction equation is `plug(L,R)=M`. The source frame
lemma supplies type-indexed reconstruction separately; `dec` itself is raw.

A segment seam is an **explicit cursor supplied by the source/representation
embedding**, not inferred from a Call type, handler eligibility, ID equality
or a source label. At depth n in L:

```text
cut(0,L)       = ([],L)
cut(n+1,[])    = error(noSuchBoundary)
cut(n+1,f::L)  = let (P,S)=cut(n,L) in (f::P,S)
boundary       = (n, source embedding location, reconstruction witness)
L              = local ++ suffix
```

The sum of lengths and literal concatenation are checkable. A source has no
metatheoretic `originalBoundary` instruction; representing its cursor as such
a marker is policy, not a new source step. The selected-handler capture cut is
a different operation (section 5), not whatever cursor splits a foreign suffix.

For an independently supplied outer context S, local reductions leave the
exact suffix S unchanged until control returns to that seam; no frame from S
is silently processed by a local transition. Observation still sees its
executing Views. At the seam, the owning outer machine executes the next frame's
rule; a segment cannot discard that rule or falsely claim the full machine
has terminated. This is a compositional projection specification, not a proved
arbitrary-suffix theorem.

## 4. Complete suffix Views and saved ambient

**R, mechanically recursive.** For full source frames:

```text
views([]) = []
views(V(spec,j,savedA)::L) = (spec,j,savedA) :: views(L)
views(f::L) = views(L)                         if f is not V
suffixViews(boundary,L) = views(snd(cut(boundary.depth,L)))
```

The output contains complete packets, paths, substitutions and lineage in
literal frame order. It does not stop at a handler or retain IDs alone.
`views(local ++ suffix) = views(local) ++ views(suffix)`. The source paper
592–594 and 1320 supplies the semantic emission coverage: all executing Views,
including those beyond handlers. Captured/stored Views enter this list only
when actually executing. Emission creates immutable Observe rows once; bubbling
does not re-emit (560–572).

**S/R.** Let `pot(spec,w)` mean source-defined potential incidence of its
interpreted packet at its effect port, using Boundary/Flow/Receive (1315–1320).
It is not an arbitrary Metadata callback. Enter and normal leave implement
1352–1356:

```text
enter(spec,currentAmbient A,w):
  allocate fresh dynamic View occurrence j
  push V(spec,j,savedA=A)
  ambient := A union pot(spec,w)

leaveRet(V(spec,j,savedA),actualReturnedPacket z):
  pop precisely this frame
  ambient := savedA
  returnedPacket := result_F(spec,z,w)          -- section 7 only
```

Enter re-observes in the current world. Force uses the current owner and makes
no Call receiver. Shared incidence witnesses require saved ambient restoration;
set subtraction loses an outer View's identical witness. History rows are not
deleted by leave. Packet transport and ambient restoration are different
operations. No F-result edge is needed to define the savedA equation.

The existing carriers lose this information: `ControlSyntax.lean:50–65`
has `.view identity`; `133–158` extracts IDs/erases the result payload;
`284–298` accepts suffix views merely matching IDs. Matching such lists cannot
recover typed suffix View contents. `ControlTyping.lean:120–124` supplies
independent suffix typing, not missing provenance or a View reconstruction
function. `Metadata` at `ControlSyntax.lean:93–103` is not the source equation.

## 5. Req extension and capture cut

**S/R.** A saved continuation retains finite code and a frame list with the
same plug equation. Starting from `K=cont(B,x,N)`, first alpha-convert its
binders to avoid the appended frame's free names. Constructor extension is:

```text
extend(K,bind(y,M)) = cont(B,x, let y <- N in M)
extend(K,scope(u))  = cont(B union {u},x, Scope_u N)
extend(K,view(V))   = cont(B,x, View(savedSpec(V),N))
extend(K,handle(h)) = cont(B union activations(h),x, Handle_h N)
extend(K,mapop(w))  = cont(B,x, mapop_w N)       with same response code/instance
extend(K,wait(h,q,p,K0,a,as)) =
  cont(B union {h},x, wait_h(q,p,K0;a,as;N))
```

Bind/scope/handler/wait follow 339–354, 433–449, 468–470; View persistence follows
485–486 and 1355; mapop uses its actual payload/response construction (703–712),
not a bare invented mapper summary. The compact mapop line denotes framing the
saved response continuation, including those explicit code components; it does
not bypass payload adaptation during the outgoing request transition.
`savedSpec(V)` retains packet, paths, result specification, source position,
interpretation and lineage; it omits a future command to install old savedA.
Appending changes neither the original event nor immutable observations.

In the frame encoding, every case has
`frames(extend(K,f)) = frames(K) ++ [saved(f)]` and unchanged response type.
The binder sets above bind owner/handler names only. The wait binder is its
activation h, not automatically owner(h); the owner is bound only if its Scope
was crossed (446–449). View occurrence freshness at later entry is distinct
from adding an owner/handler binder here. Preserve nested continuation binders
without binding them a second time.

Let the active source context at capture decompose as:

```text
L = inner ++ [Handle(h)] ++ outer
Kinitial = cont(empty,x,Ret x)
Kinner = foldLeft(extend,Kinitial,inner)
```

After sequential source bubbling/eligibility search, an eligible selected
handler gives its arm Kinner, **not** extend(Kinner,handle(h)). Its own frame is
removed for the attempt; outer stays outside Kinner (419–456, 1645–1646,
1695–1697). If the request is forwarded after the required attempts, use
extend(Kinner,handle(h)); then continue outward. Inner contains every frame
actually crossed, including skipped handlers, Views and pending wait data.
This fold is a description of the actual finite propagation derivation, not
an eager algorithm skipping attempts or eligibility. A View outside the selected
handler belongs to outer and remains observed at emission, but is not captured
into that handler's raw continuation. The full source stack, not the segment
cursor, determines this cut.

No normal result transport occurs on Req. Rebuilding the outer executing
context restores its own ambient; saved inner Views persist in K and become
executing only upon resume.

## 6. Current-resumer re-entry and failures

**S.** Paper 460–483, 566–572, 1380–1402:

```text
K = cont(B,x,N)
rho = injective fresh renaming of B, avoiding full current support
Resume(K,a) -> (rho_saved * N)[a/x]
```

The response a is a current caller packet: substitute it after the saved
bound-name action; do not rename it merely because it happens to mention an
old name equal to a saved binder. Well-typed responses are a theorem premise,
not a raw transition premise. Malformed raw continuation/response eliminations
remain Bad. Free names, operation family, State scope, resource identity and
type arguments stay fixed. The same action applies to saved templates,
receipts, packets, pending event observations and later reads. It does not
rewrite global storage, current ambient or packets already instantiated by
another branch. `CoreSubstitution.lean:527–544` only renames lexical value
variables and leaves these fields unchanged; it cannot supply this operation.

**R.** Re-enter crossed saved Views in outer-to-inner execution order:

```text
A0 = currentResumerAmbient
for each re-entered saved Vi, from outermost to innermost:
  V'i = interpret(rho_saved,Vi)
  frame.savedA = Ai
  allocate fresh occurrence ji
  Ai+1 = Ai union pot(V'i,currentWorld)
```

With a nearest-hole-first saved list, this execution order is its View order
reversed; other frame code still executes according to plug. Leave of each
re-entered frame restores its newly saved Ai. One does not eagerly enter every
View anywhere inside N or latent values. The loop describes actual re-entered
delimiters on the active context spine. Pending queries keep their immutable
emission observations under this branch's interpretation and use current
activity when searched again (1657–1671). No replay or new event seed occurs.

**S.** For any one active-child source frame f (331–335):

```text
f[Fail r] -> Fail r
f[Bad r]  -> Bad r
```

Iterate one crossed frame at a time if projecting a finite propagation trace;
do not collapse all frames into one source step. A bare malformed Force is
Bad; `Force(Delay(Bad r))` reaches child Bad, then the same Bad crosses its
exposure/outer frames. Fail stays one of the language failures and never
becomes Bad or a normal result. No failure case calls result_F, allocates a
return packet, emits a request, or invents a failure-world cleanup relation.
The paper does not specify a special observable post-failure ambient cleanup;
terminal failure may be represented without such a projection. A strengthened
world-observing failure theorem would need its own source premise.

## 7. Exact localization of F's open parameter

Write `Theta_F(ell,instance,forcedPacket,bodyResultPacket,sourceLineage)` for
F's unresolved typed Force-result correspondence relation. Its argument list
names available source inputs; it does **not** assert any particular incoming
rows, arity, two-input image, prefix equation or Flow paths. Endpoint types
cannot instantiate it. F owns deriving its exact domain, image and legal row
construction, or supplying the two admissible observable row systems required
to demonstrate genuine underdetermination.

```text
result_F(spec,z,w) = apply the licensed Theta_F relation to this actual
                    body result, forced packet and retained source evidence,
                    with the required fresh output occurrence(s)
```

This is **O-RESULT**, not an executable resolved function. Generic return
freshness/transport follows 553–555, 582–583, 1245; exact Force rows do not
follow merely from those citations. This report intentionally leaves them out.

Theta_F occurs in normal Force result transport and the Force node's result
and latent-port graph, including View result summaries and cut summaries
containing such a leave. It is retained unchanged, under coherent interpretation,
through capture/re-entry. A later `pot`/Path/eligibility query on a packet whose
history used that transport consequently depends on Theta_F too; it would be
incorrect to claim otherwise. It does not occur in raw constructor observation,
the six context constructors, segment cut, literal suffix extraction, ambient
union/restoration as operations, event-time traversal, name-action scoping,
or Fail/Bad propagation. Those equations stay unchanged for every admissible
Theta_F. This locality permits review of P without choosing F's rows.

## 8. Conditional correspondence statement and falsifiers

A possible later proposition is conditional on:

1. actual source administrative derivations with the counted step expansion;
2. typed input/decoration and lineage generated from the same source derivation;
3. an F relation established at its source owner, rather than assumed by a checker;
4. an explicit source embedding seam with full outer frame payloads;
5. source-owned fresh allocation and scoped name action.

Under those premises, `pi` is structural copying of the raw head, full frames,
concrete history and explicit cut; typing annotations are projected separately.
Reconstruction follows by induction on the context list. Suffix View extraction
commutes with concatenation by its three defining cases. These are bounded
representation facts; they do not establish the five premises, raw S/C, Call
A/B, soundness/principality, native correspondence or the full parent theorem.
A counted target refinement needs a trace simulation, not an assertion that
stack focusing instructions were printed as paper steps.

Symbolic discriminators, **not run or source-admission-certified fixtures**:

| Case / mutation | Exact failure it detects |
|---|---|
| `Force(r)` with `H(r)=View_chi((Lambda a.Delay M)[A])`; replace trace by lookup | Lost separate reference/View/type administration or wrapper metadata; latent M must stay inert until dispatch |
| `Force(View_chi(unit))`; erase wrapper then treat as typed thunk | Malformed Force must remain Bad without a typed-input premise |
| `Force(Delay(Fail BoundsError))` versus `Force(Delay(Bad r))` | Failure conversion or missing child Bad; no result transport in either branch |
| Two nested executing Views with the same incidence witness | Set subtraction on inner leave loses outer ambient witness |
| Inner View / selected handler / outer complete Call View | Outer View observed at emission but excluded from selected K; stopping scan at handler or capturing all Views fails |
| Same suffix View ID with two distinct packet/path payloads | ID-only suffix equality cannot reconstruct source data |
| Resume same K under ambients A and B | Restoring capture-time outer ambient incorrectly makes both re-entries equal |
| Same old owner u appears saved-bound and ambient-free | Global rename corrupts ambient; saved side must become fresh u', ambient remain u |
| Body returns a thunk later forced | Result/latent provenance requires F; effect-port-only transport cannot close the input bridge |
| Suspension during wait, free owner expires, guard later returns No | Must preserve original event and re-search in current activity; creation-time eligibility is invalid |

These examples discriminate equations directly; they are not new alternative
Force meanings or a counterexample to an accepted theorem. No independent
runtime oracle was used. Source authority and candidate encodings share the
paper; a checker written from the encodings alone would share all their missing
premises. Seeds/ranges: none, no enumeration. Mutations are hypothetical table
entries above, not applied code changes.

## Checks, remaining owner and STOP

Commands used: `cat`, `rg`, `nl`/`sed` source reads, `sha256sum` for all frozen
pins, one read-only `git rev-parse HEAD`, and the clock tool. No Git mutation,
Lean/Lake, build/test, Cargo/native command, checker, network request, scratch
file or compiler edit ran. One new file: this exact lease. CPU cap 1, memory
cap 1024 MiB, wall grant 600 seconds; actual CPU/peak memory and start timestamp
UNKNOWN. Charge the full 600-second grant. Clock sampled during work; no
claim of independently measured execution time is made.

Unverified: a fully expanded source administrative relation, its chosen Lean
trace encoding/adequacy, exhaustive raw malformed normalization behavior,
complete packet/slot generation in an implementation, the F-result rows,
and any compiled proof. Searches were limited to pinned inputs and exact rule
locators, not the whole compiler/native implementation. This packet does not
supersede r1/r2 accepted characterization or promote the r3 design.

Recommended next action: Luna should submit the frozen F/P pair to the assigned
fresh spec auditor, asking it to separate O-RESULT from O-NORM. The source
decoration/representation owner must discharge O-NORM with explicit counted
normalization constructors and a correspondence argument; the Control context
owner must carry full frame/suffix payloads. No further equivalent lookup probe
would discharge either premise.

Worker state: **STOPPED; writes ceased after revision 1**. No descendants or
unresolved child leases. This exact file is frozen for primary-assigned review.
Its SHA-256 is supplied in the final handoff, outside its own bytes.

## Commit packet

* Exact leased paths: `tasks/agent-loop/inbox/20261025-force-source-input-equations.md` only.
* Baseline: `9b945b0bb175e8e0919d388dc720babbdf0c2464`.
* Changed dependency hashes: none observed; all r4 pins matched.
* Review: NOT RUN; candidate source equations with explicit O-NORM/O-RESULT.
* Checks already run: source constructor/locator audit, all dependency SHA-256
  comparisons, read-only HEAD comparison; no executable tests.
* Proposed message: `research: record source-indexed Force projection equations and open premises`
* Shared deltas intentionally left to Luna/curator: reconcile stale current
  baseline; record P STOP/hash and review; track O-NORM with the normalization/
  representation owner and O-RESULT with F; retain all parent gates OPEN.
