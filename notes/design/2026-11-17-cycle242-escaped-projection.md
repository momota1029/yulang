# Escaped ordinary consumers: cycle242

I47 design A remains a partial representation redesign. I45 external point
protection remains unchanged. Read standing orders, I47 and cycle241 design.

The old OwnerBack producer requires every consumer support outside private cells.
That excludes actual escaped ordinary references. We instead compile every finite
ordinary consumer atom by simultaneous substitution of the OLD definitions,
retaining the resulting source constraint before installing the NEW block.

Data: coherent finite (target, type-term) definitions, arbitrary finite atoms.
Independent restriction: every RHS source lies outside all definition targets.
This restriction rules out both self and mutual dependency for this first layer;
coherence alone does not rule them out. Consumers have NO nonescape restriction.

Meaning: old equations plus original atoms, existentially projected over target
types, equal inlined atoms. Assignment equality is retained outside targets and
row values at every name. Construction is the actual finite patch, not an assumed
back-extension. Converse follows from the equations and external RHS supports.

For a replacement, any assignment satisfying new block and inlined old consumers
has a constructed old assignment satisfying old block and original consumers.
The new block is not conjoined with old definitions. No claim is made about
whole journals, nominal descriptors, cyclic solving, or global termination.
All-live labels need protected actual centers; ordinary atom retention does not
by itself cover every packet, descriptor, and evidence consumer.

## Raw nominal consumer review

Read GeneralNominalState.Fits/FitsAll/Denotes/Models and
GeneralNominalCommonBridge.assignment/Models, plus actual240
LooseFamilyBase.source/anchor/pair and LooseFamilyRevision.preserves.

The new finite Store theorem covers ordinary atoms only. Raw Models also reads:
1. base.source at every structural head and interval;
2. base.rowSource at row parameters and head row subterms;
3. a nominal descriptor's actual source and every argument endpoint through
   Fin slots; these uses are not State.ordinary atoms.
Mapping only State.ordinary therefore does not retain all raw consumers.

Actual240: source n (anchor n)=lower n, and the root Pair descriptor has two
intervals (anchor n,original 4). A lower aggregate becomes an observed source
slot with Foo descriptor. Reusing one stable lower cell L and inspecting that
root again makes the next lower term union(var L,var L). The direct new entry
is self-dependent and fails External; Fresh plus Endpoints cannot both hold
for a pool containing that endpoint and excluding L. Merely marking L owned
or allocated does not solve this. This is a failure of this producer's domain,
not a new refutation of the complete design A.

One old-definition substitution can turn that new RHS into
union(oldRHS,oldRHS), external when oldRHS is external. It does not remove the
promoted descriptor's constraint: that descriptor still relates L to Foo and
the root descriptor still constrains actual arguments through L. Those old
consumers must be compiled under the OLD substitution as well. Stable syntax
may grow even here; semantic equivalence to oldRHS needs an idempotent/no-op
check before this counts as a progress-producing service.

Required semantic intermediate (not yet an executable State):
  RawInline E raw m := raw.Models (patch E m).
Under Coherent E and External E the desired exact statement is:
  (exists old, Preserves E old m and Definitions E old and raw.Models old)
    iff RawInline E raw m.
A genuine producer would first prove raw.Models invariant under the existing
assignment Same relation (types Equivalent; rows literal), by structural
head congruence, interval transitivity, FitsAll preservation with the SAME
argument witnesses, and nominal target equivalence. Then extension_same and
the constructive old patch discharge the existential. This is not assuming a
raw-model backextension, but it is a semantic pullback, not an operational raw
snapshot constructor.

To obtain an operational snapshot one still needs either expression-valued
endpoint/source observations with their own inspection/normalization proof,
or a checked map from each substituted endpoint expression to an existing
finite source slot. Current base.source/rowSource fields take Nat identities,
not type/row expressions. A private-to-public alias chosen without an equality
proof can lose the descriptor constraint. Fresh frozen aliases per service
would revive the unbounded-name problem. An in-place source reclassification
also needs raw heads, root/child actual centers, cache/readback and I45 point
protection transported; existing Store projection proves none of those.

Preserving raw nominal truth is distinct from preserving live labels. If a
live actual center itself is a target, the projected old model may change its
type. Need either protected live centers, or an expression/readback label with
a proved semantic value transport. Ordinary inlining does not automatically
supply this. No meaning change or further point-revision rule is proposed.

## Newly activated cells: singleton to repeated capture

GeneralNominalAllocation.declarationKeys reserves both purpose0/1 cells for
EVERY input name even when capture is singleton and merges emits no definition.
Fresh allows a key already in allocated to appear anywhere in state.sources.
Thus allocation membership is not a producer of absence from old raw/ordinary
consumers. The existing source_fresh theorem proves absence only while the key
is not allocated. Initial source IDs are below seed, but revisits need a stronger
preserved invariant, not just that initial bound.

Changing the projection domain from old targets to old/new union does NOT by
itself make a singleton-to-repeated replacement sound. Minimal mathematical
obstruction: old definitions empty; unused future cell c is read by a retained
consumer c = public a. Projecting over c makes the old constraint true for any
a. New definition c = public b with unchanged consumer implies a = b. Both RHS
supports are outside the union and all targets fit the reserved universe, yet
source projections differ. It is not sound to remove the consumer, and inlining
old definitions cannot eliminate c because there is no old defining expression.
This is a local obstruction to unrestricted union-domain replacement, not a
refutation of the chosen whole redesign.

A sufficient structural route is: both definition blocks have RHS outside the
fixed owner target universe; additionally every old consumer is type-insensitive
to newly active cells (new targets absent from old targets). For finite atoms,
a conservative producer is absence of these names in their type dependencies;
rows may still read them because the patch preserves every row. Raw Models
need the same condition on base.source, descriptor endpoint/target reads, and
head terms, not just state.ordinary. With that condition, old canonicalization
need not determine the extra unused type variables, but consumers do not see
them, and new patch preserves the old projected constraint. The independent
new-cell insensitivity condition is what replaces TargetsWithin, not union
bookkeeping alone.

For actual source-reachable use, prove an invariant that a reserved but never
materialized purpose0/1 cell cannot occur in any source head/descriptor,
ordinary consumer, child actual/support, or trusted snapshot. Existing Fresh
and declarationKeys do not establish it after allocation. A narrower first
producer can cover a never-allocated first install via source_fresh; a true
singleton-to-multi revisit requires proving the no-read invariant through all
operations. If old consumers do read an undefined cell, retaining a separate
existential historical value would require a different representation and a
finite bound; simply using the newly defined current cell is incorrect.

RawProjection242 now closes the semantic-pullback theorem above using the
existing RawCongruence238.models_iff, including a combined raw-plus-ordinary
replacement theorem. Operational snapshot reconstruction remains open.

## Required executable-snapshot interfaces

The next executable work must select a representation before claiming a new
boundary. One precise option is an interpreted snapshot with the original
finite slot/descriptor structure and a finite expression environment:

- typeRead : Fin slots -> TyTerm Nat;
- rowRead : Fin slots -> RowTerm Nat;
- nominal argument bounds still use original Fin slot pairs;
- the assignment at a slot evaluates typeRead and rowRead separately;
- nominal target values evaluate typeRead at the target slot;
- each original base ordinary atom and head term is evaluated under this slot
  assignment; ordinary Nat-atoms outside the base use the global substitution.

A compiler from old entries and raw snapshot must prove, for EVERY physical
assignment m, InterpretedModels compiled m iff raw.Models (patch entries m).
This includes base heads/intervals and the same nominal argument witnesses,
not just ordinary atoms. TypeRead for a source slot is the old substitution's
type component at raw.base.source slot; rowRead at raw.base.rowSource slot is
unchanged. Thus the semantic compiler is plausible without minting new IDs.
It is not an existing GeneralNominalState.State, whose source fields are Nat.

To connect execution, additionally require an inspection/compilation simulation:
report captures, scalar/nominal observations, actual-center expressions, and
emitted constraints must denote the interpreted reads. The observation graph
must retain stable occurrence/slot identity without treating equivalent type
expressions as different public source identities. Every refreshed head needs
a readback theorem in the interpreted assignment; old cache certificates over
the raw unmodified assignment cannot simply be reused.

Boundary acceptance types to implement next:
1. CompilerSound: forall m, compiled.Models m iff oldRaw.Models (patch E m).
2. SourceAndLiveReadback: all designated public and live actual values in the
   compiled interpretation equal/equivalent their retained values, with literal
   row equality. This must be produced or explicit in the local fragment.
3. StepSimulation: each necessary source/inspection/materialization operation
   has a compiled transition with exact old/new model transport, point-source
   protection, and finite observation/owner support preserved.

A representation that stays with existing raw Nat source fields instead needs
an explicit map assigning EVERY substituted source expression to a finite
existing source identity, together with value-equivalence and head/readback
proofs. No such producer is currently supplied; arbitrary fresh aliases are
not a substitute because they can invalidate the termination argument.

The local new-cell O/W obstruction is now formally checked in
GeneralDictionaryRebaseNewCellObstruction242. Old definitions empty and the
retained equality c=O have a projected model; adding definition c=W while
retaining that equality has none. Both values are from the actual230 fixture.
Removing the retained consumer makes a model exist and is therefore a real
constraint deletion. The unrestricted union shortcut is not pursued.

## Externalizing the new merge RHS

MergeExternal242 supplies an additional concrete producer. New entry RHS terms
are the actual lower/upper terms of arbitrary new endpoint bindings, with
variables/unions/intersections/constants and no row positions. Substitute old
coherent external definitions into each RHS, keeping the target unchanged.
All resulting RHS supports are outside old targets. With new targets contained
in old targets, the rewritten entries are coherent and External, so the exact
replacement projection theorem applies. No nonescape premise is imposed on
new binding endpoints themselves.

The evaluation contract is important: rewritten new equations say current
physical target value is Equivalent to the original NEW RHS evaluated in the
OLD patch of the current assignment. This is not the original new equation
evaluated entirely in the old patched assignment. General new type terms with
row positions are not covered by the support-elimination producer, since row
variables intentionally remain unchanged. Coherent old definitions may be
arbitrary terms provided their full RHS supports already satisfy External.

This eliminates the direct union(L,L) RHS self-reference after substitution
when an external old definition of L exists. It does not produce a finite
semantic observation universe, normalize repeated union syntax, or prove a
whole operational step/progress theorem. Newly activated undefined cells still
need the separate no-read condition described above.
