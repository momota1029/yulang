/-!
R5 CORE: source-footprint argument and an UNREALIZED candidate trace.
Author: /root/native_fresh_use_context_coverage_core_r5.
No declarations, imported assumptions, theorem claims, or checker execution.
This file records the bounded complementary source result, not a Lean proof.

Parent: SourceProblem.InferenceSoundness, Contracts.lean:128:
  forall s x d a, supported s -> generates s x d -> solves d a ->
    exists e, sourceJudgment s x e /\ sameScoped s x e a.
No source quantifier or shared witness is changed.

SOURCE FOOTPRINT
candidate_context.rs:2630 context() returns an exact existing expression or
appends a new one. relation_with_scoped():3062 returns the exact existing
(pair, context, sources, scoped) key or appends it. Neither successful branch
rewrites the existing key or ContextExpr. Canonical endpoint changes before
interning can cause relation reuse; they do not prove new allocation.

candidate_context_execute_relation():3800 writes discharge membership and an
optional residual, after candidate_zero_word_filters():3669 selects the residual.
post_check_context():3297 consults these mutable fields. relation_context():1691
exposes that result. In contrast retained_input():1167 selects key.context and
its constructor children, and closes dependencies in both directions. Discharge
alone therefore does not erase the constructor of an already selected relation.
This is a local source footprint, not a proof of all successful driver paths.

If a parent was already discharged before preparation, execute_relation's guard
at 3841 returns before a second discharge write. If it has no consumable filters,
the filters.is_empty() branch also avoids discharge. The unresolved category is
an originally undischarged captured parent with filters executed during an
earlier bound restoration. A global stability premise would hide this category.

rename_contexts_impl():1566 validates/constructs the image of each encountered
source constructor, including both Replay children. It can reuse interned output.
The FreshUse caller starts with an empty map (candidate_scheme.rs:4425).
FreshUse preparation reads all effective roots before restoration (4419), whereas
begin_candidate_fresh_bound():4670 reads each effective root again at 4702.
It attaches the image of this SECOND root via fresh_transport_scoped():4278.
Hence immutable DAG storage does not by itself attach every prepared image.

CANDIDATE TRACE (finite structural configuration, NOT source-reachable evidence)
Use stored ContextIds:
  0 = identity (no stored row), 1 = PrefixLeft(w,0), 2 = Replay(1,0),
  3 = PrefixLeft(w',0), 4 = Replay(3,0), where w' differs from w.
Capture bounds in order B0,B1, with B1 parent p, p.key.context=2 and p not
discharged. Preparation produces map[0]=0,map[1]=3,map[2]=4.
Earlier B0 restoration replays original bound-fiber relations a,b having
contexts 1,0. If canonical pair, source union and scoped composition exactly
match p.key, relation_with_scoped returns p. incoming_use=true bypasses the
ordinary already-recorded dependency skip (candidate_context.rs:4055).
Replay delivery queues that relation (4105); execute_relation can discharge p
with residual 0 because the Replay-only zero-word filter branch chooses identity
(3750). All filter payload/view checks and successful effect checks are required.
Later B1 now reads relation_context(p)=0 and attaches map[0]=0. If the selected
relation dependency component consists of these original fibers and transported
identity-context rows, retained_input selects contexts 2 and 1, but never 4 or 3.
It also misses w' unless an independently selected endpoint/view selects w'.
No row 0 may be invented to represent identity.

EXACT UNPROVED REACHABILITY CONDITIONS
1. A completed authentic module/local capture contains the specified still
   undischarged Replay parent p, and admits B0 before B1.
2. B0 restoration encounters the original a,b fiber pair and produces p's exact
   pair/sources/scoped key; no fresh scope, endpoint or context distinguishes it.
3. The copied weight w' differs; no selected copied endpoint/view or another
   attached mapped constructor already makes 3,4,w' observable.
4. Every native operation succeeds and the consumer is completed, not paused.
These are not supplied by the candidate. A source witness or a universal capture
invariant excluding condition 1 is the next discriminating evidence. In particular,
no actual Yulang program or shortest successful trace is claimed here.

Application: retain the original parent OPEN. The footprint eliminates erasure
of an already attached mapped constructor as this packet's proposed failure
mechanism, and isolates a temporal root-read/attachment obligation. It does not
supply the all-image observation theorem, source inference, effect hygiene,
principality, termination, F1/FK1, or production authority.
-/
