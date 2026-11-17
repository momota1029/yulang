# Cycle232: remaining bridges after guarded source-boundary repair
Status: Draft engineering proof plan, not a language decision.

## Established interfaces

The successor keeps historical legacy constraints intact and records each new
versioned plan/effect explicitly. Install models are characterized exactly,
including every old/new live class obligation. The source-facing boundary
uses the established HeadAlloc registry encoding; its diagnostic fields retain
V8 priority, full head sharing, output and merged-class conflicts.

The concrete230 regression has an OLD source-initial reachable prefix followed
by a fully guarded NEW step. Its installed state has a nonempty model set and
all models have a current-frame dictionary. The literal B4SkeletonV8.EvidenceAt
of the NEW guarded/source boundary is proved there, and V8 selects the node.
A separate migration-fragment path starts at the original source initial state.
That path is NOT a path using only the new boundary Step relation.

## Exact law status, without a composite wrapper assumption

Proved concrete laws: stepModels, closure, frontierLocal, localIdentity,
dictionaryRefl, initialReorders. Local totality/functionality also proved but
are not counted twice as extra members of the twelve-law list.

Remaining: progress (Acc), execution, halted, whereAccessible, treeExecution,
canonicalLocalOrder. No saturation executor is supplied just to assume these.
The two additional selected-node laws, GeneratedChildren and general
EvidenceNode, also remain open. Current-frame EvidenceAt at the concrete state
does not imply either general law.

## Immediate next obligations

1. Construct an initial-to-installed trace using the new guarded boundary alone.
   The current fully proved first transition starts from lift(old230after).
   Recreate the initial versioned installation and trusted reobservation. Do
   not insert a definition that declares arbitrary old reachable states Initial.
   Replay the actual230 source construction rather than renaming migration
   reachability. Prove final full-kernel Stable separately; install-only closure
   currently does not exclude future refresh/equate/reobserve actions.
2. Extend the trusted observation interface to facts from recorded VERSIONED
   effects. Retaining the legacy slice system is a sound sufficient certificate
   interface; preserving its cache does not prove it can justify every new
   generated head required for progress. New effect facts must retain settled
   support/readback conditions; full-journal entailment alone is not a substitute.
3. Close the reachable finite-version pool and progress/accessibility before
   an executor/composite theorem. Cycle231's explicit finite alphabets and
   binding-length bounds remain hypotheses whose closure along real steps is
   unproved. Then port source-registry reorder/canonical closure and rerun
   199/202/204/206/218 on the new boundary.

## Review outcomes

No new exact counterexample was constructed. An effect initially stored only
HeadModels plus class effects; full Holds is separately required of each
recorded new plan. Recorded232 proves that every effect in every ACTUALLY
reachable state has its plan in that list, so the reachable interpretation is
not accidentally head-only. It does not claim this invariant for arbitrary
hand-built states. The initial registry-encoding omission in the kernel-level
packaging was corrected with SourceBoundary232; the generic source adapter and
its local/evidence/initial transport are now explicit.

No modification to V8 classification or refusal semantics was adopted.

## Concrete next trace and settlement boundary

Prefer a five-slot source-initial trace with first versioned install, source-only
trusted point reobserve, then second versioned install. Optional upper refresh
is not needed for the dictionary evidence itself. This is a candidate proof
route, not a proved new-boundary Reachable or full Stable result. Reuse
OptionalInstall229 packet/report/bindings, JournalRefinement228Reobserve source
certificate, OptionalCurrent229 point context, and AggregateVersion231 freshness.
New-list support bounds and all guard/acyclicity obligations still need proofs.

Legacy PacketSettled and Discharged recurse through old Packet.children; actual
new install sites/edges use versioned children. Cache232/KernelCache232 preserve
existing Trusted derivations and do not identify those two child lists. Future
nonterminal settlement and new trusted facts require versioned settled/readback
or a proof relating the old and new children. No new counterexample is claimed.
