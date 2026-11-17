# Cycle237 installation progress: counterexample-first scope

The old DefaultDepth208 assumes InstalledDepthBound; it is not an available
unconditional depth proof. MixedProgressSplit236 proves administrative
termination but explicitly leaves InstallationDescent open. Numeric aggregate
DAG236 does not bound an ascending chain of fresh versions.

First real invariant: actual source traces retain all recorded plans as
Committed. Reconstructing any such plan under a current ordinary-only context
extension must remain Committed, even after arbitrary intervening mixed steps.
Use current full model raw validity for the added atoms, not an assumed new
packet model. The existing versioned transport keeps children and current
class semantics unchanged. This rules out context/ordinary/allocation-only
reinstallation and isolates actual observation/report change. It does not
claim global finiteness, complete progress, or a new target counterexample.

## Corrected producer dependency
DefaultAncestry208.ground_depth_bound DOES produce the old bound, via actual
head-schema weighted readback and Paterson mass. The new work ports schema
mass/readback from Versioned SchemaHolds and Versioned Frame, never assuming
legacy total Holds. Its actual binder is definitionally preserved. Child
semantic labels and a retrospective mixed-trace mass invariant are the next
real producer; finite versioned endpoint support remains distinct afterwards.

## Verified local retarget fixture; not a source-reachable counterexample

The separate GeneralDictionaryVersionLoop{Source,Packet,Frame,Full,
RefreshBase,Refresh,Retarget}237 modules check a terminal Pair(x,x) declaration
with source Pair(Foo(Int),Foo(Int)). The initial observation uses the same
source `a` twice. Its versioned plan creates aggregate lower/upper names with
value Foo(Int). The concrete installed state has a full model, constructed
from the actual packet full Holds and effect class semantics.

A mixed Refresh then exposes the lower aggregate as Foo(s,t), where distinct
source identifiers s,t both denote Int. A mixed Reobserve changes this to
Foo(s,s) while retargeting the already-point root from Pair(a,a) to
Pair(lower,lower). Both certificates and the actual two-step mixed-kernel
path from this installed fixture are checked. Both refreshed and retargeted
states retain a concrete full model. The improvement certificate requires a
new point at the lower aggregate but does not preserve the exact descriptor
of the already-point root.

Critical scope: Source237 proves InitialSource and its concrete source model,
but the complete SourceBoundary.Initial/GroundRoots and the first guarded
initial-to-install Step have NOT been constructed. Therefore local_steps is
not an original-source Reachable proof. The second installation, uniform
iteration certificates, an infinite trace, and a termination refutation are
NOT proved. No target counterexample is asserted. This is a precise possible
obstruction to claiming finite versions from finite source invocations alone.

Next work: close source GroundRoots and initial SafeKnown/acyclicity for the
nested Pair/Foo/Int model; obtain the first full guarded install Step; then
construct a second install with genuinely changed ordered capture endpoints.
Any global nontermination claim additionally requires a uniform family and
all guards at every iteration, not just this finite local prefix.

Next237 additionally computes the retargeted report and bindings exactly as
[(0,lower,lower),(0,lower,lower)], proves lower < nextLower, a different version
hash, and nextLower distinct from the old upper. These are actual current
packet computations, not a proof that the next installation is enabled.
