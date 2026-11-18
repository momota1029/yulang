# Cycle251: split capture, binder and output roles

Status: Draft compiler component.

The two-map MixedPacket compiler has an independently defined old/current
judgment, but constructing its current map requires alias consistency. A capture
singleton endpoint can be a historical aggregate while another role needs the
new aggregate. Do not silently assume one global Nat map distinguishes them.
Use explicit expression fields for capture bounds, binders and output targets.

RoleEnvironment keeps old origin mapping, per-variable Bounds, per-variable
binder terms and target mapping separately. Head uses/tests and total explicit
or positional-default equations compile exactly to independently defined Values
judgments. OutputNames override every mode; nominal expression arguments use
actual mode; default variables are input-center positions.

For actual stable bounds, replace only handle.names and keep an explicit fallback
for other names. Related proves equivalence to old occurrence folds on those
names, with no claim for uncovered names. A checked packet's Needed names are
indeed inputNames, via its existing declaration scope check; this supplies binder
list coverage when handle.names equals inputNames. Head-schema and equation free
variable coverage, actual binder/target allocation and child-bound production
remain separate obligations until proved. No source semantics is changed.
