# Cycle54: scalar-preserving source endpoints

Status: Draft implementation boundary. Date: 2026-11-09.

## Bounded objective
Close the materialization boundary exposed in cycle53: source slots must retain
all four existing ordinary scalar heads, especially str, without encoding str as
int or a nominal name. The old int-only syntax and its proofs remain unchanged.
The new observation carrier is unknown, a scalar Base, or a unary constructor
around another observation. Endpoints retain fixed observations and source slots.
This is an additive observation adapter, not a replacement role matcher.

## Data, independent meaning, execution, theorem types
The executable slot reader is the existing ordinary detect, which scans paired
upper/lower atoms. The carrier preserves its Base value directly. Finite variants
for every slot are unknown/int/bool/str/unit; wrappers preserve those variants.
Independent endpoint meaning relates a source endpoint to an observation using an
ordinary assignment: a known scalar must be equivalent to the assignment's type;
unknown makes no positive assertion. It never calls detect or materialize.

For all states s, assignments a satisfying s, and source endpoints e, evaluation
satisfies that independent meaning. For each slot i and scalar b, under an actual
model of s, evaluation is scalar b iff the explicit paired Evidence s i b exists.
This restriction concerns syntactic evidence, not full arbitrary entailment.
For all atom lists with identical membership and a model, endpoint observations
are equal. Adding atoms preserves every known scalar when the later state has a
model. These model premises are explicit and are not silently inferred.

For every finite string/equality input table T, initial problem P and finite
updates U, the evaluated receiver at slot i is str iff all independent original
source models force i to str. It is unknown iff two original source models
assign inequivalent receiver types. Here the existing construction supplies the
required consistency, so no caller-supplied model premise is needed.
Connect this readout to the actual checked Index producer and cycle53 diagnostics.

## Scope and remaining bridges
Fixed finite source carrier, positive string seeds, equalities and externally
supplied finite updates remain fragment restrictions, not language rejection
rules. bool/unit are preserved observations but the existing Roles.Term producer
still only accepts its supported int/str encodings. No new role semantics is chosen.
The old recursive diagnostic carrier, general declarations, dynamically generated
source slots, dictionaries and four-way language classification remain unconnected.
General B4 still has five open bridges. This work closes a named sub-boundary of
source_boundary_adequate rather than reducing that count.

## Yulang2 and authority
Read work/dots-audit notes/audit/x-oracle.md X13–X17 and C3-PARENT, plus spec 6.3.
The oracle provides finite examples, not a generic materialization proof.
The new adapter preserves existing ordinary scalar identity and does not add a
language decision or run a new Yulang2 instance.

## Existing graph inspector connection
Build a finite graph on the original occurrence slots, reading each ordinary
scalar to a distinct scalar graph node (int=0, str=1, bool=2, unit=3). These are
internal injective codes, with int/str agreeing with existing first-order codes.
Unknown nodes are not identified just because their observations are equal.
Prove that the existing scalar head inspector matches exactly the paired
ordinary evidence under a model. For the positive-string source construction,
matching the str head is equivalent to original source forcing, and its unknown
snapshot is equivalent to two distinguishable source models. This connects the
new readout to an existing inspector, rather than merely adding a parallel tree.
No alias-canonicalization, recursive graph construction, or general candidate
applicability is asserted by this flat scalar graph bridge.
