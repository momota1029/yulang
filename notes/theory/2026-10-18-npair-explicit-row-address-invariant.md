# Explicit Operation root row: address and cache audit

Status: frozen research-only conditional derivation; independent review NOT_RUN.
Parent: CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017, original theorem,
quantifiers, accepted meanings and source domain unchanged. Parent closure
starts 0 and remains 0. No semantic incidence or `At` conclusion is asserted.
Sprint: npair-operation-self-effect-decision-20261018, contract revision 1.
Baseline: d4db1bda69e53628d362d33ced23f4e0f37563a3.
Author: /root/npair_explicit_row_address_invariant, complementary source auditor.

## Objective and exact claim class

Determine whether the explicit root result-effect cache can reuse a view that
lacks the root self-family or has another provenance/tail/field address. Method:
static constructor and traversal audit of the four leased source inputs and
§3 of the frozen prior proof. This is source evidence and a conditional theorem,
not a checked execution, established semantic theorem or independent review.

**Conditional result.** For a successful `candidate_operation` construction of
an authentic parsed signature, if distinct BracketRow syntax nodes in that
signature have distinct `SourceNodeKey`s, the explicit root result-effect call
is a cache miss. It therefore creates the view with self-family at member 0,
then the written members, the signature's mapped symbolic tail, actual
owner/Operation declaration/occurrence and the root result row's position.
Cache hits at that root field are unreachable under these hypotheses. The
leased files do not establish the stated key-injectivity premise.

This does not assert that arbitrary cache hits preserve these facts. A hit
returns the saved ID without comparing family, owner, provenance, tail or
field. No authentic source collision is demonstrated or alleged.

## Derivation and exact premises

Premises are successful construction; immutable authentic parser-produced
signature; the ordinary owned tree recursion shown below; and injectivity of
keys on distinct parsed BracketRow nodes. Key injectivity is the sole newly
isolated external source-identity premise, not an accepted theorem here.

1. `candidate_source.rs:1008–1025,1466` carries the actual resolved declaration,
   owner, occurrence, target and level into `candidate_operation`. Its slots
   1/2 address the Operation expression's separate computation effect.
2. `candidate_effect.rs:844–863` allocates fresh value/effect/view maps for each
   Operation reference and constructs that declaration's signature once. Thus
   no view from another reference, annotation, catch operation or earlier
   operation construction can enter this local cache. The context remains
   unchanged through all recursive calls.
3. `source_annotation.rs:257–294` parses and retains the signature and its
   source position. `parse_type_source` and `parse_group` (407–526) produce an
   owned `SourceAnnotationType` tree. Moving `effects` with `effects.or(...)`
   retains a row in one slot; it does not clone that row into two slots. An
   arrow moves leading effects to its argument and gives its own Function
   node no effects. Each parsed explicit row belongs to one tree-node effects
   slot. `parse_row` (530–586) obtains its position from `source_nodes[node]`.
4. `candidate_signature_value` (1610–1702) recurses through argument and result
   values, then consumes each child's effects slot exactly once at its parent
   Function. It does not consume the current Function node's own effects slot.
   Therefore recursion into a Function-valued root result does not consume the
   outer root's result-effects slot early. Its row can only be consumed at the
   outer root result-effect call. Nested callbacks can populate other keys
   before that call, including rows at positive composed variance.
5. Operation omitted rows without a self-family return leaves (1725–1726)
   and insert no cache entry. The root omitted-row/self-family path creates a
   fresh view directly (1717–1723), also without a cache insertion. Thus the
   annotation-only cache key `context.position()` cannot contaminate this
   Operation construction. Its cache entries come from explicit rows.
6. The root family is supplied only when `ty` is pointer-equal to the actual
   declaration signature (1682–1686). It is never supplied by nested Function
   calls. By steps 3–5 and key injectivity, no earlier explicit row has the root
   result row's key. Hence lookup at 1796 misses. The miss prepends the family
   (1804), appends concrete members in order, and retains the already computed
   tail (1775–1789,1806–1812). Duplicate written families keep separate vector
   positions. `candidate_signature_view` (791–831) saves owner, row position,
   allowed vector, tail and `ViewOrigin::Operation` containing the same
   declaration and occurrence. The root positive port receives Support(view)
   (1823–1837); this is a physical construction fact, not semantic incidence.

On authentic repeated traversal of the same row with unchanged Operation
context and no root-family-role change, a hit reuses that same view and its
stable name-mapped tail. This observation is not needed for the one-pass root
result. The repeated payload/response traversals in `candidate_catch_operation`
(864–887) use a separate local cache and never pass the declaration signature
root to `candidate_signature_value`; they cannot seed this Operation root cache.
No all-callers cache theorem is claimed.

## Smallest mismatch condition and conditional witness

The necessary failure condition for a stale root hit in this construction is:
an earlier explicit row that populated the same local cache has
`earlier.position == root_result_row.position`, while its expected view tuple
differs. Such a hit bypasses the family prepend and all validation of that
tuple. This is an exact code-level condition, not evidence that parser output
can meet it.

A minimal owned-carrier witness needs two Function nodes and two explicit rows.
Consider the shape suggested by `([]int -> int) -> []int` in a family F's
Operation signature, but **mutate only the retained row keys to the same key
k**. This is a hypothetical malformed carrier, not an executed program or a
source-qualified counterexample. One Function alone cannot populate a prior
view: its argument row has negative composed variance and returns before the
view cache.

With two Functions, the inner Function lies in the outer argument, so its own
argument row has positive composed variance (two reversals). That empty row
populates key k first, with allowed=[], tail=None and the actual Operation
provenance. At the outer root result-effect call, family=F, positive variance
and key k produce a hit. The view remains allowed=[] instead of [F]. Owner and
Operation provenance still match, but self-member 0 is absent and the key no
longer authenticates which physical source row was meant. Adding a named tail
to only the later row also permits tail mismatch; the two empty rows already
suffice to discriminate the unconditional self-member claim. No mutation was
applied to repository source or any actual carrier.

## Evidence owner and remaining boundary

`source_identity.rs:26–51` traverses syntax nodes and copies `node.key()` into
maps keyed by SyntaxNode. It does not check uniqueness of the resulting key
values. `source_annotation.rs` faithfully copies those values. Neither file
defines `SourceNodeKey` equality or `node.key()` generation. The next missing
evidence belongs to the syntax source-identity owner that defines those two
operations, plus its connection to `counters.source_nodes`. That owner lies
outside this packet's four-file read lease. No lease expansion was attempted.

One recommended next action: primary leases a bounded read of that identity
owner and the source_nodes construction/assignment to discharge or refute
injectivity for distinct BracketRows, then applies the result to this frozen
conditional derivation. Do not run another transition-model probe of the
already visible cache code. Even an established address invariant would leave
the original Operation semantic self-leaf bridge and parent gates open.

## Frozen dependencies, checks and omissions

SHA-256:

- contract rev1: 7751165b11b2c286ee1d2021a1bd5b6784d743ace78c4124cb6e80ee6b822aa3
- candidate_source.rs: 4ea9d89e4a31e7be4ce170517e50eea31dd9e054c360cedba9ccc9cb7ced69ce
- candidate_effect.rs: 9ea9498692bdff12c2a7ebd8546ca2b443a095c0700f3e87ad6c956cc690e212
- source_annotation.rs: b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f
- source_identity.rs: 7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3
- prior reference-indexed-self-leaf proof: db9b4ab7894865bb8b67b502564fa193c9569ef205f9209e9cd6af894bc16187

Checks: `cat`, targeted `rg -n`, `sed -n` reads and `sha256sum` only. A broad
initial search output truncated; all reasoning above uses subsequent targeted
reads. No tests, builds, probes, compiler execution, Cargo, Git, network,
children, shared edits or reviewer appointments. No executable oracle exists;
this derivation shares the inspected compiler traversal and parser premises,
with key injectivity explicitly unverified. Seeds/ranges: not applicable.
Failures, allocation rejection, extrusion/freshening/replay, downstream
canonicalization and semantic Support interpretation are outside this result.

Requested runtime: Luna/high, Astra0, read-only analysis cap 180s plus the two
expressly leased research outputs. Effective model/effort: UNKNOWN from launch
metadata; no runtime setting change. Local commands used one short process at
a time. CPU/RAM and exact wall usage are unmeasured; primary should charge the
full 180s reservation rather than infer a refund. No descendants. Writes stop
at frozen submission; author will not edit during review.
