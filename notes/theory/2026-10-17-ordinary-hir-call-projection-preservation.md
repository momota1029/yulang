# Ordinary HIR Call projection: preservation lemmas and error-output lower bound

Status: frozen candidate mathematics/source correspondence; independent review pending.
Full adopted-resource claim: STOPPED at the explicit mismatch in §1.
This does not declare the structural preservation theorem impossible.
Author: `/root/astra_accepted_call_hir_projection`, sole author, current-session.
Assignment/handoff revision: `ordinary-hir-call-projection-preservation` / 1.
Requested: astra_prover, gpt-6-astra / medium; observed model/effort UNKNOWN.
Sprint contract SHA-256: `a9220bc8dab9019a3b8d362ea6ed447cdbc0e70373f2b10845e6b02b8d8cc496`.
Adopted rev4 SHA-256: `2e61e2acb1a8981bb78592accc48207a24a5cc4c75278e100f63eb960acfeea3`.
Baseline/checkpoint supplied by Luna: `b1f15a81a`; contract's source baseline
`5fbceb68d`. No Git inspection. Adoption receipt below overrides the frozen
proposal's historical “not adopted” header for the exact adopted bytes.

## 1. Decisive result: aggregate errors are an output-size parameter

Rev4 §4 requires each `Apply.errors` to be the ordered, duplicate-free list of
authentic error IDs **within that retained subtree**. Pinned
`crates/yu-hir/src/module.rs:481` stores this as an independently owned
`Box<[HirErrorId]>`. Rev4 §2 says pending and retained entries are linear in
the accepted expression subtree. Those statements do not support a linear
bound counting all retained error-reference entries.

Let Gamma contain no bindings named f or x_i. Form the permitted associated
expression family

```text
E_0 = Name(f)
E_i = Apply_ml(E_(i-1), Name(x_i))       (1 <= i <= m)
```

The corresponding ordinary source shape is `my z = f x1 ... xm` with unique
unresolved identifiers, no recovery, tuples, dynamic operators or unsupported
children. This is a family inside the adopted inductive grammar, not a newly
selected input restriction. The authoritative ML association yields the same
left spine; the argument can alternatively be read directly over admitted
associated trees, without a new runtime/parser claim for every family member.
Each distinct Name occurrence generates exactly one UnresolvedName error e_i,
with e_0 for f. There are V=2m+1 expression nodes and D=m+1 actual error records.
The required subtree lists are

```text
errors(E_1) = [e_0,e_1]
errors(E_2) = [e_0,e_1,e_2]
...
errors(E_m) = [e_0,...,e_m].
```

Therefore the number R of retained Apply error-reference entries is exactly

```text
R = sum_(i=1)^m (i+1) = m(m+3)/2.
```

The lists have no duplicate ID *within* a list and no duplicate HirError record;
the same authentic descendant ID must occur in several ancestor lists. This is
allowed by §4 and is precisely the source of the lower bound. For m=3, seven
expression nodes and four error records require nine stored references.
As m grows, R is quadratic in V. Even counting spelling bytes of x_i gives
only O(m log m) input bytes. Independently owned flat slices require Omega(R)
stored ID entries and initialization work; a worklist cannot remove this
output lower bound. The finite u32 identity ceiling and allocation failure
policy do not change the exact count for successfully constructed instances.
No huge fixture, timing experiment, or memory exhaustion was run.

**Exact falsified claim:** all retained entries, including the specified flat
subtree error arrays, and their construction work are O(V), uniformly in the
admitted expression size. This counterexample does not falsify operand order,
source identity, lexical resolution, dense diagnostic ownership, carrier
noninterference or the original Call theorem. No admitted case is removed.

Luna acknowledged this mismatch and instructed freezing this lower bound and
independently valid lemmas. No contract or implementation is edited here.
An output-sensitive interpretation is a **proposed repair only**: retain linear
node/worklist control, charge all aggregate-reference output by R, and state
O(V+R) work/storage (plus copied spelling bytes and the existing module passes),
with worst case O(V²). An alternative representation/aggregation policy would
need its own adoption; this author selects neither repair. The following
lemmas identify exactly what survives if the output-sensitive repair is adopted.

## 2. Judgment and premises with independent owners

Fix one ParsedFile P, its authoritative association result A, its parse-owned
node/key map K, an already admitted binding root b, the ordinary lexical
parameter stack L and complete module namespace N. The source audit establishes
these inputs for the fixed literal. For general source, the governing association
and recovery owners supply them; implementation must validate their provenance.

Let an origin plan t be a finite tree of the following constructors, each tagged
with its **actual** source node p and key K(p):

```text
Atom_p(kind, spelling, token_range)
Group_p(t)
Apply_ml,p(t_c,t_a)
Apply_call,p(t_c,t_a).
```

The tags are retained by descent from P's actual nodes. They are not recovered
by searching equal text/ranges. A plan may be assembled in a private worklist,
but its shape is checked against A; this does not create another association
authority. In particular an implementation cannot use a guessed left fold to
admit a tree whose authoritative association differs.

Write `P,A,K |- C => t` for complete **shape preflight**. Its rules are:

- ATOM: the associated node is childless IdentifierExpression or IntegerLiteral;
  p is that exact CST node, with one appropriate token, a unique parse-owned
  source mapping, and the supplied token spelling/range.
- GROUP: the associated node retains ParenthesizedExpression p with exactly one
  child t; raw punctuation confirms no comma/tuple; the child preflights and p
  has its own unique key. It yields Group_p(t). Elision is permitted only if the
  existing association adapter actually elides the wrapper, in which case the
  ATOM rule applies to the retained atom. The proof never elides a retained
  Group merely to reuse an inner ID.
- APPLY-k, k in {ml,call}: authoritative A has exactly two associated children
  in callee/argument order at the actual MlArgument/CallTail p; each preflights;
  raw source confirms the one-operand, nonempty, noncomma envelope; p has its
  exact unique key. The two children retain their disjoint actual source nodes.
  Yield Apply_k,p(t_c,t_a).

All rules require the pre-existing causal/recovery gates to permit projection.
A Missing, Invalid, Error, unsupported child/operator, malformed delimiter,
comma/tuple, absent operand, ambiguous mapping or shape mismatch fails whole-
body preflight. No name resolution occurs during this pass. Identity exhaustion
and allocation failure are availability failures, not source refusal or success.
Preflight must check source keys at the owner, including ambiguity, before
replacement. “Shape resembles an Apply” is not an independent key witness.

This judgment is a finite verifier/construction specification. The existing
`associate_chain_owned`/`ChainParser::structural_continuation` establishes
associated order; `ParsedFile::source_root` and SourceNode::key establish
parse ownership; source_identity retains exact nodes; the new general ordinary
preflight is **not implemented in the pinned baseline**. The proof does not
claim tests of this judgment show a future constructor emits its premises.
Its implementation correspondence is TODO PROJ-IMPL-1 below.

After *complete* preflight define `L,N |- t => q ; D` by structural recursion.
q is a private resolved plan with symbolic error handles; D is its ordered
sequence of leaf error events. Use the existing atom rule:

```text
resolve(s) = Parameter(last matching L)              if present
           = Resolved(the unique DefId in N[s])     if |N[s]|=1
           = Ambiguous                             if |N[s]|>1
           = Unresolved                            if |N[s]|=0.
```

The owner is `module.rs::ScopeStack::parameter` and `lower_leaf`, not any typed
Function judgment. Integer gives Integer and an empty D. A resolved name gives
Name and empty D; an ambiguous/unresolved name gives the matching NameResolution
and one fresh error event with Lowering origin, matching kind, exact token range
and `Value(b.def_id)` attachment. Group forwards its child's D. Apply returns
callee plan then argument plan, D=D_c ++ D_a, and stores those symbolic handles
as its subtree list. Each error event is emitted once; copying a handle into
ancestor lists does not emit another error.

The formal rules apply to all admitted trees, including unresolved names; a
semantic/name error is not structural refusal. They change no source typing,
Call semantics or solver decisions.

## 3. Induction: association, lexical facts and exact keys

The measure is the finite number of retained constructor nodes. For ATOM,
q preserves kind/spelling/token range and resolves by the independently fixed
L,N rule. It adds no invented child, key or Call claim.

For GROUP, the induction hypothesis gives the child's shape/resolution/key
facts. Wrapping it in Group at p preserves that child, retains the parentheses'
key and range, and changes no lexical environment. The outer constructor is
Group even when its child is Apply; this is the repaired rev4 root case.

For APPLY-ml and APPLY-call, apply the induction hypotheses separately to the
authentic associated callee and argument. Put q_c in callee and q_a in argument;
retain the source_form k and the authoritative associated range. No permutation,
flattening or callee extraction is performed. The key of the Apply is K(p), the
continuation key, not the argument key or whole-chain range. This proves shape
and lexical preservation for each constructor and hence nested applications.
The same argument proves left-associated callee preservation; it supplies no
evaluation-order theorem.

For each actual key, equality requires the same parse brand, green allocation
and start (`full_parse.rs::SourceNodeKey::eq`). Preflight's unique mapping plus
the disjoint actual subtree positions makes the callee/argument keys distinct.
Same-range wrapper/child nodes retain different green kinds/structure. Separate
occurrences of equal identifiers have separate source positions. Recovery may
create ambiguous zero-width keys; this proof does not assume universal key
injectivity and those cases cannot pass the unique-source preflight.

Inductively each q node therefore maps to exactly its own input key and its
subtree references are complete and unmerged. This is uniqueness of the
canonical projection's source owner. It does **not** assert that one key has
only one HIR occurrence across the carrier and canonical projections: rev4
explicitly permits both to map to the same key with different IDs.

## 4. Root lineage, staged allocation and atomic publication

Let r be this body's existing ordinary occurrence. Preserve all existing
binding/parameter/lambda/root occurrences. Let M0 be the pre-finalization
source-identity map after the unchanged ordinary/carrier passes, and let k_next
be their next occurrence ordinal. Only proper descendants of q need new IDs.
Traverse those descendants deterministically in source preorder, allocating
successive checked ordinals from k_next under the same artifact brand. Across
bodies use the existing source root order. The root of q receives r.

For an Atom root, r maps to its atom key; for an Apply root, to its continuation
key; for a retained Group root, to its ParenthesizedExpression key. In
`Group(Apply(c,a))`, root= r, while inner Apply,c,a are three new descendants.
This is one rule over all four constructors, not a special case for one fixture.

Proof of lineage by induction: ATOM has only r. GROUP reserves the outer slot
and recurses on a fresh child; APPLY reserves the outer slot then recurses on
disjoint fresh callee/argument slots. Checked monotone allocation gives unique
new ordinals. All new IDs are >=k_next; all previously allocated carrier/ordinary
IDs are <k_next and keep their original artifact/ordinal. No carrier occurrence
ID is reused for a canonical child even when the source key agrees.

Before publication, check r in M0: absent => stage r->K(root); same key => retain
without duplication; different key => InconsistentIdentity with no overwrite.
Stage all new descendant mappings in a single occurrence-only empty_stage.
`source_identity.rs::append_stage` checks the same parse root, duplicate IDs,
empty forbidden definition/expression deltas, and reserves each target capacity
before extending any map. Thus a successful stage preserves all old entries and
adds exactly the new mappings. It is essential not to call overwriting
`record_occurrence` for this final publication. Reservation/ordinal/collision
failure returns the existing availability error and publishes no HirModule;
this is not a claim that private capacities or every internal value roll back.

The complete q and error-sink delta also remain private until the module can
be returned. Unsupported/recovery preflight failure commits neither q, new
child IDs, operand-name errors nor mappings; use the existing refusal and
causal-error attachment. Allocation failure aborts publication. Therefore the
successful-output invariant is preserved on every success and no partial new
projection is published on refusal/failure. This proof is independent of R;
it requires checked reservations for R as well as node entries, not a false
linear allocation estimate.

## 5. Carrier noninterference and dense diagnostic ownership

Carrier noninterference is a simulation of the unchanged carrier pass, not
solely a tree induction. Its inputs are the same plans, namespace, parameters,
source map, artifact and next ordinal; no pending new canonical child IDs or
root mappings have yet been installed. The source q remains private.
`local_source.rs::form_ordinary` uses those inputs, performs its own empty_stage,
orders its own occurrences and merges its own mappings. It does not inspect a
new canonical Apply to decide its grammar or error output. Therefore each
carrier step sees the same inputs as before; induction over roots yields the
same Supported/Unsupported outcomes, forms, IDs, key mappings and next ordinal.
The later canonical stage cannot overwrite them. This also covers unchanged
direct-expression carrier outcomes: binding admission does not activate
ordinary direct-root application admission.

A carrier failure remains its original failure. The theorem compares successful
carrier runs with sufficient resources; it does not assert equal memory budgets
or that adding output R cannot cause a later allocation failure. Early canonical
child allocation would falsify the simulation by shifting carrier ordinals.
Opt-in local-source/shadow passes are excluded from the changed ordinary route
and keep their established placeholder errors.

For diagnostics, first give every error event a private symbolic handle h.
Retain the old event schedule and payloads except the whole-body admission
UnsupportedExpression event for a successfully admitted tree. Insert new atom
error events at the ordinary semantic-error emission location, in leaf source
order. Keep all existing causal/duplicate ordering and other retained records;
`lower_plan` is the owner of this scheduling seam, including its distinction
between lower-body refusal and deferred atom semantic errors. The implementation
must not simply emit each new leaf error during an early speculative traversal.

Let the resulting ordered event log be L'=(h_0,...,h_(e-1)). Assign
`ErrorId(h_i)=i`. Restrict L' in order to events that have a HIR diagnostic and
assign DiagnosticId(j)=j within that subsequence. Make every diagnostic.error
reference the corresponding ErrorId, and every error.diagnostic the matching
DiagnosticId or None. Resolve all q subtree handle lists using this one map.
Existing syntax-origin markers still have no HIR diagnostic.

D(q) contains each erroneous leaf handle once by induction: ATOM gives zero/one,
GROUP forwards, APPLY concatenates disjoint child event lists. Consequently each
Apply.errors is ordered and duplicate-free, all its IDs name actual entries of
L', and repeated ancestor references never duplicate a HirError. The module
vectors are dense by construction. Retained record payloads, multiplicity and
relative order are preserved, while numeric suffix IDs can shift. Reusing old
numeric IDs after removing an earlier error would violate density; rev4
explicitly does not require that reuse. R counts the materialized Apply lists,
so the proof of correct references does not imply a linear count of references.

With sufficient reservations the same construction proves all these invariants
under an output-sensitive O(V+R) interpretation. Node validation, preorder
control, root mapping and worklist entries remain linear in V; each output
error reference can be written once per containing Apply. Actual error records
number at most the erroneous leaves for an admitted body, O(V). Across a module
add the unchanged existing traversal/storage and spelling-byte costs. The
Omega(R) lower bound remains; worst case is quadratic. These are candidate
mathematical bounds for the stated construction, not measurements or proof of
unwritten implementation code. No repair to the adopted cost clause is made.

## 6. Concrete derivations and useful, bounded proof interpretation

Use the fixed audited module containing all three declarations. Merely writing
`my answer = apply id` alone would leave apply/id unresolved; its derivation
below explicitly uses the complete module namespace including id and apply.
The fragment `my apply f = f 1` needs only its admitted formal f and integer.

The audited keys are K_f for the IdentifierExpression at 26..27, K_1 for
IntegerLiteral at 28..29, and K_t for MlArgument at 28..29. The keys K_1 and K_t
are distinct despite coincident ranges. Let L contain f with parameter identity
p_f=(definition_root(apply),0). Then:

```text
P,A,K |- f => Atom_f       P,A,K |- 1 => Atom_1
------------------------------------------------ APPLY-ml
P,A,K |- f 1 => Apply_ml,t(Atom_f,Atom_1)

resolve_L,N(f)=Parameter(p_f)          D(1)=[]
------------------------------------------------ RESOLVE-APPLY
q = Apply_ml(Name(Parameter(p_f)),Integer(1)); D(q)=[].
```

The enclosing existing Lambda keeps its own occurrence and parameter p_f. Its
body root r_apply belongs to the Apply, not to the formal use or the Lambda.
The two child occurrences are appended after the entire existing carrier pass,
map to K_f/K_1, and are distinct from the carrier's occurrences. No
UnsupportedExpression or atom error is created for this shape under adopted
admission. Current baseline code still emits the old refusal until implemented.

For answer, use K_apply at 43..48, K_id at 49..51 and the distinct outer tail
K_u at 49..51. The completed unique namespace gives DefId_apply and DefId_id.

```text
P,A,K |- apply => Atom_apply      P,A,K |- id => Atom_id
------------------------------------------------ APPLY-ml
P,A,K |- apply id => Apply_ml,u(Atom_apply,Atom_id)

resolve_N(apply)=Resolved(DefId_apply)
resolve_N(id)=Resolved(DefId_id)
------------------------------------------------ RESOLVE-APPLY
q = Apply_ml(Name(Resolved(DefId_apply)),Name(Resolved(DefId_id)));
D(q)=[].
```

Its existing body root r_answer owns K_u, and its two children are new appended
IDs. Both derivations establish source operand incidence, resolution and empty
structural error lists. They assert no type for f, apply, id or either result.

A useful derived rule is SOURCE-OPERAND-INCIDENCE:

```text
P,A,K |- C => Apply_k,p(t_c,t_a)
L,N |- t_c => q_c;D_c     L,N |- t_a => q_a;D_a
successful staged finalization with root r and child roots c,a
----------------------------------------------------------------
StructCall(P,b,r,k,K(p); c,K(root(t_c)); a,K(root(t_a)))
```

`StructCall` means exactly a retained source application with ordered operands,
lexical resolutions and authentic owned occurrences. It is a new proof notation
for established structural facts, not a new source or typing rule. The rule is
proved by the APPLY induction and finalization lemmas. Independent owners are
association/source nodes, ordinary lexical resolution and checked publication.
Falsifier: an output swaps c/a, maps root to the argument key, reuses a carrier
ID, or changes a lexical target. No premise mentions a desired type or result.

An IF-Use application can use these structural occurrences only **together
with** an independently typed original reference and its whole instantiated
interface, original scoped substitution, containing source/operator slot,
licenses and contextual evidence. Under those separately established inputs,
§2's existing IF-Use constructor in the original source interface definition
retains that reference incidence; structural preservation prevents its source
occurrence from being replaced during HIR projection. The present work supplies
only the occurrence identification portion of this conditional application.
It does not generate the typed-reference premise or an IF slot from a DefId.

## 7. Application to the original Call obligation and missing owners

The exact original source-interface authority is
`2026-10-08-call-source-interface-definition.md` §§2–4. Its Call constructor
retains separate callee, **whole argument**, actual returned provider/current
world, receiver phases, full Call result and dependent future-provider fields.
Lexical u_f, checking u, actual exposure and ElimOrigin are distinct. The two
concrete derivations supply authentic syntactic callee/argument incidence and
lexical identity for those admitted source occurrences. They do not supply a
whole-carrier contract merely by retaining an argument expression.

First semantic antecedent still missing at this boundary: an independently
typed original callable/reference and complete whole-argument/context interface
at the same source incidence, with original licenses, scoped substitutions and
provider/response/future contracts. Owner: original typed source/interface
formation and reference constructors (§2 of that authority). A type-unknown
formal must continue to generate/accumulate Simple-sub demands through the
approved inference algorithm; this missing proof is not permission to require
prior callability or solve constraints early during HIR admission.

First executable ordinary-consumer boundary: pinned `yu-solver/src/lib.rs`
`ConstraintBatch::collect`/`collect_mode` marks Apply/Group bodies Error (around
1109–1114); the structural observer (around 1520) records
ApplicationTypingRuleUnresolved and explicitly does not feed operands into
semantic collection. That is the exact first missing ordinary source-to-Call
constraint bridge here. CandidateInference and private source crosswalks are
separate consumers and require their own authentic carrier/registration/recipe
correspondence. A successful HIR stage cannot certify that correspondence,
source T, native Result adequacy or a joint MODEL.

Reuse the existing reviewed local FORWARD-FIRST-CALL theorem honestly:
`2026-10-16-first-call-joint-forward-preservation.md` proves its original
`receive (f: () -> 'a) = { my g = f(); g() }` case under an independently valid
hereditary input Function, compatible punctured context and one anchored joint
MODEL, for its full original observations/developments and returns. Its explicit
MODEL and lawful-map premises are not model existence or no-errors-implies-MODEL.
Our integer-argument and unannotated/module-name examples supply neither its
Unit-arrow input nor its context/MODEL. Empty/unit calls are outside the newly
adopted HIR grammar; this does not narrow the original theorem's source domain
or invalidate its existing result. No local F1 theorem is inferred for the
independent FK1 foreign-continuation quantifier.

Thus the direct parent application is precise: after source implementation and
review, the structural occurrence/operand conjunct can be used unchanged in an
original source-interface construction at these instances. The remaining typed
and native conjuncts retain their original owners and quantifiers. Original
A/B, F1/FK1, N-Transport, complete Call, soundness, principality and termination
are not closed or weakened. The bounded dependency-cut map is reused as a map,
not as proof of globally minimal premises or a replacement for the exact
source-interface/theorem statements above.

## 8. Evidence, falsifiers, TODOs and stop receipt

Source evidence reused: authoritative association; the independently consumed
fixed-source constructor audit; source-key/identity-stage owners; unchanged
carrier pass; ErrorSink's dense index construction; exact ordinary solver
pending-application consumer. Prior shadow behavior is evidence only within
its premises: `shadow_resolved_call_inventory` currently rejects empty Apply
errors (shadow.rs:249), which must be changed only by the approved ordinary
structural-observation seam. It is not evidence of Call acceptance.

Additional falsifiers, not proposed domain repairs:

- `Group(Apply(f,x))`: assigning the inner Apply the preserved root ID falsifies
  the root-constructor rule; retained Group must keep it.
- An unresolved operand: admitted shape need not have zero diagnostics.
- `Apply(Integer(1),Integer(1))`: structural admission supplies no independent
  callable certificate. No typing success is inferred from its empty name-error
  list.
- A single-element parenthesized tuple: if preflight checks only associated
  child count and loses comma punctuation, it can admit an excluded source.
- An unsupported/recovered argument after an unresolved callee: resolving the
  callee before full preflight creates an unauthorized extra operand diagnostic.
- Early child-ID allocation shifts subsequent carrier IDs; later numeric error
  ID reuse after removal creates holes or wrong cross-references.

TODO RESOURCE-R-1 (owner Luna/adopted-contract adjudication): resolve the §1
mismatch before the dependent implementation. Inputs: exact rev4 §2/§4 and
Box<[HirErrorId]> owner. Output: reviewed/adopted clarification or distinct
representation decision. Candidate output-sensitive O(V+R), worst O(V²), is
only a proposal. Falsifier of a linear-all-entry claim: the E_m family and exact
R=m(m+3)/2 count. No accepted grammar narrowing or hidden error deletion.

TODO PROJ-IMPL-1 (owner separately leased Luna implementation after this stop,
review and resource adjudication): implement/validate source-tagged preflight,
whole-tree refusal, symbolic/final diagnostic references, unchanged carrier
inputs/order, post-carrier child allocation and non-overwriting append_stage.
Existing baseline does not implement these facts. Exact falsifiers are the
root Group, distinct-source/equal-range operands, conflicting root key,
unresolved-before-unsupported child, carrier ordinal shift, and non-dense or
foreign final error references. Tests are future implementation evidence, not
proof actual constructors satisfy the judgment merely because it was specified.

TODO CALL-SOURCE-NEXT-1: after ordinary source projection exists, connect these
exact source incidences to the independently typed source interface/actual
constraint constructor and consumer, preserving all original provider/context/
response/future evidence. Owners and missing predicates are in §7. No code or
new theorem dependencies are granted by this TODO.

Claim classes: §1 is a mathematical representation/output lower bound, not an
executed compiler counterexample. §§2–6 are constructive candidate specification
lemmas and an implementation refinement obligation; they are not current-code
correctness, independently reviewed theorem status or production authority.
Original theorem conditions discharged: 0. Tests/builds/probes: none.

Resource receipt: hard cap720s, no descendants, one Astra slot. First active
clock09:20:45 UTC; counterexample receipt09:23:41 UTC. Final charged time and
remaining cap are in the handoff; exact CPU time is UNKNOWN. No further research
or dependency expansion follows the acknowledged counterexample stop; this
artifact preserves the independently completed argument and exact obstruction.
Model/effort observations remain UNKNOWN. New/scratch paths: only this artifact
and `tasks/agent-loop/inbox/20261017-ordinary-hir-call-projection-preservation.md`;
no scratch files. No code/tests/Git/external contact/central-record edits.
Three inherited UNKNOWN reservations untouched. All writes cease after frozen
handoff/hash receipt. Fresh independent review belongs to Luna, not this author.

## Frozen dependency manifest

- `notes/theory/2026-10-17-accepted-call-hir-projection.md` — `0c1a29f3d590f68064e980459a4373400702034a2366591dae32fe7b1572e25f`
- `notes/design/2026-10-17-accepted-call-hir-admission-contract.md` — `2f3b6dbb6e735b3c5da96f0bbdaa8357f7580435999e08136ce24e1bf19174ab`
- `crates/yu-syntax/src/declaration/binding.rs` — `eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544`
- `crates/yu-syntax/src/pattern/mod.rs` — `1b608422c93ce0f6947125a9b1ea88314a48b3a5e45030ed23e5154492ad7883`
- `crates/yu-syntax/src/expression/operator_chain.rs` — `81db2aec4774f2cd1ddc12b64fd9206cf41cdf3eee00ed740676ffc6d7fc5669`
- `crates/yu-syntax/src/expression/tails/mod.rs` — `a3ee107c996e028765570c7ba89b12857cd072eddc988b5b4c8eb66ffc753b8c`
- `crates/yu-syntax/src/expression/delimited.rs` — `e65c4d500ce0878faf13f1a8d31da816e5db9b6af4690b505c8875d27b700f95`
- `crates/yu-syntax/src/full_parse.rs` — `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8`
- `crates/yu-syntax/src/cursor.rs` — `f08aae49fcf048ad11890def7ef9cadab56825a63b8d87db44821a792fe9b142`
- `crates/yu-syntax/src/root_statement.rs` — `c6d1dc49625d1687ff0dae8f6808f4c97c3f78398aae3bc061c44b6fc9661626`
- `crates/yu-syntax/src/statement.rs` — `fe8ba4e144b0c3ea5c8f451dddea42f718e9c3087aa77bb81447c61a9d213797`
- `crates/yu-syntax/src/cursor/recovery/emit.rs` — `de091c117486f7990dc6872bf2ee7659c0e3e7e148e255f47b56b7836fe7c59d`
- `crates/yu-syntax/src/lexical/item.rs` — `0a1dcbd84874f6abd571e0ce7035b9ba7682ebdf7c2348c030a1ba77deabcd25`
- `crates/yu-syntax/src/lexical/current_item.rs` — `41efcce2b737a0362484e854a8549bda5f7bf0d2b911499553f1e449c6782a84`
- `crates/yu-syntax/src/lexical/lexer.rs` — `97c69c86888784ee4b3eb04d8e4685f6370dbf451631c83ec1838fe7abfc36e1`
- `crates/yu-syntax/src/lexical/expression_item.rs` — `c981a994a11c539256ef34382c4ae154395e5d438371db4959e914df58aa8c7c`
- `crates/yu-syntax/src/lexical/trivia.rs` — `887f1499fe63d870a70777626f0357c502a356d106c623d9a79e3596a17aba19`
- `crates/yu-syntax/src/lexical/observation.rs` — `730e65947f889ef07014aa003eb846012d5cec6ae1434f77edf1cbd0e7096641`
- `crates/yu-syntax/src/lexical/stops.rs` — `edcf37bbe061c0966ba786d9090361c6c3befdbe3f99aa79f29271bd5230bf5b`
- `crates/yu-syntax/src/literal/mod.rs` — `d54b4ef01cb3c9d46048b5638f9837eb050816a5e7edd35460f20cf1e557fd40`
- `crates/yu-syntax/src/literal/rule_literal.rs` — `d21f7e27eb89dfa3c6717b895726e827974728be962faefcb08c9ce9092753ee`
- `crates/yu-syntax/src/lexical/operator_scan.rs` — `145002d4254aaf186fa5176d0c6c56d89c88235e29e2da9ab1d33790a31ca3a2`
- `crates/yu-syntax/src/operator_compilation.rs` — `f1a5bd012f064d414d476acbc326c6a9804dc8128bf2e4f1800acb718a7d423b`
- `crates/yu-syntax/src/syntax_environment.rs` — `3f1e2c97c49318e02c595aa739bfb48532f7631d38afaaac4d8dfca6142cb973`
- `crates/yu-syntax/src/operator_table.rs` — `369ce0a3a8f5ac39da9da572cfe4fab6f61dd4ca07c554848cfcc44aa7051643`
- `crates/yu-syntax/src/lib.rs` — `18709b87b1b761374b5b81f90fcbf37d001fd7d981597e889aef05ad3f230f93`
- `crates/yu-syntax/src/header.rs` — `cd3791144704226f67a05ae3d39aff9b42f4380073b3e9f9817951a493bce5ad`
- `crates/yu-syntax/src/declaration/operator_header.rs` — `021e79529445054e5d54bfccf93d2287e94221a99e1554fbd7c715cb0706edbd`
- `crates/yu-syntax/src/declaration/mod.rs` — `cf1067280be3974a5702b18f47ac02cf824c9d8cf971c1bdbc1b143676fc5c71`
- `crates/yu-syntax/src/declaration/use_decl.rs` — `8a0143f4c7bb187211076f725e5116424b499c3d9c0929d9681e978e3ab83cb6`
- `crates/yu-syntax/src/declaration/mod_decl.rs` — `6adf9945e096ee027886a05857f6c187134a5331e4ab37493d95304255760741`
- `crates/yu-syntax/src/declaration/struct_decl.rs` — `7b36b18fc6ef3e149e756a37b0f74719a5ae40be195c6986efe2c44d57fa3de4`
- `crates/yu-syntax/src/declaration/type_decl.rs` — `e01d1f30c1dca051fb590a9fddac1686621fc789444f9cb053dcc269e746c134`
- `crates/yu-syntax/src/declaration/enum_decl.rs` — `9c717571426927a3619330b372ec721d1f660377ecd45c6f0ab7f6cf9ed3ec31`
- `crates/yu-syntax/src/declaration/error_decl.rs` — `56eace59a91d156f59d27a348e98ea353e9cc96595a49fc0f7e58d36dcd7a028`
- `crates/yu-syntax/src/declaration/role_decl.rs` — `0ec972a3acc036764a9d1407e292a4c676a24beb4cd0b5c3348c093cf3cf8634`
- `crates/yu-syntax/src/declaration/impl_decl.rs` — `026edcb3e6d3c9f2214be8b9fa9fd510378b64152de55673c18cb93373f62066`
- `crates/yu-syntax/src/declaration/cast_decl.rs` — `c4907b91f0cbe72606597fb6ef1918c757e9f78621a2c4c68bf0632fe629a0ed`
- `crates/yu-syntax/src/declaration/act_decl.rs` — `f1af95a12df81900564c83d0aad541064eb2fff21ca41259b7a943ae3ad4fd74`
- `crates/yu-syntax/src/expression/for_decl.rs` — `fd50ab8b049addc3c366a0eda5519fd38bda31a2b518ba139d90ad24949714ec`
- `crates/yu-hir/src/lib.rs` — `5bdcb7c0df022da919cef5402c62dc1c7baf0700a4d06e526a608cbd7db21464`
- `crates/yu-hir/src/module.rs` — `2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e`
- `crates/yu-hir/src/module/local_source.rs` — `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5`
- `crates/yu-hir/src/source_identity.rs` — `aa97bc34be51644cf944b2813af47ad9243a8eb270850eeb6df34b9cddb3b3a2`
- `crates/yu-hir/src/shadow.rs` — `2dffd7fd6542eed9fd3346e0672e76197c248be9c84334f341c4d612234b7ee9`
- `crates/yu-solver/src/lib.rs` — `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f`
- `crates/yu-solver/src/shadow_apply.rs` — `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf`
- `crates/yu-solver/src/shadow_candidate_source_crosswalk.rs` — `392d665579a74810134846e1274c0c9ce975a7eb0e2cfb9ad79a07af2cd2eeb0`
- `crates/yu-hir/src/module/source_annotation.rs` — `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f`
- `crates/yu-hir/tests/ordinary_expression_source_carrier.rs` — `36ec22c58cf790ed910ed4af93d6f9a860263efe6a5fa3fdefb7291ad3c03fbf`
- `crates/yu-solver/tests/research_accepted_call_vertical.rs` — `78fd0d4c38df86def4cd4aefb37e164f71269eb58cd9a53b370bc42e42f9a963`
- `notes/progress/2026-10-17-original-goal-minimal-cut.md` — `ee28746816f843e9e5729a879492c7b7415dcbf6a85d96e81f3eee439f5dcb8c`
- `notes/design/2026-10-17-ordinary-hir-application-admission-successor.md` — `2e61e2acb1a8981bb78592accc48207a24a5cc4c75278e100f63eb960acfeea3`
- `notes/progress/2026-10-17-ordinary-hir-application-admission-adoption.md` — `6d28dc76e321ce63588aab74d74caa6d9eb2655b2d11eb43ca700ba19edfe970`
- `notes/theory/2026-10-17-choice-a-call-cst-source-key-audit.md` — `e8a320be0e78ecc2c5ee5210338476740c03a1fae61fb2747ec39636286ad501`
- `notes/design/2026-10-08-call-source-interface-definition.md` — `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c`
- `notes/theory/2026-10-16-first-call-joint-forward-preservation.md` — `f71cc442bcccb23f7e6f1aa6221b089abb8c24d1c4ce01fecef37995541c16b6`
