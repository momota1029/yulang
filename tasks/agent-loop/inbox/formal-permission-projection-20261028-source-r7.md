# Formal permission projection r7: capture/path correspondence

Status: FROZEN revision 1 on submission; producer-authored, UNREVIEWED.
Outcome: conditional source derivation for C. No successful counterexample found.
B/D, C adjudication, r1 Lean verification, original parent A/B, source/native,
full inference/executor and production gates remain OPEN.

## Objective, baseline and authority

Assignment `/root/formal_permission_projection_source_r7`, session
`GOAL-REPLAN-EVENTPROOF-20261028`; registered researcher, observed model/effort
UNKNOWN; no descendants or coauthors. Baseline supplied by primary:
`3cc8a897fe08980576b1582952a95acab55f09d2`; no Git resolution attempted.
Contract r7 hash `40035df185bb2266f395264a137babf9b433e875922ff86f453836fba278a767`.
Exact output lease is this file alone.

Method: static equations from actual constructors, representative lookup,
capture interning/expansion and export; induction on the retained permission
path. Apply yulang-proofs distinctions between assumed source laws and source
evidence. Governing meaning: annotation policy §§1, 1.1, 1.2 and 4 (its §6 stays
retracted), and inference top-level principles §§4–5. Composed polarity and
annotation-local authority are preserved; equality of rows supplies no grant.
No selected semantics are reconsidered.

Authenticated direct dependencies (all match r7; none changed):

| Path | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| `tools/inference-playground/src/scheme.rs` | `82019fd22ad565c753461d8962934fcfe8e6663f8a7971b4fcbc5f5067026be0` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |

Frozen r6 contract `63c7079d33b639e43792a69f543f79eea1c1d9ef5cffce1f6126a4a392c28620`,
handoff `013821988ef1979b5c530754a8f6c36a440c10ce6c5597fd3e64d1a0cfef749d`, review
`31eb7c1c774bb7592680c2bc82c9d5d42d2f43d1c3c96cf677ebb9c7e452bd45` also match.
R6 supplies only its accepted conditional private-attempt/error-propagation
result. Its candidate_receiver locator is superseded by the r7 correction:
`candidate_receiver_positive_shape` is in admitted `lib.rs:11847`.
`candidate_receiver.rs` was not opened or searched.

## Exact conditional statement and premises

Fix one permission record R produced by successful originating formal
construction, not an arbitrary endpoint with equal family or representative.
Let T be that construction's negative domain, pi its retained path, o its
occurrence, and q the raw effect row allocated for the concrete negative
permission at that occurrence/path. Let S be the session at this particular
successful capture; let M be its actual endpoint-to-node-index interning map
immediately before destruction at capture return. For endpoint e, write k(e)
for capture-time canonicalization, including its polarity. Define I(e)=M[k(e)].
The statement is:

    successful projection of R from this captured graph returns
    index I(Effect(EffectRow(q), Negative)), occurrence o, and path pi.

This is an equality to the actual capture image, not equality to raw row q,
an independently reconstructed fresh graph, or a later representative.

Explicit premises, not newly established universal facts:

- Remaining B supplies that R, its parameter-to-T association, the term-store
  lineage and original constructor children survive to this capture, and that
  the final exported graph/state association is this capture with that same R
  and domain. No intervening replacement, stale-key reuse or escaped failed
  attempt may substitute another originating association. This is the still
  open transitive lifecycle/ownership obligation; r6 does not discharge it.
- The representative structures are well formed on the reachable successful
  session: lookup terminates and same-kind parent chains have their intended
  roots. The operations below support the local invariant; this packet is not
  a whole-program forest audit.
- D supplies successful capture and successful export/projection for R. In
  particular the negative formal root was actually captured, all requested
  shapes and rows are available, allocation/resource checks succeed, and the
  final port is an Effect Row. Capture termination is conditional here.
- Ordinary Rust/std allocation, borrowing, indexing and map semantics apply.
  No unsafe concurrent mutation or memory corruption invalidates those semantics.

The derivation below establishes the structural implication under these
premises. It does not infer B from D, and does not assert D universally.

## Actual constructor equations: the originating path

`candidate_effect.rs:1419–1492` constructs the paired value trees. Tuple
recursion appends Element(i), recurses at unchanged variance in enumeration
order, truncates back to the saved prefix, and stores positives/negatives in
that same order. Function recursion reverses variance for Argument and
preserves it for Result. It appends the corresponding step separately for
value recursion and effect-port construction. Its exact paired Function terms
are, naming the child pairs (ap,an), (qap,qan), (qrp,qrn), (rp,rn):

    F+ = Function+(an, qan, qrp, rp)
    F- = Function-(ap, qap, qrn, rn).

The fields are always argument, argument_effect, result_effect, result.
`term.rs:1230–1279,1390` validates their kind/polarity and interns exactly those
fields; tuple construction copies the element slice in order (`:1295`).
`TermNode::view` returns the same fields (`:271`); branch `term_view` is lookup
followed by that view (`:856`), and the store forwards it (`lib.rs:3714`).
Lookup checks the lineage brand and selects collected-prefix or page/offset
storage (`term.rs:831`). Successful interning hits return the matching stored
Term; misses publish the supplied node (`:1166`); successful tuple structural
interning retains the backing (`:1358`). These are local constructor/readback
equations. Survival across rollback/replacement remains B.

`candidate_formal_effect_port` (`candidate_effect.rs:1496–1544`) emits R only
for nonempty concrete, variable-free rows at composed Negative variance. It
allocates q, clones the current path, occurrence, source owner, scope, source
row position and concrete operands into R, then returns live Effect terms
(q+,q-). Live terms are interned with that ordinal and requested polarity
(`lib.rs:10542`, `term.rs:1205`). Thus the selected negative tree path ends at
q-; this is derived by induction on the original construction: root variance
is Negative (`candidate_effect.rs:1662`); each Argument flips both variance
and selected paired-tree side, Result preserves both, and Element preserves
both. A permission can only be emitted when the resulting side is Negative.
It may sit inside a Positive Function reached after an earlier Argument;
nearest textual field names alone would be insufficient.

## Canonicalization and the actual interning invariant

`lib.rs:11839,13491` canonicalize only ValueRow and EffectRow respectively;
Function/Tuple term keys, other endpoint forms and polarity are unchanged.
`candidate_intrusion.rs:119` follows parents until a fixed point or missing
entry. If this lookup terminates at r, a second lookup at r immediately stops,
so rep(rep(x))=rep(x). This includes an absent entry, which is its own returned
representative. It is a consequence of the actual loop, not an assumed
transition rule. A cycle would invalidate termination and is outside the
successful well-formed premise.

Visible births append self-parents (`candidate_intrusion.rs:342–352`); merge
first resolves both operands (`:613–619`), returns if equal, checks same kind,
then links the from root to the distinct to root (`:679,691`). Under a forest
invariant this creates no cycle and preserves roots for unaffected classes.
Journal rollback restores recorded parent values in reverse (`:203–224`).
This is local support, not an exhaustive transitive proof of every forest
lifecycle. Distinct q values may merge before capture; I uses their actual
capture-time canonical representative.

Crucially, `Capture.session` is `&InferenceSession`
(`candidate_scheme.rs:1594`), not a mutable session reference. Its intern,
shape expansion and row expansion read the session store/forests while mutating
only capture-owned structures; relevant bodies are `:1713–1738,1800–2090,
2137–2260`. Representative functions only read forest vectors. Thus throughout
this capture k is stable, and k(k(e))=k(e). Resource metering's separate Cell
and test counters do not rewrite these source fields. No source merge occurs
between child interning and pending expansion in this borrow.

Actual invariant, maintained for every successful capture operation:

1. M's values designate allocated, never removed node positions. On a miss,
   intern allocates index nodes.len(), pushes a placeholder and exactly one
   pending canonical key, then inserts M[key]=index (`:1713–1723`). On a hit it
   returns the existing index without replacing M or creating another pending
   copy. Allocation failure supplies no successful return and is excluded by D.
2. intern_shape canonicalizes, records a shape frontier if necessary, then
   calls intern (`:1725–1738`). Idempotence makes the double canonicalization
   harmless. A node already interned through a bound has the same index when
   later requested through a structural path.
3. expand_node fetches index=M[key] (`:1935`), builds that key's node using
   child interning, then writes nodes[index]=node (`:2087`). It neither removes
   nor remaps any key. Different child insertions append nodes, so no existing
   index changes. Shared ports produce equal indices precisely when canonical
   endpoint including polarity is equal; opposite polarities remain distinct
   endpoint keys even if their Row descriptor is shared.
4. The outer capture loop drains pending, expands rows, and repeats after
   latent/context discovery (`:2671–2703`). Returning successfully requires no
   pending nodes. Thus every M entry used on the path has its expanded shape,
   rather than its temporary Bottom placeholder. Bounds and latent roots can
   add keys but preserve all previous associations.

This invariant is about the actual source map and writes. No checker assumed
it as a transition axiom; no separate oracle was used.

## Child equations and induction through export

Let E(t,K,p) be `Capture::term_endpoint(t,K,p)` (`:1800–1930`). It maps
LiveVariable to its ordinal with matching kind/polarity; components use the
session's component translation; Function/Tuple terms retain their exact term
key and matching polarity. The permission path's terminal terms are live q
terms, so its final equation does not need an inverse component recipe law.

For an expanded Function endpoint at polarity p with term fields t0..t3,
`candidate_scheme.rs:1973–2027` gives exactly:

    children[j] = I(E(tj, Kj, pj))
    K = [Value, Effect, Effect, Value]
    pj = [opposite(p), opposite(p), p, p].

For Tuple(t0..tn-1) at polarity p, `:2068–2084` gives:

    tuple_children[start+i] = I(E(ti, Value, p)), 0 <= i < n.

The tuple range is reserved/resized before recursive child interning and
filled by offset; other tuple expansions occur later from pending. No sorting
or representative deduplication changes element positions. Term interning
may share identical subtrees; path induction uses positions and not uniqueness
of term identities.

At the start of export, successful negative-root lookup is for exactly T:
`candidate_scheme.rs:2787–2799` recognizes NegativeFunction(T) or
NegativeTuple(T,n) and looks up that exact negative endpoint in M. Structural
keys are fixed by k, so the stored root index is I(E(T,Value,Negative)). Missing
root is an error, not a falsifier. Export selects the frozen state's graph by
authenticated definition position (`shadow_apply.rs:2029–2054`); the required
capture-to-final-state association is B, not inferred from a successful lookup.

Induction invariant at each nonterminal prefix of pi: export's current index
is I of the corresponding original selected value subtree and composed
polarity. Base is the negative-root equation. For Element(i), the Tuple child
equation proves the next invariant at the same polarity. For nonterminal
Argument, export chooses children[0], so the Function equation proves the next
invariant with flipped polarity. For nonterminal Result it chooses children[3]
and preserves polarity. At the final Argument it returns children[1]; at the
final Result it returns children[2]. The constructor induction identifies that
exact field as q- for R; the Function equation therefore gives
I(Effect(EffectRow(q),Negative)). Final Element is rejected, consistent with
permissions originating only at Function effect ports.

The export implementation is `shadow_apply.rs:2650–2686`; it also validates
the returned node is a Row whose descriptor kind is Effect. It pushes the same
ordered path steps and borrows R's occurrence/source_row/concrete (`:2688–2694`).
It does not merge or deduplicate permission records by endpoint index. Two
records whose ports alias remain separate records with their original o/pi;
this proves identity transport even when the returned node index coincides.
No conclusion about permission authority follows from coincident indices.

Conditional conclusion: under B, representative well-formedness and D, the
retained path/export index equals the actual capture interning image of the
originally selected endpoint. No additional owner was required for these local
equations. There is no reachable successful out-of-image witness in this
packet; representative merges, shared ports and missing roots do not supply one.

## Checks, limitations and next action

Commands: `cat`, focused `rg`, `sed`, `head`/`tail`, and `sha256sum` on the exact
admitted source/policy and frozen r6 inputs. All pins matched. Some broad reads
were truncated; focused reads supplied constructor, representative, capture,
term storage and export bodies used above. No tests, probes, builds, Cargo,
Lean/Lake, Git, network, descendants, Rust edits or quarantined-path writes.
No seeds/ranges/mutations or executable search applies. This is producer static
analysis under ordinary Rust/std semantics, not an independent oracle or review.

One sequential lightweight process at a time; no heavyweight execution. Exact
CPU time/RSS and elapsed wall time were not instrumented; command-reported wall
times were subsecond. No resource exhaustion observed; numerical peak usage is
UNKNOWN. Scope is finite source inspection, not exhaustive input enumeration.

Unverified: universal B/transitive no-replacement and no-escape, forest
well-formedness for every reachable execution, capture termination/resources,
universal D, r1 Lean proof checking, source-to-HIR realization, native execution,
full inference/executor and production application. No original quantifier is
weakened and no parent gate is closed. Recommended next action: fresh non-author
compiler_referee review of this frozen conditional C derivation, especially the
paired-tree induction and capture-to-final-state B boundary, before any bridge
or promotion. Writes stopped after this revision; no descendant leases exist.

## Commit packet

- Exact leased/changed paths: `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r7.md` only.
- Baseline SHA: `3cc8a897fe08980576b1582952a95acab55f09d2` (primary supplied).
- Changed dependency hashes: none; authenticated hashes listed above.
- Claim/review status: conditional source derivation; UNREVIEWED, research-only;
  B/D, C adjudication, r1 Lean, all parent/native/production gates OPEN.
- Checks already run: exact dependency SHA-256 authentication and static source
  reads only; no executable verification.
- Proposed commit message: `research: derive conditional formal permission capture image correspondence`
- Shared-record deltas left to primary/curator: record conditional C result and
  remaining B/well-formedness/D premises; assign fresh review; preserve the
  corrected lib.rs receiver locator; mark this worker STOPPED and lease FROZEN
  from this cessation receipt. No shared record was edited.

STOP.
