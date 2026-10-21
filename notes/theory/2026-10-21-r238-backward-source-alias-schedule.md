# R238 — Backward source alias schedule from raw consumers

Status: partial constructor-level weakest-precondition result; unreviewed. R71, R72, and the original Simple-sub theorem remain OPEN.

## Fixed parent and method

R238 keeps the original computation-forwarding claim, source domain, quantifiers, approved Value-SCC occurrence qualification, and contextual residual-lineage policy unchanged. It starts at a later production Work::Bound and works backwards through the exact raw lookup, its relation consumer, typed-drain stages, attachment constructors, equality canonicalization, and finally the source Action/Value association required to produce the event.

The controlling contract is tasks/agent-loop/sprints/simple-sub-backward-source-alias-20261021-r238-rev2.md, SHA-256 928e2b33167961d5f6d816292a5c0c0a349caa49482f247c115b43b0b605c5ae. The frozen boundary inputs are R237 (9d93bf9e4579adf8ac88d05325431610757a1c844e85894b47308aa86a7a291e), R236 (95dce8a15b7e9c57b94f6c5741cb7af1b4056fe32af66fb7adfe41db99c68144), R71 (620947cece53ca60a7f8a2388a398f53850b835c79afd546bfdcfd10349a876e), and R72 (504abc36cd877407b57b744484640c3fb2f8e12d09f08bfe90188dc700ee18a5). The contract pins the governing design authorities and exact current solver files.

## Backward constructor result

Write k=(owner, polarity, item) for the physical slot's stored raw BoundKey; C_t(k) canonicalizes its row endpoints at time t; and F_t(k) is the ordered relation-fiber bucket attached to exactly k.

The selected extrusion Visit captures the physical slot's raw item b, builds an operation-local key from the canonicalized b, and queues Work::Bound(copy_owner, polarity, canonical_item, raw_source=k). In the Work::Bound arm, the operation-local key chooses the copied endpoint, but candidate_transfer_bound_origins(k, destination, Extrusion) reads bound_cursor(k). It walks exactly the relations in F_t(k) and creates a witnessed transport child for each parent. It separately copies origin-table entries as metadata with MissingOriginAssociation; those entries do not create executable relation fibers.

The equality sweep has the opposite index direction from the missing claim. For each retained raw key k', candidate_context_canonicalize_bounds computes C_t(k') and transports each existing parent in F_t(k') forward to that canonical key with an EqualityCanonicalization witness. The raw key and parent remain. If k' != C_t(k'), the sweep does not attach its child back to k'.

Consequently, the exact code-level transfer equation is:

    WorkBoundFibers(s,t) = witnessed_Extrusion_map(F_t(raw_key(s)))

It is not witnessed_Extrusion_map(F_t(C_t(raw_key(s)))), nor a reverse saturation of the canonical bucket. A canonical child from a different raw key k' can be seen by a canonical-key replay, while the WorkBound selected from k still reads only F_t(k).

For a fixed successful WorkBound event and its actual cursor snapshot, a named relation c is an exact transport parent if and only if c occurs in F_t(k) at that snapshot. This follows from the helper's complete, ordered cursor traversal: it saves each next pointer, emits one witnessed transport for each encountered relation, and performs no lookup by canonical key, pair equality, ancestry, or origin-table association.

This describes the constructor and lookup; it does not yet say that every canonical child is an independently required input to this copying occurrence. That requirement belongs to the unchanged original consumer theorem, not to row equality or a relation's existence in the canonical bucket.

## Exact weakest precondition for a required canonical child

Fix a selected WorkBound W with raw source k, canonical key K=C_t(k), and a canonical child c at K. For W to transport c by the direct raw-bucket route, the necessary condition is c in F_t(k) at the actual lookup. If c is only in F_t(K), the direct transfer does not read it when k != K.

An alternative proof must provide an actual constructor path from some r in F_t(k) to a copied relation whose consumer obligation is equivalent to c's obligation. That correspondence must retain the exact RelationId, source set, dependency parent, transport witness/FiberTransform, scoped payload, creation-time context, discharge state, and selected residual lineage. Endpoint equality and common ancestry do not establish it.

A possible alternate route is a selected physical sibling whose own raw key is K: its WorkBound reads F_t(K) and may transport c. This is a separate event, not evidence that the stale-key event W read a canonical bucket. It discharges W's theorem obligation only if the unchanged parent semantics independently licenses that sibling event as a consumer-equivalent witness for the same selected residual lineage. R230/R236's physical-prefix result must account for every same-class sibling before this case is used.

Thus the consumer-side weakest precondition is the following disjunction, for each independently required child c:

1. c is in the exact F_t(k) bucket read by W; or
2. an existing, source-derived transport from a member of F_t(k) yields a consumer-equivalent descendant with the same required residual lineage; or
3. another selected physical sibling has exact raw key K, and its own WorkBound transports c with the required lineage.

This is a necessary condition on a proposed coverage proof, not a theorem that one of the alternatives holds for every accepted program.

## Inverting production attachments

R236's exhaustive census yields four production attachment routes:

| Route | Backward requirement for an attachment at key k | What it does not supply by itself |
| --- | --- | --- |
| candidate_context_bound_for from successful owner emission / extrusion link | A real relation and bound admission are constructed for the insertion key; successful physical insertion reads back the same canonicalized key. For the exact raw key, the insertion-time key must equal k. | A later raw key after representative changes, or a reverse edge from a canonical key. |
| candidate_context_fresh_transport_scoped | An authentic retained Local/FreshUse route maps an existing parent to destination k, with its source/use identity and FreshUse witness. | Equality-canonicalization ancestry or an arbitrary equal-row relation. |
| candidate_context_transport_witness_with_evidence | An existing parent, exact from/to, and constructor reason produce a typed Transport and FiberTransform, then attach at to=k. | Any destination other than the exact to; no witness is reconstructed from endpoint equality. |
| candidate_context_transport_witness without evidence | No production caller reaches this no-witness branch; the wrapper's direct no-witness caller is test-only. | No production reverse transport or source admission. |

An extrusion link is a relevant candidate descendant rather than a direct copy of the processing RelationId. Before selected bounds are traversed, a deep-row Visit admits an opposite-polarity link. Its bound constructor may use the current processing relation as the Derived parent when its pair matches the origin; otherwise it interns an origin relation first. The link's side is opposite the current WorkBound side, so it is not that same Visit's selected bound. A later opposite-polarity Visit can select it and transfer the link relation. This is a real possible ancestry path, but its BoundAdmission evidence records ProcessingAntecedentsUnavailable, OrdinarySeedAuthenticationUnavailable and MissingAntecedent. R72 also found a source link slot without a checking event and with no source set. Therefore the link alone proves neither source licensing nor that its descendant discharges the same consumer obligation as c.

For the equality-sweep route, to=C_t(k'). It reaches a stale raw bucket k only if an independently recorded constructor actually has that exact destination, or if C_t(k')=k; equality of canonical representatives alone does not reverse the transport.

For WorkBound and ParentCopy, insertion of the destination physical slot and transfer of the exact raw source fibers are separate ordered actions. A successful event preserves that source lineage; a failed/rolled-back attempt is not an admitted source history. The merge sweep runs after representative write and scans the captured prefix; it cannot retroactively justify an earlier source read.

## Consumer and chronology boundary

candidate_context_begin_replay indexes both input buckets by their supplied keys and combines each relation's original key.context; it preserves ordered replay dependencies. A later transport uses post_check_context(parent). Discharge and residual are keyed by RelationId, so consuming canonical child c can alter c's later post-check context without changing a distinct raw parent r's state.

Within one typed drain, the source order is Transport → Context → Dispatch. Dispatch can lead to an extrusion that schedules a WorkBound in the same chain. This establishes control-flow possibility, not a source-derived occurrence satisfying the consumer weakest precondition. For a replay-based consumer, the proof must identify the exact input key and child; for a later raw transport it must identify the exact parent and then-current post-check residual. Those are separate obligations.

## First missing source/semantic edge

The constructor graph answers how a fiber could reach the exact raw lookup. The remaining missing premise is whether an accepted source can make a canonical child independently required at a later copying occurrence while none of the three weakest-precondition alternatives holds. R237's accepted callback candidate supplied no slot-4 alias to a later raw WorkBound; R72's annotated helper prefix did not supply the later qualifying occurrence. Neither finite result settles the parent.

To finish this edge, source evidence must join: (a) an authentic source Action producing the relevant bound/physical slot; (b) the actual qualifying extrusion occurrence and all parent/copy pairs; (c) the equality/attach history giving c its canonical key; (d) the later selected physical slot and exact raw bucket; and (e) the original consumer's independent residual-lineage requirement. If (e) is not determined by the existing theorem/source authority, the original semantic consumer owner must supply it; no RelationId requirement may be invented.

## Fixed parent consumer boundary

The fixed parent is `notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1, 6–7. Section 1 keeps one shared satisfying assignment, original formals, arbitrarily long finite forwarding chains, repeated calls and simultaneous receiver entries. Sections 6–7 distinguish original registration bounds from each authentic FreshUse instance map `mu_i`. For an actual provider comparison, the mapped Name/body bounds must actually be admitted (`mu_i(e_t) <= mu_i(e_n) <= mu_i(e_R)` and `mu_i(e_n) <= mu_i(e_t)`), and each forwarding Apply must join its actual argument/output to that instance and the next provider's own map. This per-use mapped-bound admission and source-to-native join remains OPEN.

That parent fixes the semantic consumer condition for this packet: establish the relevant actual per-use map and admitted bound chain for the same source forwarding route, then show the resulting consumer obligation is covered at the later use with its selected residual lineage. Solver `RelationId`, `BoundKey`, or endpoint equality is not itself the parent's `mu_i` correspondence. The source map must identify which solver bound realizes each mapped source bound, and the actual admission/activation must be shown on that route. Therefore the exact-fiber weakest precondition above is a constructor-side condition only; R238 has not yet proved that every parent-required mapped bound reaches, activates at, or is consumed by a particular raw WorkBound. No new RelationId-level theorem obligation is added to the parent.

The result narrows the proof target to a specific consumer-coverage implication. It does not establish the source schedule, a universal no-gap theorem, a source-qualified counterexample, R71/R72, semantic approval, or production readiness.

## Evidence and limits

This is a source-independent local constructor derivation based on the pinned current code and R236/R237/R71/R72 artifacts. It uses no manually assembled graph, source execution, test, build, compiler change, or semantic change. Static repository consistency remains a separate check. No independent review was run. R71/R72 and the original parent remain OPEN; full solver tests, semantic approval, and production remain OPEN.
