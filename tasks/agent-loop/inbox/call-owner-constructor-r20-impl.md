# R20 implementation owner audit — revision 1

Sprint/contract: `CALL-OWNER-CONSTRUCTOR/20261028-r20`, revision 1, SHA-256 `0b19ec601ee40765fdd1f74235d0b6f35e0c6e195a4a032672f40c7358c410f1`.  
Input manifest: SHA-256 `ebd5164460314d7b6a940e9a9caf2bbbe385c105bc8f4ff15f13e7daa9eec57d`.  
Role/author: Luna primary implementation audit.  
Outcome class: **owner-specific NO_SAFE_CODE_SLICE**. This is a source audit, not independent acceptance or parent proof.

## Frozen bytes and inspected owners

The R18 snapshot was used, not the R19 selector overlay. Directly pinned R18 source hashes:

- `candidate_effect.rs` `7c8e4fe5270fd45cecece80dfbbdff81aa8f294546687938bf89212325fc146b`
- `candidate_context.rs` `be1be2277d54288ba4ae542e003dabc294031c29cb26b2b5d0454b0d1c102bd0`
- `candidate_scheme.rs` final R18 bytes `3eb9ba3b414dd0e40f49957e0ee2b9de1ba21fd86dff718111d1b5030ccac6b7` (the R18 manifest pins its pre-result baseline separately)
- `candidate_call.rs` `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f`
- `shadow_apply.rs` `8db4bae1b79959161b6b0dc4d516164b0e756eb8cbc73896bb4a4545a0b0ebf8`
- `candidate_extrusion.rs` `a6538ab3deae503fd2c002c88fb673a51848a350b226b8a38c3b43496cdd03ee`, verified against the pinned R18 manifest.

Inspected `candidate_effect::candidate_bound_origin_with_evidence` (lines 551–620), `candidate_extrusion::candidate_insert_bound` and copied-bound path (lines 635–660), `candidate_context::candidate_context_bound_for` (around 4063), `candidate_scheme::capture_candidate_graph_inner` and its negative-root/demand retention (2635–2976), the R18 demand observer/reconstruction (around 952–1050), and `candidate_call` source observation/scoped-call authentication (around 100–740).

## Producer-to-consumer account

The lower `OwnerEmission` evidence is built from the emitted `BoundKey`, an optional typed pair or current processing relation, and a `BoundAdmissionCause::OwnerEmission { processing: Option<RelationId> }`. The scoped path creates/attaches a candidate context relation for the bound and origin pair. The cause contains no original Call constructor identity, `completeCallCertificate`, `sourceCallIncidence` derivation, or producer-owned ordered Function-port tuple. `candidate_insert_bound` publishes a physical owner/polarity/item bound with this cause; copied physical bounds are bootstrapped separately and receive `BoundTransport` evidence.

Capture retains actual graph nodes, row mappings, scoped relation maps and evidence snapshots. It first populates `negative_formal_roots` from live `formal_domains` whose terms are negative Function/Tuple terms, using the already indexed endpoint. It then walks captured bound demands and inserts a negative Function endpoint selected by the demand root term when the node and bound relation checks succeed. This is concrete capture/reconstruction evidence for the candidate graph. It does not recover the original Call source derivation or establish that a matching term was emitted by the constructor-owned producer required by J-Owned/C-Call.

The retained FreshUse observer joins a route using use-instance/context IDs, original call/root demand, a unique captured relation and bound, retained scoped demand, imported snapshot, remapped scope/input, and a negative Function node. It reconstructs the ordered four-port tuple `(argument, argument_effect, result_effect, result)` from `Node::Function.children[0..4]` and the retained term map, with kinds `[Value, Effect, Effect, Value]`, then compares it with the terms supplied by the candidate graph. This is the candidate-native ordering; it does not identify an original source owner. `candidate_call` separately authenticates the source/HIR Apply owner and Local FreshUse route. These joins authenticate the candidate's own recorded structures; no inspected equation joins that source Call owner to the original semantic Call owner and the specific lower `OwnerEmission` that supplied all four ordered ports.

## First absent supplier and disposition

The first missing implementation-side supplier is the constructor-owned identity/incidence equation:

```text
one original source Call derivation and shared xi
  -> its actual lower OwnerEmission identity
  -> captured Function producer and its four ordered typed ports
  -> the same Call consumer after FreshUse/replay transport
```

The existing `OwnerEmission` payload and candidate term/endpoint joins do not supply that equation. Adding an ID or equating terms in this lane would invent the source owner relation; changing the cardinality selector would not close it. Therefore there is **NO_SAFE_CODE_SLICE** under R20. No source, test or candidate file was changed, and no Cargo/test/build/formatter/Lean command or Git operation was run. No production or parent gate changes.

Primary audit began within the R20 session and concluded at `2026-10-28T14:01:38Z`; active work was not independently metered, so exact time/CPU/RSS are UNKNOWN. This receipt is frozen at revision 1; no writes remain on its path.
