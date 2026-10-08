# Proposed PE frame-to-root-slot contract

Status: research proposal; non-authoritative; exact-contract review passed
Scope: connect selected source `Instance` / `Alias` ownership to the already
selected ordinary public-root slot direction
Implementation, API, production-routing and F5-cutover authority: none

## Question

The selected source rules distinguish a real polymorphic instantiation from a
monomorphic alias, while the selected PE decoder requires a distinct ordinary
root for each real `new` and the identical root for aliases. Current HIR and
solver handles do not retain this distinction. The approved Direct architecture
permits dense root slots in a uniquely identified immutable environment, but
does not select the producer that connects source frames to those slots.

This note proposes the minimum typed output and validation relation needed at
that boundary. It does not select a Rust API, allocator, malformed-input
diagnostic, environment rebuild policy, storage layout, failure policy, or
resource limit.

## Selected contract to preserve

Source Generalize §3.4 puts `new(p,i,r)` only at an actual source
instantiation rule. It produces `Instance(p,i,r)` or `Instance(d0,i,r)`.
`alias(h,j)` produces `Alias(h,r)` and carries the same monomorphic handle and
certificate; it has no instantiation, template, or initializer replay. Its
§5.2 whole-frame action keys eligible declarations and ViewLogic by the
instance, keeps fixed and Shared fields original, and preserves actual event
ownership separately from frame-local EventProof witnesses.

PE construction §4.2 allocates one ordinary root `u_i` for a real new frame,
installs that frame's complete active equations, and returns that same root for
an alias. Equal endpoint terms do not merge separate roots. The approved
Direct direction binds root and law references to slots in one validated
immutable environment with a unique environment identity and generation.

## Proposed producer output

At the source rule that already owns the classification, emit a typed event
record joined to its original publication/component/root and scope records:

```text
FrameEvent =
  New { instance_key, publication, member, source_root, original_scopes,
        complete_frame_action }
| Alias { alias_key, antecedent_handle, source_root }
```

`instance_key` is an artifact-local identity minted for this actual `new`
event. It is not a source spelling, HIR ordinal, Q/R binder ordinal, endpoint,
or caller-supplied public-root number. The complete source frame-key and
binder-routing schema is fixed by the owning constructors before assignments,
challenges, or histories; a post-solve pass cannot choose or repair those
keys. `antecedent_handle` resolves to the existing monomorphic handle; alias
resolution does not mint another frame.
`complete_frame_action` references the selected declaration, ViewLogic,
Shared, event and EventProof records with their original scopes and dependent
incidences. It cannot be reconstructed from a solved type row.

This is a logical record contract, not a claim that current HIR/solver code
already emits these fields. Existing branded handles can be retained as
provenance joins only; a reviewed bridge must establish the source rule and
owning local-law outputs.

## Proposed validated public-root correspondence

For one immutable environment `E`, validation produces a total map from every
admitted PE instance key to one dense root slot. Within this proposal, alias
routing covers only aliases whose antecedent is one of those admitted PE
instance frames. Source aliases of an established `Mono(h, Contract_h)` import,
capture, or rebind have no required `New` ancestor; their genuine installed
root owner and correspondence are outside this proposal and must not be
fabricated here. The candidate invariants are:

1. Every `New` has exactly one slot, and distinct `New` keys map injectively
   even when endpoint and equation payloads are equal.
2. Every in-scope `Alias` resolves to an already admitted PE instance handle
   and then to exactly its existing slot; it creates no slot or frame action.
   Established external handles remain fixed at their actual installed roots
   under their separate owner.
3. Each slot contains the full PE equation image and original scope/incidence
   map for that frame. Lookup is total for admitted handles and never consults
   source syntax or the source relation.
4. Fixed anchors, Shared fields, and actual event operands retain their
   original identities. Only the selected eligible declarations and
   frame-local ViewLogic/EventProof fields follow the whole-frame action.
5. A certificate names `E`'s immutable identity/generation and exact slot
   operands. A stale or foreign environment reference cannot validate merely
   because a numeric slot is reused.
6. Validation establishes structural correspondence only. It does not derive
   semantic laws from table membership, IDs, endpoint equality, or successful
   F5 solving.

The source contract requires frame and binder routing to be determined from
the source constructors before assignments, challenges, and histories. This
proposal does not prescribe the later compiler's concrete storage timing, but
the bridge must preserve that source allocation order.

These conditions are obligations for any later implementation, not a selected
malformed-map behavior. Duplicate keys, dangling/cyclic aliases, slot
exhaustion, stale references, and rebuild/transport need an explicit failure
and lifetime contract before implementation.

## Falsifiers and current gap

- Two real `New` events with identical endpoints but one root falsify
  injectivity.
- One `Alias` with a new slot or a replayed initializer falsifies literal
  reuse.
- A distinct event operand freshened with the description frame, or a
  frame-local EventProof shared across independent frames, falsifies the
  selected key partition.
- A fixed import changed by frame allocation falsifies fixed-anchor
  preservation.
- A Direct certificate accepted against a rebuilt environment that merely
  reused the slot number falsifies environment binding.
- A public-root lookup that reads HIR/source bodies or reconstructs from F5
  rows fails the selected producer/consumer boundary.

Current `SourceNodeKey`, `HirOccurrenceId`, `DefinitionRootId`,
`DefinitionUseId`, and Q/R ordinals do not supply `instance_key` or the
frame-to-slot map. The bounded owner audit also identified no current ordinary
public-root allocator/store/readout owner. Established imported-root routing
is a separate correspondence still to be mapped. Consequently this proposal
does not establish the source-to-compiler bridge or authorize implementation.

## Next evidence and limits

The next source-side evidence is an actual successor caller that emits the
typed `New` / `Alias` events together with each required source-owner and local
law output. The next public-root evidence is a concrete producer, immutable
store/readout seam, identity-observer inventory, and reviewed correspondence
proof. The Direct caller/local-law map and numeric limits remain separate
required design work under the approved q1/d1 answer. Numeric limits cannot
be responsibly fixed before the actual caller and per-attempt work schedule
are known.

Review: one independent `spec_auditor` pass and delta review. The review found
and this revision closed the alias-domain and allocation-timing findings. The
review does not select this producer contract or authorize implementation.
`git diff --check` passed. No compiler changes, tests, builds, benchmarks, or
measurements were performed for this proposal.
