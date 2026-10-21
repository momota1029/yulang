# R236 — Production attachment ancestry for R71

Date: 2026-10-21. Status: partial source/native lemma; R71 and the parent
theorem remain OPEN. Author: Luna solo primary; no independent review.
Sprint: `simple-sub-attach-lineage-20261021-r236`, contract revision 1.
Parent: unchanged R71 raw/canonical fiber coverage and the original
computation-forwarding / Simple-sub theorem.

## Result boundary

The live production source has exactly four `State::attach` call sites in
`candidate_context.rs`; additional direct calls are confined to the
`#[cfg(test)]` context-test module. The census gives an exhaustive partition of
production bound-fiber attachment:

| Attach site | Constructor path | Physical/source relationship |
|---|---|---|
| `candidate_context_bound_for` at line 3796 | `candidate_bound_origin_with_evidence` for `OwnerEmission` / `ExtrusionLink`, called inside `candidate_insert_bound_with_evidence` | Relation is attached before the append. The enclosing insertion appends to the addressed lane, reads the exact physical slot back, and emits its admission/slot/readback record before successful return. Failed insertion is not an accepted source history. |
| `candidate_context_fresh_transport_scoped` at line 4150 | `begin_candidate_fresh_bound` → `candidate_begin_bound_restoration` → `candidate_insert_bound_with_evidence` | The FreshUse relation is prepared first, then the same bound-construction sequence inserts and reads back the mapped physical slot. Resumed Local use retains the restoration cursor; transactional failure rolls back the attempt. |
| `candidate_context_transport_witness_with_evidence` at line 4191 | `candidate_transfer_bound_origins` | Used for `Work::Bound` extrusion, `ParentCopy` merge slots, and the equality sweep below. For `Work::Bound` and `ParentCopy`, the destination physical slot is inserted first and the transfer then attaches at its destination key. |
| `candidate_context_transport_witness` at line 4217 | No-witness helper branch | No production caller reaches this branch. The production caller in `candidate_context_canonicalize_bounds` passes `Some(EqualityCanonicalization)` and returns through the evidence-bearing helper at line 4200; the direct no-witness wrapper is `#[cfg(test)]`. |

Relevant source routes:

- `candidate_effect.rs:522–545` maps owner emission to
  `candidate_context_bound`; scoped `BoundTransport` records metadata with
  `relation: None`, so it does not attach a fiber.
- `candidate_extrusion.rs:509–673` canonicalizes the insertion key, admits its
  relation, appends the physical bound, checks exact readback, then emits the
  physical/evidence record. `candidate_begin_bound_restoration` calls this same
  insertion at `candidate_extrusion.rs:773–792`.
- Local FreshUse prepares its mapped relation at `candidate_scheme.rs:2151–2170`
  and immediately routes it through that physical restoration. The retained
  Local cursor resumes the same bound at `candidate_scheme.rs:2429–2443`.
- `candidate_extrusion.rs:157–165` schedules each selected physical bound with
  its exact raw source key. Its `Work::Bound` arm inserts the copied slot before
  `candidate_transfer_bound_origins` (`candidate_extrusion.rs:319–342`).
- `candidate_intrusion.rs:636–663` copies each physical parent-merge slot and
  then transfers its raw source fibers before writing the representative.
- After a representative write, `candidate_intrusion.rs:693` invokes
  `candidate_context_canonicalize_bounds`. That sweep iterates the retained
  `bound_keys` prefix, preserves each raw key and parent, and forwards the
  parent to the current canonical key with an explicit
  `EqualityCanonicalization` witness (`candidate_context.rs:4091–4105`).

Therefore the sole production attachment that is not itself paired with a
physical slot at the destination key is equality canonicalization. It is not a
new source root: the exact retained parent relation is recorded in both the
`Transport` dependency/FiberTransform and the additional `Derived` edge. The
raw attachment is preserved. This closes the possibility of an unenumerated
production fiber constructor, but it does not yet establish that every
canonical descendant is independently required by a later copy consumer.

## Conditional sibling-lineage lemma

Fix one successful production `Work::Bound` selected from a Visit's physical
prefix. Let `k=(owner,polarity,item)` be its raw source key. Suppose a fiber `c`
at the current canonical key `C(k)` was introduced only by a successful
equality sweep from parent `r` at some raw key `k'` with `C(k')=C(k)`.

The code-derived facts are:

1. The sweep preserves `r` at `k'` and records `r → c` with the exact
   `EqualityCanonicalization` source/destination witness. The child uses
   `post_check_context(r)`, the parent's source set and scoped flow, subject to
   the explicit endpoint remapping in `transported_scoped`.
2. `Work::Bound` does not look up `C(k)`; it looks up `k` and transports every
   relation in that exact retained raw bucket. `candidate_transfer_bound_origins`
   advances the raw cursor before each transport and preserves the actual
   parent/witness/FiberTransform lineage.
3. If `k' != k`, the corresponding physical sibling is still stored. The
   Visit schedules each slot from its saved direct/atom prefix. R230's
   same-owner snapshot lemma establishes that every selected alias-equivalent
   physical sibling contributes its own raw fiber list. Thus `r` is copied by
   the WorkBound for `k'`; the claim does not require substituting `c` for `r`
   as the exact transport parent of the WorkBound for `k`.
4. For effect payloads, an equality witness remaps a negative-function demand
   root only when one of the witness endpoints is that exact root.
   `Work::Bound` applies its own raw-to-fresh witness to the same retained
   parent. The witness path remains explicit; endpoint equality does not
   collapse the two transform records.

This establishes a parent-preimage path for canonicalization-only fibers across
the selected same-owner physical prefix, conditional on the existing Visit
snapshot and successful merge/history premises. It does **not** prove that the
downstream consumer may use the copied descendant from `r` in place of a
descendant from `c`. Their destination RelationIds and dependency parents can
differ; `post_check_context` is relation-local, and a prior consumer may have
discharged `c` without discharging `r`. A theorem-level commuting or
non-independence argument must still justify exactly which of those descendants
the original computation-forwarding claim requires.

## Exact remaining seam and falsifier

The census narrows R71's first missing premise to a consumer law, not another
attach constructor:

> For an equality-only canonical child `c` of a physical raw parent `r`, when
> is a later WorkBound transport from `r` a valid source/native replacement for
> transporting `c` itself, including context residuals, scoped remaps, all
> dependency/FiberTransform records, rollback, and the independently licensed
> downstream consumer?

Two outcomes remain live. Prove the lineage square for the original consumer
semantics without identifying distinct RelationIds or deleting witnesses; or
derive a production-reachable accepted source in which the consumer needs the
canonical child's distinct residual/source payload and the raw transfer lacks
it. A manual row graph, equal endpoints, equal initial context, or finite
accepted-source corpus is not that proof/counterexample.

R71 therefore remains OPEN. R72 remains OPEN at its later source occurrence;
the exact R218 fixture has a complete ordinary solve trace but does not contain
the requested third-owner post-alias WorkBound. No code change is justified by
this source census. The unreviewed R235 formal-effect fix and the existing
playground evidence are unchanged; full `yu-solver` status also remains OPEN
because the exact long-running context test is unresolved.

## Evidence and dependencies

Read-only census command: `rg -n '\.attach\(' crates/yu-solver/src -g '*.rs'`.
It found the four production call sites above plus direct test-module fixtures.
Call-graph searches also covered `candidate_context_bound_for`,
`candidate_context_transport_witness`, `candidate_context_fresh_transport_scoped`,
`candidate_transfer_bound_origins`, and all call sites of the latter.

Direct source pins at freeze:

| Path | SHA-256 |
|---|---|
| `crates/yu-solver/src/candidate_context.rs` | `90665143f127394316b950d039fc498d460ac680df20b2387911a2fbdcaaeee1` |
| `crates/yu-solver/src/candidate_effect.rs` | `45324aaec3825b1bf5cb15811ce309b8ff2dc020d5882383c0ed33d9d0b779f8` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `5185481127cb619d66d49025c0a20ee7d829bc1e7a46072a05adecf4d22aa891` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_scheme.rs` | `135b72655d948d5035b21eaddce9fbeb0260c49bc3093e4bf2df73b03d88c4a1` |
| `crates/yu-solver/src/lib.rs` | `285a39449360b050d7689f9e52f400b821e651ec9ce300bd14a1a3d9a9ab8b64` |
| `notes/theory/2026-10-19-r71-raw-canonical-fiber-coverage.md` | `620947cece53ca60a7f8a2388a398f53850b835c79afd546bfdcfd10349a876e` |
| `notes/theory/2026-10-21-r218-r72-exact-source-execution.md` | `1d8202d64361b92f6f7fd6f21bc353fb882dede6dc4764bdc12d9312f8c2a22b` |
| `tasks/agent-loop/sprints/simple-sub-attach-lineage-20261021-r236.md` | `1bbd3de2fbf28530b17332fa4b1268f1c1be7b9d53bec603fb2083df22fb9f99` |

No tests, builds, candidate behavior changes or source executions were run for
this static proof step. No independent review or parent closure is claimed.
