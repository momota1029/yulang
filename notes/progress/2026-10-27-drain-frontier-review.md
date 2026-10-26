# Independent review: first boundary after the active drain cut

Reviewer: `/root`, not the producer `/root/principality`.
Verdict: **PASS for the initialized polling invariant and first same-owner
post-active-cut boundary. Full native NQ and inference termination remain OPEN.**

## Frozen targets

| Target | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalDrainFrontier.lean` | `ec7d4ab463858b73cd09295588833fa095a749c529d40a03cd4f5b8406fb9682` |
| `notes/theory/2026-10-27-original-drain-frontier.md` | `8a85547d3bf0823f288d2fd968ed25842002be3f84ce30fa791bc370b101df5f` |

I read the complete 277-line module and paired note, the imported stage and
first-boundary definitions, NQ §§3–5.2, and the actual initialization,
Transport and Dispatch owners in `candidate_context.rs` and `lib.rs`.
The prior independent Stage/First review remains a separate receipt; it did
not certify this new application.

## Decisive application repair

The earlier initialization trap is real: `.begin` creates an empty idle
Transport frame before its seed enqueue. This module never selects NQ's
post-tau frontier by minimizing a prefix from global initialization.

Instead it first derives, for every frame of the actual computed initialized
event prefix:

```lean
frame.poll = .entry ∨
  (frame.stage = .transport ∧ frame.core.current = none)
```

`update_returns_entry` uses the existing full-stage entry-preservation proof
when the input is entry. Otherwise the invariant selects the actual
Transport/current-none branch, which resets entry for every queue-pop outcome.
`apply_polls` covers every existing event constructor. In particular, settle
uses its real guard, settlement return uses the previous invariant and
settling poll, and prepare cannot change the relevant fields.

At the supplied active top frame, a nonempty current slot excludes the idle
alternative. `initialized_active_entry_only` derives the same-owner property
using initialized stack validity and `same_top_is_saved_frame`; no uniqueness
law or poll certificate is a caller input. It retains both birth and index.

The final construction applies `finite_first_boundary` to the candidate
suffix **starting at tau**. The active current also proves tau is not already
an empty boundary, so the returned prefix is nonempty. Its end has the same
owner, actual top slot, Transport/current-none/empty queue, a derived entry
poll and the exact computed successful settle update. Thus the initialization
cut cannot satisfy this conclusion as the chosen prefix end.

The Dispatch corollary derives nonempty current from the initialized shape
invariant and actual Dispatch-stage readback. NQ's stated event-1229 cut is
immediately before `dispatch_live_item`; the native Dispatch arm reads its
required current item at that point. This is the correct control-shape
application. The theorem still requires extraction of that native event into
the supplied model prefix, frame and stage readback.

## Scope and unresolved owners

The candidate suffix and final boundary are hypotheses for analyzing a
proposed finite normal continuation. The result does not prove that either
exists, that a drain finishes, or that an arbitrary projected event list is
an extracted native execution.

The strict-before property excludes only this owner's prior boundary and
settlement. Other owners and nested frames remain allowed. Their absence
where required by NQ's ordinary route, generation/representative stability,
the same physical bound/Replay history and successor production are separate
native correspondence obligations. A current-none starting cut also requires
its authentic program-counter supplier; the invariant alone deliberately
permits settling/returned idle frames.

No original source constructor or Effect work is removed, and no finite
identity bound or global solver fuel is introduced. All original whole-language
roots remain open. No blocking issue was found against the packet's stated
conditional local-control claim.

## Independent checker and axiom evidence

The parent built the exact frozen source, six jobs, before review checks.
I then used two of four allocated independent checker invocations, both with
pinned Lean 4.35.0, `timeout 120` and no `-o`:

| Invocation | Bound | Outcome |
| --- | --- | --- |
| Direct frozen source | `-j1 -M1024` | Exit 0; empty diagnostics |
| Complete imported-origin audit | `-j1 -M2048` | Exit 0; all 33 declarations and 26 theorem constants |

The census requires all 16 authored roots to be theorem constants and audits
the seven originating definitions and all ten generated theorem constants
as well. All 33 types and transitive axiom sets are unelided, with matching
begin/end records. There is no project axiom, proof hole, bypass or dependency
outside `propext`, `Classical.choice`, and `Quot.sound`.

The authored axiom groups exactly match the producer's named inventory:
4 with none, 1 with `propext`, 8 with `propext`/`Quot.sound`, and 3 with all
three standard axioms. No failed independent invocation occurred.

| Evidence | SHA-256 |
| --- | --- |
| `/tmp/yulang-drain-frontier-root-review/direct-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/tmp/yulang-drain-frontier-root-review/Audit.lean` | `b5afb170cf1db35c49fbf28cda786d2730db4bdce575a2a882725b45fee53bce` |
| `/tmp/yulang-drain-frontier-root-review/audit-02.log` | `ee2c5fda06a896cfaef9feb1a3272a168f5dc3b3b8b590fad81b03d42ece1071` |

Both processes ended. No producer source/note edit was needed. Integration
and publication are root-owned subsequent steps.
