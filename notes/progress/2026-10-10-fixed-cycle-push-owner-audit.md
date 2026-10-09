# Fixed effect-cycle matching-PUSH owner audit

Date: 2026-10-10
Status: unreviewed source audit; fixed-witness owner result only
Baseline: successor `70d529702`; pinned Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Authority: user-selected effect-hygiene policy and the accepted callback cycle
Scope: determine whether the mapped `h <: E` cycle itself has a matching
`PUSH_i²` continuation that distinguishes the Oracle-suppressed POP counts

## Result

The fixed witness does **not** provide the proposed matching-PUSH discriminator.
The annotated callback return-effect row and its nested wildcard return-effect
are separate source owners:

1. `annotation/constraints.rs:442–447,608–626` constructs inner wildcard
   return-effect owner `h` without a Stack or output predicate.
2. `:450–470,657–691` separately constructs outer callback effect owner `t`
   and attachment `i`, yielding `Stack(t, PUSH_i[{io}])`. The written `[io]`
   and `[_]` rows have distinct source positions/constructor keys.
3. At the actual outer `f 1` comparison, inherited right `POP_i` cancels this
   single matching PUSH. Stack normalization and mixing are in
   `constraints/machine/propagate.rs:11–35` and `directed_weight.rs:16–39`.
4. The returned value carries the additional `NonSubtract` POP into the nested
   Function comparison. Its return-effect port generates `h <: Cf2` under
   right `POP_i²` (`propagate.rs:257–263`).
5. `Cf2 <: Ef2 <: E` is identity transport. The recursive suffix
   `E <: Cr <: Er <: E` has one left POP and identity edges; it raises the
   right POP count without introducing a PUSH.

Thus the existing PUSH belongs to the outer callback effect path and is
consumed there. It is neither a `PUSH_i²` predecessor entering `h` nor a
cancelling continuation leaving `E`. For the mapped effect suffix, identity
and POP transport cannot distinguish the representatives by cancellation.
The audited local row/projection checks also agree on active-family absence and
attachment-ID presence for right-POP-only variants. This does not establish
equality of complete public outputs.

## Exact remaining gap

`annotation/constraints.rs:132–153` connects both annotation interfaces to the
formal. This audit did not prove that every later structural replay, supplied
argument, generalization or output projection preserves separation between
outer owner `t` and inner owner `h`. It does not rule out another source
continuation or observer, and does not establish successor equivalence or
termination. The supplied callback cycle remains source-reachable; only the
specific matching-PUSH falsifier is absent from this fixed owner chain.

The separate successor obligation remains unchanged: endpoint plus POP-ID
presence is not a contextual coverage certificate across selected bound side,
filters/future checks, opposite replay, Function children, extrusion,
freshening, intrusion and rollback. The source-level next question is whether
the paired formal negative-view route can introduce an eligible same-`i` PUSH
predecessor into `h`; the successor-level next question is still an exact
admission simulation.

## Verification and limitations

Pinned-source inspection only; no execution, tests, build, Git mutation or
production edit. This is an unreviewed producer audit and does not close a
semantic or proof gate. The producer reported exceeding its two-process cap by
one lightweight source-read invocation; no expensive process or runtime probe
was used. General source incidence, public observation, guard justification,
successor correspondence, full Call and complete inference remain open.
