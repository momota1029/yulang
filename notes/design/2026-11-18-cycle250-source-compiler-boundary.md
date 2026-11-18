# Cycle250: exact remaining source compiler boundary

Status: proof-obligation map, not a successor boundary implementation.

Read against GeneralNominalRebasePacketView243, SourceDelta250,
StableCaptureStep250 and MultiOwnerCommands250 on 2026-11-18 UTC.

The old packet compiler uses one mapping for all eight fields: raw context,
ordinary constraints, projection origins, input site, capture binders, head,
children and outputs. Its variables function reads the legacy versioned capture
addresses. Merely passing identity or the old snapshot mapping into this compiler
does not manufacture the new stable owner capture addresses. The new step theorem
only constructs exact lower/upper bounds for actual occurrences on a computed
fresh witness. It does not replace all uses of legacy captures in the packet.

The next narrow implementation should introduce a packet environment with two
explicit roles: old context reads are substituted by the old block mapping;
current capture bounds use StableCapture250.bounds. Binder and schema expression
compilation must consume those bounds, with separate proofs for singleton and
multiple occurrences. Empty occurrences have bottom/top value equations, but the
Fits-to-all-original-intervals theorem currently requires nonempty occurrences.
Do not silently erase that premise or identify arbitrary empty capture semantics.
Output binders and child schemas need their actual allocation identities checked;
the current materialized handle seed is not asserted equal to legacy State.seed.

The source step adapter must then produce the actual post-install Delta and
prove its Holds equivalence on the *new* witness. SourceDelta250.compile_exact
currently interprets an already supplied legacy delta at one readback assignment,
and effect.Live is evaluated against its supplied fixed source core. It neither
regenerates alias classes/live requests nor establishes that source eligibility
implies FiniteInstallTrace250.Permitted. Passing checked_success proves only safe,
covered, coherent structural preparation, not satisfiability or source acceptance.

A fixed registered owner list gives fixed private slot targets, including traces
alternating owners. Registering new owners is distinct and increases this domain.
No theorem bounds how many registrations the actual source scheduler will make,
or term size after repeated snapshot substitution. Finite request input is not
Acc. These are the remaining I47 termination obligations, with I45 retained.

Existing QueryTransport245 already transports finite observable query expressions.
It does not justify keeping a literal private slot name public while changing its
value. Future promoted source outputs require actual query transport/ownership
invariants, rather than dropping the privateNames premise from public_models_iff.

No language choice or new source counterexample was established in this review.
