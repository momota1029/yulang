# Cycle251: remembered-owner plan traces

Status: Draft finite native Plan adapter.

Lookup each actual Plan by demand identity and declaration id; require its exact
input-name list to match the remembered handle. Compile its packet Delta using
current frame snapshots, RoleBinder and identity targets. Update the frame before
compiling the next plan. Registered coverage is preserved, no handle is reseeded,
and successful preparation has one command per supplied plan. This replaces the
previous caller-supplied arbitrary Delta list with actual Plan packet production.

Define the trace's semantic obligations recursively using the independent
RolePacket.Holds at each computed witness and old snapshot, not Packet.Holds.
Prove equivalence to finite-executor Permitted, then projected existence of a
single assignment satisfying those obligations iff the final PublicModels.
Private-name separation and initial SafeOrder/Registered remain explicit.

The input list is still finite by construction, and the registry is supplied.
This does not generate source eligibility, establish semantic satisfiability,
add source Live/class effects or defaults, or prove source termination.
Unknown/translation readiness remains distinct from the semantic judgment.
