# Frozen Oracle State frames: historical construction and runtime route

Date: 2026-10-07
Yulang3 baseline: `c6067ef51ba2c9ca6018ea282152e6d52f7f7af7`
Frozen Oracle: `/tmp/yulang2-oracle-rebuild`, `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Status: bounded historical mechanism characterization; not successor authority
Gate relevance: STATE_ID, STATE_RW, STATE_RESUME, REF_WORLD and CALL_TYPE's captured-environment frame

## Mechanism recovered

The frozen compiler has a concrete local-State lowering and runtime-evidence
route. `crates/infer/src/lowering/expr/block_local.rs:782–841,933–957`
rewrites a local variable into an initialized binding, a reference
constructor, and a State `run` around the remaining block suffix.
`block_local.rs:1152–1169` registers the synthetic State effect family and
optional get/set operation identities. The specialization evidence path
(`crates/specialize/src/specialize2/runtime_evidence.rs:132–159`) serializes
those registrations as `CompilerLocalVar` handlers with `SnapshotFork`
continuation metadata.

The evidence VM connects registrations to concrete plans:

- `crates/evidence-vm/src/lib.rs:2474–2496,2747–2773` joins the effect
  certificate to get/set handler plans and reconstructs the state parameter
  from the handler's nested Lambda shape. A missing or conflicting parameter
  prevents that plan.
- `crates/evidence-vm/src/runtime.rs:22595–22614` installs a dynamic frame
  and state-scope identity.
- `runtime.rs:22659–22678` restores a snapshot into a fresh frame while
  retaining the snapshot's state scope and captured state.
- `runtime.rs:22873–22923` finds the latest matching live frame; get reads
  its current payload, set replaces that payload and updates the handler
  environment before continuing.
- `runtime.rs:16043–16095` restores frames around continuation processing,
  removes them afterwards, and snapshots updated frames if a resumptive
  request escapes again.

This yields one useful identity/value distinction. Under successful plan and
frame installation, restoring a captured snapshot
`(state definition d, payload v0, scope q)`, writing `v1`, and then restoring
the original snapshot again yields a new dynamic frame with `(d,v0,q)`. The
static definition and scope survive, while the current payload differs between
branches. This is a control-flow consequence of those historical constructors,
not a successor transition theorem or executable probe.

The separate mono-runtime path in
`crates/mono-runtime/src/runtime/eval.rs:84–94` saves the lexical environment
before callee evaluation and later evaluates the argument through it;
`crates/mono-runtime/src/lib.rs:260–263` stores that environment as
`HashMap<DefId,Value>`. `crates/mono-runtime/src/runtime/thunk.rs:158–177`
composes request continuations. These retain lexical lookup/control flow, but
do not certify a captured provider's referenced values or latent dependencies
at a returned callee world.

## Successor boundary

The construction is relevant historical evidence for which mechanisms a
successor's source and runtime pipeline may need to account for: static
operation identity, dynamic activation/frame identity, current State payload,
continuation snapshotting and repeated resumes. Oracle names such as
`SnapshotFork`, its State semantics, generated identities, and runtime branch
equations are not adopted as Yulang3 rules.

In particular, none of these artifacts supplies the current theorem's required
joint fact: original captured-binding/provider/dependency adequacy at the
actual returned `C1`, extended compatibly with every retained `CalRet`
witness, plus actual-provider whole-carrier compatibility. They contain no
current original `xi=(nu,K,D)` interpretation or typed `EnvStore/JointWF`
preservation. The governing architecture records static slot origin and pure
restart, but the exact replacement/restart successor equation remains absent;
ordinary Bind only forwards an already obtained configuration. Therefore
STATE_RW, REF_WORLD and the Name/Name CI-ArgFrame leaf remain open.

The recovered route is distinct from ordinary Call attribution archaeology,
which found no new pre-query owner/view-kernel producer. It does not introduce
an `OriginalAssocType` inhabitant and does not change P2, P3, licensing,
profile or admission status. The Oracle and its optimized evidence VM are one
historical implementation, not independent semantic authorities.

## Limits

This pass inspected source constructors and consumers at the recorded frozen
Oracle revision and compared the listed dependencies against their pins. It
did not execute the Oracle, establish all lowering paths, prove the historical
solver sound, demonstrate source acceptance, or establish correspondence to
Yulang3. Aliases, escaped providers, every response/resumption history,
payload typing preservation and all current-world admissions remain outside
the result. No gate status or semantic clause changes.
