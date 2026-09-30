# SCC intrusion redesign charter

Status: Reviewed
Classification: research charter; replacement semantics remain unspecified
Scope: research direction for replacing Yulang3 F5 Function generalization and scheme architecture
Approved-by: none
Approved-at: none
Drafted-by: primary agent, following explicit user direction on 2026-09-29
Reviewed-by: architect, compiler_referee, spec_auditor
Reviewed-at: 2026-09-29
Supersedes: none
Research-gate disposition: withdraws the active-gate framing in the two 2026-09-29 intrusion drafts and the pure-F5 reference protocol
Implementation authority: none

## 1. User direction and correction

The user clarified on 2026-09-29 that the task is to **abolish the F5 portion**
of the type-inference design and proceed with a fresh SCC-intrusion design.
The prior research protocol incorrectly made exact F5 extrusion, Q/R,
per-member closed-scheme, ordering, and instantiation equivalence the pass
condition. That protocol is retained as a historical review record; it is no
longer the active gate.

For this research branch, F5's generalization and closed-scheme architecture
are legacy material to replace, not the semantic target. Do not require the new
design to preserve F5-specific Q/R shape, closed-scheme alpha-equivalence,
root-local numbering, or F5c resource/API contracts. Those may be recorded as
intentional differences or regression observations.

This direction does not authorize deleting code on `yulang3` or modifying
frozen `main`. The existing F5 branch remains intact as rollback and comparison
material until a replacement design is reviewed, approved, and implemented on
its own branch.

## 2. Semantic target

The semantic priority is soundness and principality before Oracle compatibility.
On 2026-09-30 the user clarified that Oracle inference-stage scheme formatting
and the phase at which a program is accepted are not successor requirements;
the compatibility target is the final acceptance capability for well-typed
programs. Meaningful source constraints must be retained when polarity-only
erasure would lose them. Use frozen Yulang2 `main` at commit `a58eefc3` as a
reference for existing behavior, but do not copy its implementation
mechanically. In particular, the audited Yulang2
`extrude_pos` / `extrude_neg` lower existing variable levels in place during
bound insertion; that code does not allocate the fresh boundary representatives
described in the 2026-09-29 sketch. The redesigned operation must be defined
from its own semantics and checked against observable Oracle behavior.

The Authoritative F4 SCC design remains in force only within its declared
Integer/resolved-Name scope. Its dependency-sink-first scheduling, open live
internal uses, and all-member visibility barrier before incoming use are
available as established infrastructure where applicable; F4 does not define
Function schemes, recursive Function bounds, or effect generalization. Its
publication wording does not require every member slot to be written in one
indivisible operation.

## 3. Research goal

Define a new type-inference architecture in which a definition SCC can be
generalized and instantiated while retaining graph sharing through an
intrusion/parent relation. The new design must state its own semantic objects
and observations before choosing data structures:

- what type constraints and polarized bound edges mean;
- which identities cross a generalization boundary and which remain local;
- how outer/non-generic variables remain shared without being captured;
- how recursive SCC sharing and productive guarded recursion are represented;
- how each incoming use receives independent substitutions while internal
  SCC uses remain open;
- when the generalized component freezes, publishes, and becomes visible;
- how failure avoids partial publication;
- which source forms and effects are in the first supported envelope.

Parent identity, polarity, boundary identity, recursive binder identity, and
handler-hygiene evidence must not be conflated without a proof. State the
soundness and principality theorem precisely, including the graph class,
boundary assumptions, and supported-input envelope. Effect-handler hygiene
remains a later gate after pure type/SCC behavior is characterized.

## 4. Research procedure

### Gate A — Oracle behavior ledger

For the smallest pure Function witnesses, record Yulang2 observable schemes,
constraints/use behavior, and recursive bounds. Fixtures include identity,
constant, shared diamond, nested polarity inversion, an enclosing non-generic
endpoint, guarded and unguarded cycles, mutually recursive definitions, and
two independent uses. Record which facts are observations and which are
inferences about the old implementation.

### Gate B — New abstract semantics

Specify an immutable finite polarized bound graph, levels/boundaries,
enclosing environment, SCC roots and uses, and the parent relation. Define
boundary closure and parent allocation independently of F5's closed-scheme
construction. State the principal-solution/soundness property and the
capture-avoidance rule for outer variables.

### Gate C — Intrusion characterization

Work the Gate A fixtures by hand or with an independent small model. Compare
the new semantics to Oracle observations, not to F5's internal representation.
For each incoming use, check fresh identity isolation and later constraints;
for internal uses, check live-root sharing. Add counterexamples before scaling
the fixture family. A finite set is characterization evidence, not by itself a
general soundness or principality proof. Before Gate D, prove the stated
theorem for the intended graph class, or narrow the supported envelope and
prove the theorem for that class. An independent semantic and specification
review must check the theorem, proof, and exact envelope before Gate D. A
failed or inconclusive proof review returns to Gate B/C; fixture agreement
alone cannot advance to representation selection.

### Gate D — Representation and resource design

Only after semantics are coherent, choose whether the generalized component
remains an SCC graph, how member roots project, and how use-site substitution
overlays work. Derive complexity from explicit graph dimensions and the
required observable output. Do not assume compact output merely because the
internal graph is shared.

### Gate E — Approval and implementation

Produce a narrow successor design that names the F5 sections/lifecycle being
superseded, intended Oracle behavior, compatibility deltas, rollback
conditions, and supported-input limits. Each limit must name the measured or
structural dimension, deterministic rejection point, and failure behavior;
inputs must not be silently truncated or partially published. Complete
independent M3 semantic, specification, and material performance review of
the successor design, then obtain explicit user approval before
implementation. Implement only on the redesign branch; keep the existing F5
branch available until a coherent replacement gate passes.

## 5. Stop conditions

Return to design if the parent relation captures an enclosing variable,
collapses meaningful polarity, merges independent uses, loses a recursive
bound, reduces final acceptance of well-typed programs in the supported
envelope, or fails the soundness/principality proof for its claimed envelope.
Differences in inference-stage formatting or acceptance phase are permitted
under the user's 2026-09-30 decision. Any other deliberate compatibility
difference needs a concrete conflict and an explicit decision rather than
being called equivalent.

Do not run the consumed F5c guarded-cycle captures. Any future resource
measurement needs a new design gate and budget based on the new representation.

## 6. Current boundary

This is a Reviewed research charter, not an implementation plan. It
records the user's direction to remove F5 as the target but does not yet define
the replacement semantics. No compiler code, F5 tests, public scheme APIs, or
frozen `main` files are authorized for deletion or modification by this
research document.
