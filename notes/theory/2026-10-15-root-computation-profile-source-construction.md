# Root computation profiles: source construction and the body-pause case

Date: 2026-10-15
Status: independently reviewed finite source specialization and obstruction
to lexical-only unconditional deletion. Native enforcement/runtime closure and
the original whole-source hygiene/soundness/principality parent remain OPEN.
Compiler baseline: `af3ed318b4c022e6baa211134ef89d0f3810eecb`.
Authority: current receiver-relative clarification and sources below.
Lease: this new note only; no implementation or old-proof edits.

## 1. Fixed source, scope and meaning of the result

The primary reports successful native admission of the sixth control in
`crates/yu-solver/tests/candidate_computation_laziness.rs`:

```yu
act io:
    our tick: int -> int
act pause:
    our stop: int -> int
my relay (thunk:[io] int) = {
    my ignored = pause::stop 0;
    catch thunk { io::tick(p), _ -> 1, v -> v }
}
my keep (thunk:[pause] int) = catch relay thunk {
    pause::stop(p), k -> k 0,
    v -> v
}
my answer:[io, pause] int = keep (io::tick 1)
```

Admission is constructor evidence, not execution or this proof. No run occurred
in this packet. The earlier candidate with pause *inside the argument* had an
unproved pre-query receipt and remains retracted as a counterexample. Here
pause precedes relay's direct formal Name lookup, providing that actual read
after resumption. The corrected reports remain historical dependencies.

Fix original single-parameter Lambdas L_s/L_r, original formals t_s/t_r,
outer annotations a_s/a_r and their distinct source row positions p_s/p_r.
Their known source interfaces are Computation(E_s,Int), Computation(E_r,Int).
Resolved families P=pause and I=io retain their original declarations.
Use one xi=(nu,K,D) throughout. Static endpoint references e_s/e_r denote the
corresponding registered AE endpoints, not executing occurrences. Original
v_t Value rows are retained with their Int constraints, not replaced by leaves.
Concretely t_s/t_r mean the HirParameterIds retained by those original single
header constructors; e_s/e_r are entry_effect of their own FormalRegistrationInput,
joined through that registration's actual parameter/recipe position. Numeric
IDs are not invented here. native_root is a Value term, not the received typed
carrier packet V_s/V_r or a runtime receiver identity.

The finite conclusion concerns these source constructors, their original
profile binders and the displayed legal raw-resumption interaction. It does
not restrict the original parent to this fragment or certify complete native
Call, source acceptance, solver substitution, all higher-order profiles or VM
execution. It tests the stronger proposed rule that a flat unconditional io
deletion follows from annotated Name + same source Lambda + total discard arm.

## 2. RootCompSchema is derived from the selected source contract

Authority: [receiver-relative decision](../design/2026-10-15-callback-identity-forwarding.md),
“Direct clarification: protection relative to the receiving boundary”; and
[annotation integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1,1.1. The first protects associated argument effects inside their receiving
boundary; the second adds local permission for the written concrete family
and admits additional effects. The primary's architect adjudication confirms
these apply to the explicitly exposed computation root, including known io.
No extra policy choice is introduced by the specialization below.

HIR supplies original formal/Lambda, annotation.position and row.position,
resolved concrete P and Computation role; the role is fixed before body use.
For this signature the applicable effect path is uniquely RootComp: it is
the computation carried by the parameter, not every nested latent position.

```text
OriginalFormal(L_s,t_s,a_s); a_s = outer [P]Int at source position p_s
Role(t_s)=Computation(E_s,Int); EntryAE(t_s)=e_s
------------------------------------------------------------ RootCompSchema
ProtectSchema(L_s,t_s,a_s,p_s,RootComp;xi)
PermitSchema (L_s,t_s,a_s,p_s,RootComp,{P};xi)
```

This is a source-schema constructor, not an arbitrary χ premise. ProtectSchema
marks the RootComp **position**, not “all effects except P”: protection and
permission are separate coordinates. At that position every associated incoming
effect is protected by the default; only a compatible P operation is expressly
admitted locally by this annotation. I is protected too, even though concrete
I is already known in the incoming argument. No symbolic effect variable must
first be exposed to trigger the default. E_s remains open; no E_s⊆{P} cap or
new effect contribution follows. The same rule gives relay RootComp protection
and its separate local {I} permission.

**Justification.** The role and explicit outer annotation identify the one
received computation position. Applying the selected default there yields
ProtectSchema. Applying the negative-position concrete annotation policy yields
PermitSchema with precisely P. Each premise is an original source-construction
operand, so neither a solved row nor successful pending Function comparison
creates the schema. These two policy instances determine this finite profile;
no arbitrary nested paths or concrete grants are chosen. This derives a known
root specialization, not the general raw-profile inference algorithm.

The schema binder (L_s,t_s,a_s,p_s) is static provenance. It is not itself an
active receiver, fresh boundary or grant. The rule is scoped to an explicitly
exposed Computation root; it does not require nonempty profiles for ordinary
Value id arguments or paint a provider's public lower output.

## 3. Actual receiving entry instantiates the schema on the received view

Use the selected whole-argument reification/retained-entry schedule and
[typed-boundary](../design/2026-10-02-typed-boundary-realization-draft.md) §6's
boundary introduction, now with the profile constructed in §2. At actual keep
entry s, let T_0 be its actual whole inert argument carrier and χ_0 its incoming
valid evidence packet (which need not already contain any desired protection).

```text
RootCompSchema_s; actual EntryRetained(keep,s,T_0,t_s) under xi
---------------------------------------------------------------- ReceiveComp
fresh b_s=(original receiver s, original slot t_s, Γ_s, endpoints)
Γ_s: Protect(RootComp); Admit(RootComp)={P}
received view V_s with χ_s = Id_*χ_0 ∪ {(RootComp,b_s)}
Receive(s,t_s,V_s,Id)
```

No entry Force occurs. Original incoming profiles remain separate source-tagged
inputs under the same xi; the received view is distinct from an unreceived
provider/caller alias. Its introduction supplies the new χ incidence, rather
than assuming χ_0 contains b_s or modifying provider lower facts. Freshness
comes from this actual source boundary entry, not the static Lambda ID.
For another invocation s2 the same schema instantiates a different b_s2.

This is the existing boundary-introduction operation specialized to the unique
known root. It changes no execution scheduling and grants no handling by itself.
Native FormalEntry currently has the required static operands but does not
implement this actual-entry/view operation. That compiler correspondence is
not claimed by the source construction.

## 4. Generate the exact Name/S-Delay/Argument map for relay thunk

The actual argument expression in keep is exactly the resolved computation
Name t_s. There is no prefix, projection, adapter, unrelated field or effect
producer inside that argument. Source synthesis therefore fixes:

```text
Gamma(t_s)=Computation(E_s,Int)
c_N = eliminate_RootComp(name t_s) : Comp(E_s,Int)
D_N = Delay(X[c_N], captured original binding t_s↦V_s)
```

The root correspondence is generated by these constructors, before execution:

| Owning constructor | Generated source positions/correspondence |
| --- | --- |
| Resolved Name t_s | Its read slot refers to the original binding's whole Computation(E_s,Int) interface; RootComp maps to that read's RootComp by identity. |
| Designated consumer c_N | Its computation effect port is precisely that Name's RootComp consumption port. It introduces no second force, handler, contract or independent effect source. |
| S-Delay at this actual argument | Stores the whole c_N interface under the carrier's latent computation slot; that designated effect port is the carrier's RootComp. The captured binding dependency is the original t_s↦V_s. |
| Relay Entry-Retained | Binds that same whole inert carrier's Computation(E_s,Int) root to t_r's received RootComp, using the actual Argument/AE correspondence. It does not execute D_N. |

These are the concrete [source-interface constructors](2026-10-08-call-source-interface-construction.md)
§5, “Registration, Name and capture”, “Reify/Delay” and “Producer and entry”.
The designated-consumer and source-role rules are in
[core elaboration](../design/2026-10-02-typed-computation-core-elaboration.md)
§§2–3,6. Here the source derivation itself names each corresponding port; no
port is selected from equal effect rows. S-Delay stores the latent port and
its dependency—it does not run the Name or allocate a receipt during reification.

**Specific-map proof.** Name's registered source interface is Comp(E_s,Int),
so its original read slot includes that exact RootComp port. Normalization
selects the designated consumer of that port, rather than Return of an opaque
computation value: this is the Computation source tag, not a shape guess.
Thus c_N has this sole designated computation port. S-Delay's carrier interface
contains the entire c_N under its latent edge; opening that carrier's known
outer computation selects exactly that edge. Relay's retained binding imports
the same carrier root, with no adaptation. Composing these three original
port inclusions therefore maps V_s.RootComp to D_N.RootComp and then to the
received relay root. This is a generated map, not just an assumed M satisfying
the abstract transport law. Symbolic endpoints and all dependent source tags
are carried by the identical source slots throughout.

The rule does not copy arbitrary captured private fields onto a public view.
Its edge exists because this exact code consumes the **whole named computation**
at its designated root. A delay that ignores t_s, returns it as inert data,
projects another component, or executes unrelated code does not have this same
source derivation. General cases require their own constructor maps; no source
is rejected by this bounded characterization.

Apply the already-reviewed indexed-image transport to this generated map.
At actual relay entry r, instantiate its own root schema and bind the carrier:

```text
χ_DN(RootComp,b_s)                 // generated map from χ_s, not arbitrary χ
fresh b_r=(r,t_r,Γ_r,endpoints); Γ_r admits I at RootComp
χ_r = M_Argument*χ_DN ∪ {(RootComp,b_r)}
Receive(r,t_r,V_r,Id)
```

Therefore χ_r(RootComp,b_s) and χ_r(RootComp,b_r) both hold with original
receivers s and r. P permission stays local to s; I permission stays local to r.
No family equality merges these profile instances or selects their witnesses
independently. All K,D and original provider/attachment coordinates remain
under the same assignment by the common packet transport theorem.

## 5. Body pause, fresh owner and the matching post-resume query

Keep s stays active while its own pause-Catch arm invokes k. Relay first emits
the direct body q_P, before H_io or its thunk consumer executes. The retained
argument's RootComp view is not executing at that emission. Merely storing its
profile cannot protect this unrelated direct request; this is the established
direct-body versus received-effect distinction. Keep's pause handler can select
q_P. By selection relay r ends, keep s remains live, and the selected pause
handler is removed. The unfinished relay Bind suffix contains the **unexecuted**
Catch and Name t_r; it retains their lexical binding V_r.

The [source-owner theorem](../design/2026-10-02-typed-source-owner-realization.md)
§§2–4 now applies. Owner(relay,r,...) enters fresh r' because r expired. It
does not replay entry, so it introduces no b_r' and never changes b_r.receiver.
The saved Bind suffix installs a new H_io' under r', then actually loads t_r.
Let V_n be that read's exact output packet, allowing a distinct view occurrence.

```text
χ_n = Id_*χ_r                         // actual immutable binding read
Receive(r', t_r-read-slot, V_n, Id)    // actual load: source-owner:157–163
Execute_RootComp(V_n)
Observe(q_I,V_n,RootComp,o_n)          // same consumer/view, structural projection
```

The q_I exposure occurs when this consumer executes the delayed Name t_s and
its original io computation. Whole-argument reification has run none of it
earlier. The observer is the actual executing V_n RootComp delimiter; the
receipt names that **same** V_n/position. No automatic handler-environment load,
old observation reuse or pointer-equality substitution supplies this join.
The generated χ_n includes b_s, so these exact witnesses establish
Path(q_I,r',b_s,RootComp). This discharges both formerly missing premises of
the body-pause report within the finite source construction.

At the actual H_io' candidate:

```text
Active(s)=true; Active(r)=false; owner(H_io')=r'
Inc(q_I,H_io',b_s)=true
Inc(q_I,H_io',b_r)=false
Protected=true; Grant=false; Visible=false
```

b_s grants only P and is not local to r'; b_r's original local I grant has
expired with r. New receipt and handler creation do not create a new annotation
boundary. Hence q_I forwards outside relay. Keep's selected pause handler is
absent and no remaining io handler consumes it in this source. The computation
can expose io outward. No numeric result or native runtime execution is claimed.

## 6. Consequence for unconditional flat deletion and actual handoff

The lexical-only filter recognizes the same direct formal, source Lambda,
exact io operation, total first io arm and discarded continuation in the new
H_io' code. Those static facts do not prove the old annotation's actual
receiver is r'. Removing io permanently from that Catch's exported interface
loses the admissible q_I future derived above. Relay's other direct pause effect
still propagates, but keep's outer raw-k row already inherits the io-filtered
relay result; retaining that nearest “full E_S” cannot reconstruct inner deletion.

Thus the specified *unconditional flat deletion from source-Lambda identity*
is insufficient under the selected source semantics and generated root profile.
A consumer that establishes the actual same receiver/contract and preserves
the complete future dependency is not refuted. Current native Catch retains
the conservative scrutinee inclusion and has no demonstrated runtime bug here.

The full source Call already owns original provider/world, ordered pending
suffix and complete future interfaces, with receipt not replayed. The next
implementation owner must preserve those original coordinates through any
conditional residual operation. Keep the existing conservative route until
that actual constructor/consumer correspondence is established; do not reject
raw resumptions or add a globally clearing guard. RootCompSchema/ReceiveComp
are the finite source specialization to implement, not proof that static AE
rows or FreshUse IDs denote active receiver instances.

Checks: bounded source reads, generated-port derivation and dependency hashing;
no tests/builds/execution/network/Git/delegation. The sixth-test admission is
primary verification evidence, not work run by this leaf. Requested Sol/high,
runtime model/effort unknown; one <=20-minute leaf. Only this leased note changed.
Independent compiler-referee review of frozen producer SHA-256
`59be3cec1ffca4be1d5d38a08fa46a10883867df0e71f3742e69273d758f6745`
found no blocking or major finding. It confirmed the finite source schema,
generated Name/Delay/Argument correspondence, actual post-resume matching
receipt/observation and expiry distinction. This closes those finite missing
premises and establishes §6's obstruction to lexical-only unconditional
deletion. It establishes no current native bug or general runtime theorem.
Primary checks matched all ten dependency hashes and six linked paths; no
tests or executions were repeated for this record update.

Commit packet: exact leased path only; compiler baseline above; dependency hashes
below. Suggested checkpoint:
`research: construct received computation root profiles and analyze body-pause future`.
Primary adjudication: apply this finite source construction to the flat-filter
feasibility gate. The lexical-only unconditional mechanism is refuted for the
displayed source; the actual-instance conditional residual theorem is not.
Original whole-source and native implementation/runtime gates remain OPEN.
Source Comp-entry/profile instantiation and complete-future Catch transport
remain the implementation owners. Shared records are synchronized by the primary.

Read dependency SHA-256 values:

```text
callback-identity-forwarding.md 4f4502536cc63185c5eb973f6b9dec6b4fd24a9d39ab69eccf3e980222e2ca4a
annotation-effect-hygiene-integration.md 4a98b5136a9d0d1bdddf135727c5e8779b579bf3c0b76d0524d01c951df34fd4
typed-boundary-realization-draft.md 1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb
typed-source-owner-realization.md 5cbd8110736ee4d43e0c65460fa9ecf700228bfdbe9fbaa7642ea0302d86f1aa
typed-computation-core-elaboration.md 0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e
call-source-interface-construction.md 278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98
computation-formal-permission-construction.md 7766aff08cedde1ebc796b8927cd1d44f459df72a632e0c0d35d4bfcd28d335e
candidate_computation_laziness.rs df5d567dca1b8d0569e1afacfda0992baf11b848205a0c7c38c449609270e5b2
candidate_source.rs 90db34173d366ed826b34492da0fb2f1c5422b1b41e43fcda14892ec8415e7ab
candidate_effect.rs deee5a0892b02bc9ee23a1f2a35c76175094c558ed7dfb2cf55a7e115ac54225
```
