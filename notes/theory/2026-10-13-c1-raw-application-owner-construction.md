# c1 raw Application: conditional skeleton and introduction frontier

Date: 2026-10-13
Status: frozen independently reviewed bounded characterization; conditional Draft skeleton; no implementation authority
Reviewed-by: independent compiler_referee; PASS for the stated bounded characterization, no findings
Baseline: `beceb0bc91b35e84b4f62b353fc6c2abf18e0414`, branch `research/simple-sub-intrusion`
Exclusive lease: this file; constructive proof leaf, no delegation
Budget: static rule/source substitution; zero builds, tests, probes or measurements
Authority/behavior: existing decisions; no semantic adoption or compiler change

## 1. Frozen statement and outcome

Use exactly

```text
let rec f = lambda x.
  let g = lambda y. (lambda z. y) (f y)
  in {a = succ (g 0), b = g true}
in f
```

The actual source tree retains all five Apps and all binders:

```text
LetRec(f,
  Lambda(x,
    Let(g,
      Lambda(y,
        App_c2(Lambda(z,Name(y)),App_c1(Name(f),Name(y)))),
      Record(a=App_c4(Name(succ),App_c3(Name(g),Int(0))),
             b=App_c5(Name(g),Name(true))))),
  Name(f))
```

The required conclusion is an authentic raw Application at c1 with its whole
dependent Call clause and actual source/native operand interpretation, followed
by lawful whole actions through g publication and both independent uses. For
every finite lawful joint client derivation, retain one active monomorphic f
root, actual scopes/providers/worlds, receiver/receipt, complete result/future,
attachments, witnesses and residual lineages, and the actual extrusion event
`(C,B,+,1),(D,R,-,1)` with approved `C=B,D=R`.

Hypotheses are the selected local source laws at their stated scopes, including
Source-Generalize L1–L5, LocalSelfRec, occurrence qualification, and the fixed
source/native history. These laws condition genuine derivations; they do not
assert this source is admitted, solvable, principal, or supplied with an
unspecified local law. No exact apply/step `Role_0`/formal seed is reused:
f is a recursive definition root. No artificial C/D Desc, independent marginal
witness, early solving requirement, new registration, fresh f, source
restriction or alternative equality meaning is introduced.

**Outcome:** the Draft §6 row computes a conditional result/consumer skeleton.
It does not establish the accepted raw Application introduction. The first
unsupplied App-specific origin is exposed in §4. No complete dependent
telescope exists in this derivation on which to apply the requested commuting
whole-map test. This is a bounded obstruction, not rejection, impossibility,
source-qualified refutation, or original theorem closure.

## 2. Exact authority, dependencies and scopes

| Actual source | Governing scope used |
| --- | --- |
| [Active-root witness](2026-10-13-active-root-call-source-construction.md) §§1,3,5 | Fixed source, scopes and native/current-owner history |
| [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md) §§2–4,6,9 | Draft conditional derivation core and generic Application row; no implementation authority |
| [Charter](../design/2026-09-29-scc-intrusion-redesign-charter.md) §§13–21 | Typed transport, whole-argument inertia, forwarding, parameter roles and joint packet scope |
| [LocalSelfRec](../design/2026-10-10-local-self-recursive-binding.md), Selected behavior and Proposed seam | Nested helper references the same active open f root; installation follows initializer actions |
| [Source-Generalize definition](../design/2026-10-08-source-generalize-definition.md) §§2–3; [proof](2026-10-08-source-generalize-definition-and-proof.md) §2, §§3.1,3.3,4,5.1–5.2 | Local rules/records and Build/publication/allocation consume authentic source clauses |
| [Call-input](2026-10-07-call-input-construction-proof.md) §§3–3.4 | Static registered binding/Name/capture, formation origins, Code-Call and complete suffix |
| [Original Call](../design/2026-10-07-original-call-formation-definition.md) §§1–4 | OSig/OC consume an actual emitted Gen-Call-0; the apply/step generator is scoped |
| [IF definition](../design/2026-10-08-call-source-interface-definition.md) §§2–4; [construction](2026-10-08-call-source-interface-construction.md) §§2,3.2,4–6 | Typed clause insertion/reference and whole substitutions; complete receiver/result/future retained |
| [Occurrence decision](../design/2026-10-12-intrusion-value-type-association.md), Approved qualification and Definition-root origin | Actual G/F event and signed pairs; no preservation/action theorem supplied |
| [Parent/copy](../design/2026-10-10-parent-copy-scc-intrusion.md), Selected operation and Definition-root ownership; [copied rows](../design/2026-10-12-value-reference-copied-row-ownership.md), Decision | Equality affects later solving/use; copying creates no Value-reference incidence |
| [Inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md) §§1–5 | Native generation/accumulation/propagation/extrusion/generalization and natural inference |

Keep the original source order:

```text
f registration; sigma_x before f challenge h_x
  h_x: receipt, Force_x, Return/rebind x
    g formation/publication p_g(h_x)
      sigma_y before g challenge h_y
        h_y: receipt, Force_y, Return/rebind y
          c2 obtains Lambda z capturing that same rebound y
          whole c2 argument is Delay(code(c1))
          sigma_z before wrapper challenge h_z
            h_z: wrapper receipt; Force_z runs c1
              c1: same f; inert Delay(Return(same y));
                  actual f receiver/entry/body/return/future suffix
            c1 result rebinds z; wrapper body returns same y
    after g publication: c3; c4's succ consumer; c5; record result
f installation/publication; final Name f
```

These are latent source regions, not an execution/termination assumption.
c1 runs under the wrapper's argument Force, not its Name(y) body. Native
numeric levels do not supply the dependent scopes.

## 3. Conditional generic Application substitution

Charter §21 fixes unannotated x/y/z to Value entry. Source-Generalize §3.1
supplies an ordinary flexible parameter endpoint at its genuine source
typing scope. The complete Desc record still requires its validating
component and telescope from authentic registration; numeric levels do not
supply either. Call y's endpoint B. LocalSelfRec fixes f's active native root
o, without completing its recursive membership or full declared interface.

Within typed-core §6's stated premise of known lexical/declaration interfaces,
put `Gamma(f)=Value(A_o)`, `Gamma(y)=Value(B)`. Actual resolution/capture
selects the same f and rebound y. When genuine declared binding and original
result ports are supplied, Call-input Name/Data-Name/Code-Result has shape

```text
d_f = name f    n_f = result(d_f)    Result(I_f)=Comp(empty,A_o)
d_y = name y    n_y = result(d_y)    Result(I_y)=Comp(empty,B)
```

No Function membership or formal seed follows. Capture restricts/imports
the same dependency-closed f reference without freshening o.

The Draft generic Application row substituted at c1 is exactly

```text
I_1 = Computation(E_1,A_1)
d_1 = reify(call(n_f,n_y))
n_1 = eliminate_p1(d_1)

X[call(n_f,n_y)] = Return(lookup f) >>= lambda actual_f.
                    let t = Delay(Return(lookup y),lexical references) in
                    ExecuteCallable(actual_f,t)
```

E_1/A_1 are symbolic complete-Call endpoints constrained by the existing
invocation relation. The callee constraint must identify a Function at n_f's
result; the argument constraint must relate the whole Name/Return carrier
image to its carrier contract. E_1 is not a body/argument row union. A_1 is
not identified with native R. Merely naming them supplies no authentic F_1,
check origin, license, receiver declaration or successful assignment.

Charter §17 fixes the inert scheduling. Carrier-Delay still requires the
actual Call-owned ReifyOrigin/root/view/scope to form the original typed
carrier. Printed `Comp(empty,B)` is not the entire ReturnImage contract,
nor evidence that arbitrary admitted carriers return.

For context only, the Draft wrapper skeleton is
`Fun(Value(Z),Comp(empty,B))`; c2 receives the whole `Delay(X[n_1])`.
Value entry forces once, rebinds z, then returns y. Its conditional complete
result is `Comp(E_2,A_2)`, and g's body/result skeleton is
`Fun(Value(B),Comp(E_2,A_2))`. Neither c2's checks nor A_2=native S is
derived. c3–c5 retain their own Application obligations. This substitution
preserves their source schedule without pretending to type them.

The Draft's own scope leaves recursive-binding inference, satisfiability,
complete invocation and lifecycle open. This is its conditional skeleton,
not an accepted original typing.

## 4. First unavailable introduction and why consumers do not supply it

Attempt accepted Call-input §3.4 at c1. Beyond the Name/code children it needs

```text
actual Application/Gen-Call-0 origin at c1 with complete dependent F_1,R_f;
Call-owned ReifyOrigin(c1,Name(y),r_arg,Comp(empty,B),scope/incidences);
original complete Comp(E_1,A_1), result port o_1;
actual emitted VIncl-origin(A_o,F_1);
actual emitted WholeArgCompatible-origin(J_y,CarrierContract(F_1));
Suffix_c1(U) at the original actual provider interface U.
```

These are emission/formation origins, not truths of constraints. No eager
solution is required. The first unsupplied **App-specific** introduction is
the authentic complete Application producing this package. The Draft row
refers to existing complete relations; it gives no selected original raw
generator producing this exact package for an active recursive root.

Earlier complete declaration/port applications for authentic f/y registration
are also not established here. The relative Name steps retain those premises
explicitly. Even allowing their static schemas for inversion does not supply
the Application input. The obstruction does not prohibit static active f
references or demand completed f membership before constraint generation.

Original Call §§1–4 is uniform on already emitted records. Its apply/step
generator's formal-root/Role_0 scope does not cover recursive f.
OSig-Demand forms Inv from supplied complete demand; OC-CallEff forms its
typed occurrence from supplied e. Neither emits e or additional Application
checks, whole carrier or actual provider suffix.

IF-Insert consumes an actual independently typed clause; IF-Use consumes its
original scoped whole substitution. Its complete Call retains callee,
carrier, actual returned callee/current world, receiver phases, complete
result/future and every original alternative. A native endpoint pair is not
that input. Preallocated finite monomorphic cycles supply static placement,
not operator typing.

**Stop:** no Q_c1/telescope, authentic g publication input, or commuting-map
proof is claimed.

## 5. Actual operational owners and required action

Reference Typer.scala at `9bae772624c23b52a93c1b226157e16898b4d9db`:
typeLetRhs:48–55 introduces recursive o at level 1; typeTerm:62–83 gives
g's B/Z/R/S at level 2 and c1's `o <: Function(B,R)`;
constrain:106–125 invokes negative extrusion; extrude:134–159 produces
C/D at level 1 under one polar memo and bounds `B <: C,D <: R`, storing
`Function(C,D)` on o. c2 adds `R <: Z,B <: S`.
Publication is `PolymorphicType(1,Function(B,S))`.
freshenAbove:166–190 and instantiate:205–207 use one coherent map per use,
fixing low C/D and freshening reachable high coordinates. No reference
intrusion exists.

The approved occurrence has origin G, receiver F. Definition-owned Names
give G→F at c1, F→G at c3/c5, qualifying the actual pairs for C=B,D=R.
This neither locates C/D in a full source telescope nor establishes a lawful
equality action on it.

| Current Rust owner inspected | Retained output/activation and limit |
| --- | --- |
| local_source.rs:329–372,636–657 | Parameterized local self identity and Names; exact zero-header Lambda-valued source admission not established |
| candidate_source.rs:245–325,375–411,660–686 | Active-root Link, Apply recipe/exact child endpoints, execution of admit_candidate_fact |
| shadow_apply.rs:1308–1420 | Integrity check, four-port demand, NativeInterface, provenance, actual constrain_live_value activation |
| candidate_call.rs:15–59,88–126,152–258 | Source/native coordinates; pending original Gen-Call-0, carrier and complete receiver/result/future suppliers |
| candidate_extrusion.rs:89–126; candidate_intrusion.rs:171–222 | Copy before bound traversal; parent/polarity/target retained, without complete source Call/G/F event |
| candidate_scheme.rs:1320–1386 | Installed local root/boundary, later graph capture/fresh use; inspected installer emits no Source-Generalize p_g/K_g/N_g/T_g |

These paths are under crates/yu-hir/src/module and crates/yu-solver/src.
Actual native activation is traced; complete source equality activation/replay
is not. The Rust demand has effect ports: scalar shape erasure does not
identify it with F_1.

If authentic Q_c1/Delta_1 were supplied, the bridge must construct a typed
projection pi and lawful whole action for each actual g allocation A_i,
with native coherent map N_i, such that

```text
pi(A_i(Q_c1)) = N_i(pi(Q_c1)).
```

The map must cover original demand/bounds/pairs/equalities and the entire
dependent license/provider/world/carrier/receiver/result/future tuple.
Source-Generalize Build and §§5.1–5.2 do not create its clauses from levels.
Draft §6 substitution assumes preserved typing premises/source tags; it
does not prove N_i lifts to that whole action or supply pi.

If authentic input retained shared C and eligible B, allocation of its
equality would yield C=B_0 and C=B_1. That remains conditional; this pass
supplies neither the input incidence nor activation. Per-frame C_i changes
the native map; textual quotient C=B needs its own preserving operational
action/later freshening proof. Neither route proves source admission,
rejection or principal coverage.

## 6. Economy audit, omissions and one next action

Claim classes: conditional derivation in Draft §6; bounded accepted-consumer/
native-owner characterization. No new invariant, probe, implementation or
parent closure. The original A/B preservation/natural-inference/principality
gate remains OPEN at complete raw Application and source/native action.

Prior allocation and representation-falsification attempts left this premise
untouched. This pass attacks the raw introduction owner and confirms the
generic structural row does not establish it. Under the economy audit,
complete Call and faithful scope/action are genuine A/B needs; reconstructing
them later from IDs/levels/bounds/Value SCC is D debt. Apply knows actual
children/source/native demand; extrusion knows actual pairs. Retention at
those owners may remove reconstruction, but alone proves no complete local
law. Another conditional frame proof or reclassification is not progress.

One next action: primary's existing source-construction/authority lane must
establish the exact c1 Application local introduction in §4 with its complete
telescope and typed native projection/action. If selected laws do not specify
it, return that localized missing local law to that lane before another
equivalent proof packet. No restriction or reapproval of selected intrusion
is recommended.

Unverified: exact admission, complete registration/declaration maps, recursive
L4, Application/Q_c1, g component/publication, equality activation/replay,
effect hygiene, complete Call discharge, all-source soundness, required
principality, termination, production correspondence and F5 replacement.

## 7. Checks, runtime and commit packet

Checks: bounded cat/sed/rg reads; manual rule substitution/inversion;
read-only HEAD/branch/status; SHA-256 and byte comparison of 21 direct
repository dependencies against the pinned baseline, all matching.
Reference HEAD/hash inspected without running inference. Initially truncated
captures were followed by narrow decisive rereads. Zero builds/tests/probes/
measurements/samples, heavy processes, children or Git mutations.
One read batch used five short shell processes; later reads sequential.
CPU/RSS and exact total wall time were not measured. Review is primary-owned;
writes stop at handoff.

The callable schema exposes prover; config registers it with ordinary
gpt-6.1-sol/high defaults and prover.toml omits pins. Actual launch arguments
are not exposed in this packet: requested role/model/effort and observed
effective model/effort are unknown to the leaf. Task identity
`/root/construct_c1_raw_application` does not establish model metadata.
No Astra or nested assignment ran.

Direct dependencies byte-matched: active-root note; typed-core Draft; charter;
LocalSelfRec; Source-Generalize definition/proof; Call-input; Original Call;
IF definition/construction; occurrence decision; parent/copy; copied rows;
inference principles; the seven Rust owner files in §5. Their hashes remain
unchanged; reference Typer.scala SHA-256 is
`f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9`.

Commit packet:

- Exact lease: `notes/theory/2026-10-13-c1-raw-application-owner-construction.md`.
- Baseline: `beceb0bc91b35e84b4f62b353fc6c2abf18e0414`; changed dependency hashes: none.
- Status: unreviewed conditional Draft skeleton/bounded characterization; no parent closure or implementation authority.
- Checks run: static owner reads/substitution/inversion and dependency byte/hash comparison; zero builds/tests/probes/measurements.
- Proposed message: `research: isolate c1 raw Application introduction premise`.
- Shared-record deltas for primary/curator: Draft §6 synthesis does not establish active-root c1 Application; retain raw Application/action, g publication, admission and original preservation/principality gates OPEN. No shared record edited.
