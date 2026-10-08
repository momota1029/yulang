# Record results: conditional local expansion and public extraction

Date: 2026-10-08
Baseline: `89b799fbc5d1a1f1b74d6486b76f58f113dccf4b`
Branch: `research/simple-sub-intrusion`
Status: unreviewed research; conditional construction and minimized falsifiers
Lease: this file only; frozen on submission
Semantic selection / implementation / aggregate gate closure: none

## 1. Objective and result

Extend the selected native projection derivation to an immutable unannotated
function returning a newly constructed one-field Record containing its formal.
The repository's retained source spelling is:

```yu
my box x = { value: x }
```

The colon/brace spelling is supported by the retained stable-core fixture
`tests/contracts/stable-core/v0/run/vm/pass/record_field_named_like_str_method/main.yu`.
This is a source spelling locator, not evidence that the current successor
semantic HIR implements Record formation. In particular, the current
`syntax-reference/en/src/expressions/braced-statement-block.md` §§1–4 gives
these braces a statement-block CST and expressly leaves Record semantics out
of scope. No `Record{value=x}` source constructor is introduced here. Below,
`Rec_a` denotes the existing mathematical Record descriptor with field
`value:a`, and `fields(r)` denotes the actual semantic field tuple.

There is a finite compositional extraction **conditional on two local owner
inputs**, H-R and H-K in §3. Existing contracts specify its sharing and
inertness requirements, but do not instantiate those two inputs. The note
therefore does not extend the selected PE-ID/PE-PICK theorem unconditionally.
It reduces the extension to the original Record introduction/inversion seam
and the original complete Lambda synthesis/production seam. Neither missing
input is a Generalize, exporter-success or query-success premise.

The one-field Boolean witness in §7 refutes reuse of the selected `EntryValue`
result dependency. It also shows why changing the displayed result to a Record
while retaining the old raw alias substitution is invalid.

## 2. Exact authority and reused results

| Frozen input | Governing sections and use |
| --- | --- |
| `notes/design/2026-10-08-native-projection-public-export-definition.md` | §§2–4 select generic inlet, projection witnesses, VP+Echo/Fixed roots, actual public decoding and native consumer; scope is id and finite-public-import pick. |
| `notes/theory/2026-10-08-projection-public-export-construction.md` | §§2–4 source formation, extraction and alias maps; §§5–7 same-callable soundness, Value/Computation/Function consumer and PE-ID; §8 finite public imports and PE-PICK. |
| `notes/design/2026-10-08-source-generalize-definition.md` | §§2–4 actual final root, constructor-owned dependency traversal, exact scope/alias allocation, GS/GC and separate public/production boundaries. |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | §2 L1–L5; §3.1 Record/tuple and Lambda rules; §3.2 actual structural checking; §3.3 owning records; §§5.1–5.2 fixed closure/allocation; §§6–7 direct construction/inversion and joint GS/GC. |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | §§2.1–2.2 independent whole-tuple local relations and active descriptor conjunct; §§3.1–3.3 immutable Record field-provider tuple, inert formation, same world and original admission/history; §3.7 original Option 2 boundary. Concrete clauses remain Draft. |
| `notes/theory/2026-10-08-native-projection-certificate-constructors.md` | §§3–5 global local proof grammar and explicit Bind/Read/Return/Invocation witnesses; §6 CE eliminates only forced raw projection aliases and preserves all proof choices. Record width/depth is a checking rule, not a Record formation constructor. |
| `notes/theory/2026-10-08-id-public-phase-constructor.md` | §4 ordinary phase grammar and independent extras; §4.4 Echo; pending branches, current raw-resume suffix and hereditary future fields. |
| `notes/theory/2026-10-08-uniform-value-entry-constructor.md` | §§4–5 fixed generic raw inlet and same-witness admission injection; §§6–7 uniform projection proof and eligibility. The admission map is reusable; the projection body's result argument is not reusable without a Record rule. |
| `notes/design/2026-10-02-source-result-synthesis-choice.md` | §§2,4 Value entry forces/rebinds before the body; an ordinary Record value result uses pure Result; latent fields are not recursively forced. |
| Committed `notes/theory/successor-proof-obligations.md` | GENERALIZE and PROJECTION at the baseline remain OPEN-PROOF. Read from the baseline blob, not concurrent ledger edits. |

Accepted decisions used: independent admission before receipt; one fixed raw
generic inlet with separate inferred descriptions; actual final source roots;
one whole frame for a real new and the same frame for aliases; complete fixed
imports and original proof/event scopes; independent Option 2 alternatives;
natural ordinary behavior is not restricted to simplify a proof. This note
selects no new source meaning, allocation policy or production kernel.

## 3. Claim classes and exact missing local hypotheses

**Established within the cited scopes:** selected generic admission injection,
native projection CE/PE-ID/PE-PICK, and source GS/GC relative to genuine L1–L5.
The Record/tuple inventory fixes actual field-provider sharing, original world
and dependencies, and inert construction. These are requirements, not an
explicit invertible full Record certificate grammar.

**Candidate representation:** the field-assembly certificate table and export
record in §§4–5. They are research representations of supplied ordinary
constructor data, not newly selected semantic tags.

**Conditional theorem premises:**

**H-R (Record owner law).** For the actual Record occurrence, its independently
specified original local law supplies a finite source-free typed clause
program `R_form`, with the following complete interface:

```text
R_form(original Record identity/label and field-port registrations;
       child decorated values/providers and FULL child certificates;
       actual Record value/provider; before/after worlds;
       original guards/incidences; FULL formation proof fields).
```

Its clauses use only original ordinary value/world/field/proof operations.
They cannot dereference the source occurrence or assert source legality,
Generalize success, export equivalence or successful Q. They give introduction
and inversion for the actual source Record rule, on the **same full tuple**.
All allowed proof terms, intermediate witnesses, alternative tags, field
occurrences and world evidence remain explicit. They establish hereditary
Record membership by the actual same-provider field constructor, with its
original compatible-world restriction and field eliminators. Formation does
not force any latent child. Any world action, identity creation or provider
registration is exactly the original Record action, with its original event
scope; this hypothesis does not assume an unchanged world or a fresh provider.
The field occurrence map preserves repeated child providers and satisfies the
ordinary whole-frame/substitution actions with original binder telescopes.

The selected source inventory entails the listed sharing/inertness obligations
but supplies no explicit `R_form` equations, complete witness inventory or
inversion. H-R must be established at the Record owner; a checking width/depth
certificate does not establish it.

**H-K (complete synthesis owner law).** Before Build/Generalize, the actual
unannotated Lambda owner supplies its final complete ordinary root as a finite
source-free expression

```text
K_box(I_q[a;Delta], a, Rec_a, IF; Omega, Record ordinary operands).
```

The expression has active complete admission, phase, production and future
clauses, including every independently licensed extra and every original
guard. Its local constructor law proves introduction of the actual callable
using H-R and the original receipt/Force/rebind/Return/invocation actions.
Its ordinary equations are attached to the actual final root and their
operand scopes are given by the owning construction. No hidden source-body
lookup or source-introduction witness is required for a production-only arm.
The premise is a **finite independent local Lambda root law**, not equality
of an already generated whole export to a source relation.

The selected projection law is specifically VP+Echo or VP+Fixed. Neither
selects `K_box`. A possible VP refinement connecting result fields to entry
would be a candidate semantic choice; this note does not select it. H-K also
cannot be inferred from the printed arrow `a -> Rec_a` or from actual trace
containment. If the existing owner chooses an ordinary root with looser
production alternatives, its complete clause program must be retained as is.

**Bounded scope:** one Record occurrence with one resolved formal field, no
annotations/conversions/State/recursion/opaque import, and finite original
interface/proof-slot maps. Finite independent client proof grammars may have
arbitrarily long finite lawful developments, original W and nonidentity local
checks. L1–L5 remain in force. Additional Desc declarations or actual fixed
contract dependencies, if present in H-R/H-K, use the selected Generalize walk;
the displayed one-template form below assumes there are none beyond formal a.
These conditions define this research case, not source rejection policy.

## 4. Full-tuple constructive expansion under H-R

Let X include the entire original inlet/receipt/carrier/Force/check tuple;
Bind and immutable Read proofs; actual field and Record identities/ports;
actual before/after worlds; all field and formation proof terms, their
intermediates and guards; pure Return and invocation-return proofs; fixed
anchors/import closures; nu,K,D; and W. Every witness remains at its original
Shared, ViewLogic, EventField, EventProof or checking telescope.

Write the completed entry as `(v,p,C_force)`. The actual source construction
expands, using selected Bind/Read laws and H-R, to:

```text
Input_I(X) and OriginalJointGuards(X)
and (v_bind,p_bind)=(v,p)
and BindCert(b;(v,p),C_force,C_bind; FULL Bind fields)
and (v_field,p_field)=Lookup(C_bind,b)
and ReadCert(b;(v_field,p_field),C_bind; FULL Read fields)
and R_form(registrations;
           {value:(v_field,p_field,FULL field evidence)};
           (r,p_R),C_bind,C_R; FULL formation fields)
and (v_body,p_body)=(r,p_R)
and PureReturnCert(Rec_a;(v_body,p_body),C_R; FULL Return fields)
and (v_out,p_out)=(v_body,p_body)
and InvocationReturnCert(IF,result;(v_out,p_out),C_R,C_out;
                         FULL invocation fields)
and AllOriginalLocalCheckClauses(X) and W(X,z).
```

The conjunct names abbreviate the finite ordinary clause inventories already
specified by the input laws, not opaque whole-source truth predicates. The
actual Record `(r,p_R)` and its worlds/certificates are retained in X. The
private alias tuple z contains only formal/read/body/outward raw aliases.

Selected Install/Lookup laws force `(v_field,p_field)=(v,p)`. Substitute that
pair in the one field operand. Substitute `(r,p_R)` in body/outward raw
positions. Leave `R_form`, `(r,p_R)`, `C_R`, all field ports and every proof
coordinate intact. These are the only total substitutions. In particular:

```text
field_value(r,value) = v       field_provider(r,value) = p
outward_value = r              outward_provider = p_R
```

are distinct relationships. The first pair must be derived by H-R's actual
field law; the latter pair follows from selected Return/invocation raw images.
There is no equation `(r,p_R)=(v,p)` and no inverse reconstruction of a Record
identity from its printed descriptor or field value.

Forward F deletes only forced private z, retaining X. Reverse G restores z by
Install/Lookup and the same Record-result alias graph. Every incident predicate
and W receives that exact total substitution, or keeps the explicit alias
graph. Expansion/inversion in H-R then restores the original Record rule
with the **same** formation and child witnesses. Thus F/G are inverse on the
retained solution/observation fiber. They do not choose canonical proof terms,
copy a shared world, or reconstruct `(r,p_R)` from the formal.

At Start/Received/Forcing there is no completed field or Record result. At
EntryValue/Body only actually introduced read/formation prefixes exist. The
Record appears only at its original formation event, with H-R's world action;
InvocationReturn remains separate. Response/raw-resume expansion applies under
the original event telescope to the unfinished suffix; receipt is not replayed.
Future demands read the same returned Record/provider, use its genuine field
eliminators, and retain the selected child provider's independent hereditary
contract. A nested child return is not equated with either r or v. Induction
on finite developments extends these local maps under their original scopes.

## 5. Finite extraction and ordinary public decode

At publication, invert the actual source rules once, verify that the final
root is H-K's synthesis root, and run the existing Generalize dependency walk.
Read the field occurrence/child-incidence map at the Record owner. Apply §4's
total substitutions. Emit the following candidate representation:

```text
RecordResultExport(
  display: ForallAt(sigma,a,Arrow(a,Rec_a)),
  boundary: Omega,
  inlet: I_q[a;Delta],
  ordinary_root: finite K_box term and ALL its active operands/alternatives,
  result_fields: {value:EntryField(formal,original field port)},
  formation: global R_form clause-program reference and original registrations,
  certificates: original typed slots/telescopes for
                Bind, Read, field checks, R_form, Return, invocation,
  sharing: actual child occurrence map and actual result/provider event slots
).
```

`EntryField` is an encoding label in this candidate, not PE-ID's EntryValue
dependency. It points to the field operand, never to the entire result. The
schema has an actual `(r,p_R)` event slot and complete Record proof slots.
It stores no source Record/Lambda body, Build graph, source-root accessor or
source-observation oracle. It references only supplied global ordinary laws
and finite typed semantic operands. This deletion is justified exactly by
H-R inversion; a retained opaque source predicate would fail the construction.

The size is linear in the boundary, Delta, H-R/H-K finite clause programs and
original slot/incidence maps. Arbitrarily large future proof terms are values
of finite grammar slots, and histories are not pre-enumerated. No new inferred
type for r is created merely to shorten the theorem: its description is the
structural term Rec_a in this bounded case.

A real new frame uses the selected whole-frame action to allocate a fresh
ordinary description root u_i, instantiate a and every incident I/Record/K_box
operand consistently, and retain fixed Omega. The decoder installs K_box's
complete ordinary equations **at u_i**, together with the same Record formation
certificate schema. It does not execute Record construction or allocate a new
runtime result during type instantiation. An alias uses the same frame/root.
Actual Record EventFields belong to the actual invocation event and remain
shared if two frames describe that event. EventProof witnesses can differ
between those frames at their original dependent scopes. Shared initialization
evidence is never copied. Any external installed contract retains its complete
fixed closure; bare box has no such capture.

## 6. Conditional theorem and compositional proof

**Conditional PE-RECORD.** Under H-R, H-K and the selected local L1–L5, the
construction in §§4–5 produces a finite source-free ordinary public object for
the bounded native box case. It is sound for the same actual source callable.
For each finite independent source-lawful joint client proof grammar d and
well-scoped W, it constructs a finite public allocation/proof grammar before
assignments, challenges or histories, with exactly the original retained
solution-and-complete-observation fiber under F/G. Original fixed dependencies,
field/provider sharing, actual Record identities/world actions, original proof
strategies and every independent complete production alternative are retained.

**Proof.** The selected generic inlet injection supplies actual admission for
the same independently checked carrier before receipt. Its designated Force
eliminator supplies the same prechosen-a entry payload/current world. The
selected Bind/Read constructors supply that decorated payload at the field
occurrence. H-R introduction produces the actual Record and its complete
hereditary certificate at its actual world action without forcing latent
children. Pure Return and original invocation return preserve that Record.
H-K's genuine local root law places these observations in the installed
ordinary equations at u_i, with their original admission/future obligations.
Finite pending/raw/future developments use those same original local actions.

For the exact fiber, §4 proves local expansion/inversion with identity on all
nondefinitional fields; H-K's finite ordinary term is transported by the same
whole-frame action and total raw substitution on every active alternative.
The production relation is its own complete coordinate, not the Record source
proof image. No production-only arm receives a fabricated Record-introduction
or source-execution witness. If an arm has distinct ordinary formation proof
fields, those fields remain in that arm with their original scope and law.

Now perform PE-ID §7's client-constructor induction. Generalize's existing
allocation supplies new/alias/Shared/ViewLogic/event distinctions before later
assignments. Replace just the body introduction row by §4's Record expansion.
View uses the existing ordinary Value/Computation/complete Function consumer
with the same finite local proof terms at u_i. Structural Record checks use
the actual selected fields and H-R's hereditary laws; they never inspect the
private body. Joins use one original world/strategy, and Bind retains the actual
Return/rebind or ordered pending suffix. Reverse G and H-R inversion restore
the source rule, then SRC-J supplies the same lawful joined derivation.
There is no per-field or per-frame marginal witness gluing. QED conditionally.

For example, at a=Bool, checking the result into a Record with `value:Any`
uses the genuine same-field hereditary Bool-to-Any proof and original Record
depth rule. Complete Function checking still requires both complete domain
and production proofs, including every H-K arm and changed future demand.
This note does not supply an unconditional Direct certificate from scalar
inclusion alone, or choose the missing H-K law to make that comparison pass.

## 7. Minimized falsifiers and mutation failures

**One-field EntryValue falsifier.** Take one independently typed pure carrier
whose actual Value-entry Force completes with true at Bool. Use one lawful
invocation, no imports, requests, resumptions or latent fields. The source
Record result is `r={value:true}`, with its actual provider p_R and field
provider p_true. Bool values and Record values have distinct constructor heads.
Therefore `r != true`, independently of whether their providers happen to
share any representation. PE-ID's EntryValue/Echo would require outward raw
value=true. That requirement fails on this actual source result. One field
and one completed event suffice; no long history or exotic proof choice is
needed. This witness is a deduction under the authentic Record introduction
law, not an executed compiler result or an unconditional construction of H-R.

Changing only the displayed result to Rec_Bool leaves the same invalid raw
equation. A raw-alias eliminator which drops r and reconstructs it as true
changes the observation `head(outward)=Record` and the genuine Record field
lookup. It cannot preserve arbitrary W or the whole public fiber.

**Smallest nontrivial field-sharing extension.** For
`my pair x = { left: x, right: x }`, both field occurrences refer to the same
raw p_x. On an envelope admitting distinct providers of the same printed type,
a proposed extraction permitting two distinct field providers loses
`field_provider(r,left)=field_provider(r,right)`. Two occurrences are necessary
to test repeated-field sharing; existence of those distinct providers is an
explicit premise of this second mutation. The one-field witness already tests sharing
between entry and its field. This is a falsifier of provider-copying, not a
second assigned proof lane or a selected meaning for pair.

Further named shortcut mutations fail structurally: erase r/p_R and the
original result identity cannot be reconstructed; merge C_bind and C_R and a
law with an actual registration/world action is changed; canonicalize a
formation proof and W can distinguish its original allowed proof choice;
freshen actual EventFields per description and one shared invocation becomes
two events; constrain every production member to have a source formation proof
and independent extras disappear. No executable mutation suite was run.

## 8. Verification, independence and remaining gate

Method: constructive symbolic rule expansion and an analytic one-field
counterexample. Inspection commands were bounded `cat`, `sed`, `rg`, read-only
Git baseline/status/blob reads and SHA-256 comparisons. No code, test, checker,
build, formatter, executable probe, generated cache or Git mutation was made.
The initially attempted `spec/` and `crates/yu-syntax/tests` search roots do not
exist; the relevant spelling was located in the retained stable-core fixture
and syntax reference instead. No exhaustive repository-wide source/HIR survey
is claimed. The historical Record source-boundary note was read for its
fixture/CST distinction; its old production locators were not revalidated and
are not current production claims here.

There is no executable oracle. Source legality remains the selected independent
declarative grammar, and public checking uses the same genuine global local
laws. The conditional proof establishes the transformation from those rules;
it does not independently establish H-R/H-K by duplicating supplied transition
assumptions. Parameter/carrier/world/local checking assumptions are shared
with the selected native theorems. H-R/H-K have no solver/exporter-success
premise and do not assume a complete public/source equivalence theorem.

Coverage: one source schema, one Record field, finite original local programs
and finite client proof grammars with original unbounded finite developments;
one analytic Bool event witness and a two-occurrence sharing mutation. Seeds,
numeric search ranges and timing samples: none. Processes: sequential bounded
read/hash/edit commands; zero heavyweight processes. CPU/RAM/total wall time
were not measured. No incomplete enumeration is presented as coverage.

Omitted: establishment/selection of H-R and H-K, parser-to-native semantic
correspondence for box, arbitrary imports or recursive/State/adapter forms,
all-semantic-view principality, effective production inference/search,
publication lifecycle and cutover. The canonical GENERALIZE/PROJECTION statuses
are unchanged. This producer's inspection is not independent review.

Recommended next action: assign the actual Record/Lambda constructor owner one
bounded task to supply the independently typed full `R_form` witness grammar
and actual complete `K_box` result law together. Then independently review this
conditional expansion against those concrete laws; do not run another alias
or descriptor-only probe while those same premises remain absent.

## 9. Frozen dependency hashes and commit packet

Direct dependencies were byte-identical to the pinned baseline on inspection.
Concurrent shared task/index/theory edits were excluded from dependency reads;
the committed ledger blob governs the reported status.

| Dependency | SHA-256 |
| --- | --- |
| Native export definition | `aed6ef63b01f555a5f2804f87a599167c1a30fa999afc0b9d9f11b8ae974a919` |
| Integrated PE-ID/PE-PICK | `4cf84e7a38153b893f1d339780598e2b79084c747ecb883acf0e4fdaa49cf631` |
| Source Generalize definition | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| Source Generalize proof | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| Source-contracts Record inventory | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| Native projection certificate constructors | `04c5699dfaaf5f98ee9db54df5bd124f25e7131abb6bc3104e1675a5490f74a8` |
| Ordinary phase constructor | `140c9c907f3ae27120acd84d96c75b2d9a64b437e3e0e71c540c0030864ebb6b` |
| Uniform Value entry | `273e8dae447e9997d586fc07abf48883c76b90988c8906094dd428a48339c2e5` |
| Source result synthesis | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` |
| Brace-block syntax reference | `81f637db94d344162c4e2541ee4b955b4469180e755ee800aa39bf9074987b58` |
| Historical Record source-boundary note | `693d7739d24a3fe0bc65ab7f60b46643f9ace232c7218cb647649d442c8cf8af` |
| Retained Record spelling fixture | `4c7e8ba61bb866c674d24b5738203d0b8ba5b2f9aeddad2956bce8d5c20e9ba3` |
| Committed obligation ledger (baseline blob only) | `f0373e133377f8a181e08710eb35371e36b75026051571b9f54342ab64f96af5` |

Commit packet:

- Exact leased path: `notes/theory/2026-10-08-record-result-public-export-construction.md`.
- Baseline SHA: `89b799fbc5d1a1f1b74d6486b76f58f113dccf4b`.
- Changed dependency hashes: none; final dependency recheck accompanies handoff.
- Claim/review status: unreviewed conditional construction and analytic
  minimized witness; frozen for primary review; no authority/closure promotion.
- Checks: narrow source reads, committed GENERALIZE/PROJECTION ledger reads,
  exact dependency hash/baseline checks and output lease/scope inspection.
  No tests/builds/probes run.
- Proposed checkpoint message: `research: derive conditional Record-result public extraction`.
- Shared deltas intentionally left to primary/curator: link this conditional
  extension and the H-R/H-K owner boundary if accepted; preserve aggregate
  statuses; no task/index/authority/ledger/question-board path was edited.
