# R60: scalar projection/lifting and the missing joint ascription supplier

Status: candidate bounded mathematical derivation plus exact source/native
obstruction. No adopted constructor or source-solution preservation theorem.
Sole author `/root/r53_ordinary_mixed_capture_proof`, session
`current-conversation-2026-10-19-r60`; no descendants.
Contract revision2 SHA-256
`6b40870963d796a9bc1d125334a39e049d893450da8d1b38bdc0b310b5f982f1`.
Baseline `b62bf4bed359ed5f8bd4728923d1807044f9e8c9`; activation/receipt commits
`a3ab8baff` / `18bfb6635` parent-reported, no Git verification performed.
Exact outputs: this note and `tasks/agent-loop/inbox/20261019-r60-proof.md`.

## 1. Result and parent application

The new method is existential elimination and explicit lifting of constructor
auxiliaries, followed by a check of the actual source/permission/result owners.
It proves a precise scalar fact: a shared AE auxiliary and an ordered pair
have the same projection E_arg<=T, provided the remaining constraints are
independent of those auxiliaries. Preserving every old uncoupled auxiliary
assignment is not the correct source-solution preservation requirement.

The first missing premise for the actual source is a JOINT whole-ascription
correspondence: it must identify the original source incoming carrier with the
same-p_A/provider checking/exposed AE ports, preserve its permission witnesses
and correlated result obligations, and provide a lift for every permitted
source solution. The pinned formal rule supplies no such whole-ascription
theorem, and the current native negative-row constructor is absent. This is
a missing supplier under settled annotation policy, not a new policy vote.

Apply the scalar result to R59/R60: shared-AE is not disproved merely because
it changes auxiliary A_c/A_e values; conversely excluding R59's assignment
algebraically does not prove that shared-AE preserves the original source
contract. The actual admitted same-provider entrance and joint lifting remain
OPEN. The parent forwarding theorem §§1,6–7, original source domain, arbitrary
finite prefixes, shared assignment and independent receiver/foreign-continuation
quantifiers remain OPEN 0→0. Simple-sub A/B and production remain OPEN;
R50 remains NOT ADOPTED.

## 2. Fixed source and preserved distinctions

```text
act io:
    our tick: int -> int

my forward (t:[io] int): [io] int -> [io] int = t
my outer (q:[io] int) = forward q
```

Fix its original io declaration identity I, original forward Lambda L/formal
t, formal row p_t, whole-function argument row p_A and result row p_R. The
three SourceNodeKeys are distinct although their concrete sets equal {I}.
The whole Function root has effects=None; its argument/result have the
respective rows (`source_annotation.rs:411–500,531–585`;
`local_source.rs:598–625,714–721`). Original definition scope plus exact
Function path/provider identify the annotation boundary; scope/spelling alone
does not establish endpoint identity. The header's single original Lambda
and formal can be lexically associated with its first argument. That static
association is not the typed carrier/correspondence proved below to be needed.

Constructor-domain membership is unchanged from reviewed R58/R59, not a full
typing/compatibility result. All negative permission meanings and positive
allowance meanings are already selected. Incoming E receives no permission-
derived closed cap; ordinary generated constraints and symbolic dependencies
remain. Permission is not an effect contribution or automatic subtraction.
Declared result interface, actual inflow and residual remain separate.

## 3. Existing polarity and constraint entrance

Use original provider schema P=(Int−,T−,R+,V+) with direct-Name N and
T<=N, N<=T, N<=R. Checking and exposed schemas from R59 are

```text
C=(Int+,A_c+,B_c−,Int−),
X=(Int−,A_e−,B_e+,Int+).
```

Native Function sign reverses on argument/AE, preserves on result/RE;
source variance is negative at p_A and positive at p_R
(`candidate_effect.rs:1780–1871`). Intended slot40 P<=C supplies A_c<=T and
R<=B_c plus Value checks. Slot41 exposes X. Slot42 adds nothing here because
the Function root has no computation row
(`candidate_effect.rs:1627–1704,1740–1777`; `lib.rs:12655–12683`). A later
actual exposed Apply supplies x=E_arg<=A_e, B_e<=E_call<=E_out
(`shadow_apply.rs:1788–1923`). None of these facts alone supplies A_e<=A_c.

These are schema/owner facts; the fixed ordinary source is still rejected
before collection, and its native A_c/A_e/first use map are UNREACHED.
Preflight and native guards stay intact (`candidate_source.rs:603–615`;
`candidate_effect.rs:1933–1935`). No failed or assumed transition is admitted
as evidence of the desired route.

## 4. Projection and explicit auxiliary lifts

Let effects range over any preorder with <=. Fix values of x,T and other
variables z. Let Q(x,T,z) be any fixed constraint predicate with NO occurrence
of the auxiliaries introduced next. It can include result constraints involving
T,N,R,B_c/B_e and z, so long as none depends on the eliminated AE auxiliaries.
Then both equivalences hold:

```text
Q(x,T,z) and x<=T
  iff exists A. Q(x,T,z) and x<=A and A<=T;

Q(x,T,z) and x<=T
  iff exists A_e,A_c.
        Q(x,T,z) and x<=A_e and A_e<=A_c and A_c<=T.
```

Projection is transitivity. For lifting, retain the SAME x,T,z assignment and
choose A=x in the first formula; choose A_e=A_c=x in the second. Reflexivity
and x<=T satisfy all new constraints, while Q is unchanged. These are explicit
auxiliary correspondences; no injectivity or finite-family enumeration is
needed. Setting both auxiliaries to T is another valid scalar lift. There is
no constraint A<=closed{I} or Support(I)<=A in this construction.

This establishes scalar projection equivalence of a shared auxiliary and an
ordered pair for this exact factorization. It does not adopt either as a
compiler representation or prove source completeness. It also explains a
false preservation test: with x=empty,T={I}, an ordered assignment
A_e=empty,A_c={I} can be lifted to a shared A=empty while keeping x/T fixed.
Demanding unchanged values for BOTH old auxiliary variables would reject that
lift even though its source-observable scalar projection is identical.

Conversely, remove the bridge A_e<=A_c and x<=T no longer follows. R59's
assignment x=A_e={I}, A_c=T=N=R=empty, B_c=B_e=E_call=E_out={I} satisfies
the uncoupled scalar factorization. It violates BOTH paired formulas above
for those fixed x/T values: no auxiliary lift can exist when x is not <=T.
Therefore exclusion of that assignment by these CANDIDATE SCALAR repairs is
proved. Exclusion by an authentic source-preserving constructor remains OPEN,
because the source/native reference correspondence has not been supplied.
The assignment is not declared an allowed or forbidden full source solution.

The theorem cannot be used when Q depends on the eliminated auxiliaries or
their typed/evidence identity without proving an appropriate substitution law.
For example, arbitrary Q(A_c) can distinguish A_c={I} from A=x=empty. This is
only a mathematical dependency warning, not a new source or evidence that
the actual annotation demands that arbitrary Q. The actual dependencies must
be obtained from the owning source/constructor theorem, not assumed absent.

## 5. The actual solution-preservation obligation and its first gap

Let S denote the ORIGINAL selected source/annotation contract for this fixed
source, under its actual typing premises and joint xi=(nu,K,D). Do not define
S to be the old uncoupled native formulas or to be x<=T by fiat. Let C be a
candidate native paired constructor, and Corr its explicit source-to-native
correspondence on typed positions, original provider/binders, effect endpoints,
permission evidence and results. The necessary preservation statement is

```text
for every sigma satisfying S under its actual premises,
  there exists rho satisfying C with Corr(sigma,rho),
  preserving sigma's original observable/evidence coordinates.
```

A matching soundness/projection judgment must send a C result back to the
same source contract; existentially hiding evidence or changing receivers is
not a valid projection. Auxiliary constructor rows may be reindexed under
Corr, but original declaration/position/provider identities and joint K,D
cannot be replaced by independent witnesses. The native checked original T
must itself have its legitimate correspondence to the source entry; it is
not silently identified with a source variable merely because both use T in
an informal schema.

To apply §4, the supplier must establish either that the whole joint remainder
is independent of A's auxiliary identity, or a source-indexed substitution/
transport law preserving its permission/result dependencies under the displayed
lift. It must also derive the original source incoming-to-checked-provider
relation under Corr. Assuming those facts because they make the scalar proof
work would assume the R60 goal. Choosing a shared row before this supplier is
proved would be an unreviewed representation, not a completed derivation.

The first exact missing supplier is this joint WHOLE-FUNCTION-ASCRIPTION
judgment at p_A: source incoming carrier and original checked provider entry
must be connected through the same declared interface, with permission and
correlated B_c/B_e result meaning preserved under one Corr. The policies fix
the polarity meanings; their general transport responsibilities do not supply
this native constructor-specific correspondence or its auxiliary lifting law.
This is sharper than “need an edge”: it says what the edge's solution and
evidence interpretation must preserve before shared-row adoption is justified.

## 6. Source/native audit locating that supplier

`candidate_annotation_pair` makes two separate signature calls with shared
symbol/view maps (`candidate_effect.rs:1627–1704`). Its concrete negative-row
branch refuses the input. There is no already emitted same-p_A open-port pair
or actual original-P/slot40 admission from which to obtain Corr. Relaxing the
guard would not by itself construct that pair or an evidence substitution law.

The formal constructor is a useful reference, not the missing theorem:
`candidate_formal_effect_port` allocates one open port for a supported negative
concrete FORMAL row and records the formal parameter, scope, path, source row,
owner, occurrence and I (`candidate_effect.rs:1385–1434`). Its two returned
polar views share the port. RootPermit/NamePermit in the reviewed formal note
derive the licence from OwnsParameter and authentic resolution, with native
owner/path/instance correspondence expressly OPEN. Those hypotheses do not
include a whole-function definition ascription or a projection/lifting theorem
for its checked/exposed result pair. Reusing it as that theorem is invalid.

At p_R, the existing positive-variance signature builder uses a source-owned
view at the result row position; checking and exposed constructions can use
Allowance versus Support, with separate fresh row ports
(`candidate_effect.rs:1941–2004,849–890`). Shared view identity does not prove
actual inflow equality, a residual, B_c=B_e, or independence from the whole
Function's AE/permission dependencies. `candidate_context` Function-port
dependencies and contextual discharge retain actual source/check information
(`:3365–3440,3575–3660`); they cannot be discarded to invoke scalar Q
independence. This report neither identifies Support with real inflow nor
retracts it as a declared-interface operand.

Further physical suppliers remain OPEN after the first gap: actual slot40/41
drain/admission and row owners; result/Name-to-exposed-RE correspondence;
all signed co-parents and qualifying source sets through extrusion/merge;
boundary0 definition capture after source action execution; one actual partial
FreshUse map and restoration of every required bound/evidence; executable
source-local permission/receipt/consumer correspondence. Owners are
`candidate_extrusion.rs:78–340,763–789,856–969`,
`candidate_intrusion.rs:308–386,568–713`, and
`candidate_scheme.rs:755–790,1054–1132,1397–1424,1555–1608,1860–1906`.
The isolated first-use and signed-copy results remain conditional suppliers;
their unannotated/private-closure premises have not been established here.

No native levels/nongeneric changes, physical BoundKeys, admitted pair or
first captured provider map for this fixed source are reported as actual.
Source identity retention and schema algebra are not compiler execution.

## 7. Exact next owner, reuse and freeze receipt

Mutual TODO R60-JOINT-ASCRIPTION-LIFT-1, owner Luna for a DISTINCT source/
constructor theorem allocation: establish the above whole-ascription Corr
from existing selected source typing/annotation contracts, including original
p_A/provider and p_R/permission dependencies. Inputs: fixed source, original
L/t/three positions, raw/checking/exposed Function ports and their exact
source interpretation. Output: explicit source-to-auxiliary lift and reverse
interpretation, or the first owning typed-ascription rule unable to supply it.
Falsifiers: a permitted source solution has no lift; wrong receiver/position
or lost correlated result evidence; permission creates a closed cap/contribution;
the actual paired constructor still admits R59's entrance failure. A proposed
new dependency, code slice or larger source family returns to Luna first.

This is a method change from R59's uncoupled-path falsifier: actual existential
projection/lifting is proved, its auxiliary-preservation reference corrected,
and the exact dependency condition preventing application to the joint source
contract is located. Repeating another scalar join lemma would not discharge
that condition. No equivalent general-induction stage is claimed next.

Reused only within premises: R59 polarity/slots and countermodel limits;
settled permission/allowance/inflow/residual distinctions; original template;
formal source-licence derivation; conditional first-use/signed suppliers.
Rejected: preserving all old auxiliary assignments as the source specification,
using uncoupled equations as S, assuming Q independence, formal-ascription
conflation, row-wide permission, total mu, guard bypass, and scalar repair as
actual native/source preservation. No withdrawn bypass or new semantics.

After the fresh receipt, Luna acknowledged RUNNING before any reads/writes.
Then exact goal/two paths were read and confirmed; contract rev2 and25/25 pins
matched before writes and at freeze. Requested Sol/high; observed UNKNOWN/
UNKNOWN.600 seconds charged, no carryover/expansion; measured duration/CPU/RSS
UNKNOWN. Static source/theory reads and hashing only; no tests/build/parser/
preflight/solver/runtime/probes/instrumentation, code/semantic edits, Git,
external contact, scratch or descendants. Stop at the first joint correspondence
premise, after the finite scalar projection/lift result; no adoption or producer
self-certification. Only the two leased paths were written. STOPPED /
WRITES_STOPPED / NO_DESCENDANTS on frozen hash handoff. Parent OPEN 0→0;
R50 NOT ADOPTED; fresh review and next authority belong to Luna.

Frozen direct dependency manifest follows.

```text
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md
a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
7766aff08cedde1ebc796b8927cd1d44f459df72a632e0c0d35d4bfcd28d335e  notes/theory/2026-10-15-computation-formal-permission-construction.md
09511a51539ca2a14cd7a40d2b9a5da00f72417d1ec5f97a4ba6bfd6ec20c2e1  notes/theory/2026-10-15-computation-freshuse-admission-bridge.md
477ada20e61ce5355601af138b37016ba1a8036e65f4f39627beda2abe062adf  notes/theory/2026-10-15-computation-signed-copy-source-bridge.md
38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895  notes/design/2026-10-10-local-self-recursive-binding.md
a67623a17f6c007ae0660135e3befd0c8d323886ea0fc7f5bc800eadc82bdf9d  notes/progress/2026-10-19-r59-closeout.md
31798df3416e4b9de029124df5eba66abdb430164c826becd337fad43289229b  notes/theory/2026-10-19-r59-negative-function-argument-row.md
b5bd0fe27373fc1d89668bb6357103ea1c5ebed903353d3d31d069e73f879ec7  tasks/agent-loop/inbox/20261019-r59-proof.md
486eff8031c3d0137d39dbb2163b5cc95f72cb73df219c2bbabd74e932424a12  notes/progress/2026-10-19-r59-annotation-constructor-owners.md
a6d0fecd56770e7aa5fd36ea2a6bb1e68f4b72da971ed4ad71e05c2dbd662cd2  tasks/agent-loop/inbox/20261019-r59-implementation.md
155d8817f050566f4a51ccbb82dabb4c809bcabb82654fdce07a6fbaf867fdcc  tasks/agent-loop/sprints/negative-function-argument-row-20261019-r59.md
ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5  crates/yu-hir/src/module/local_source.rs
c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a  crates/yu-hir/src/module.rs
b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f  crates/yu-hir/src/module/source_annotation.rs
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c  crates/yu-solver/src/candidate_source.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278  crates/yu-solver/src/candidate_scheme.rs
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d  crates/yu-solver/src/candidate_extrusion.rs
8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4  crates/yu-solver/src/candidate_intrusion.rs
42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca  crates/yu-solver/src/candidate_context.rs
8738c1b1699228b1a4dfd30af7e03d0afb100ca6124d23037c645246d888dc50  crates/yu-solver/src/candidate_value_graph.rs
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb  crates/yu-solver/src/shadow_apply.rs
2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee  crates/yu-solver/src/lib.rs
```
