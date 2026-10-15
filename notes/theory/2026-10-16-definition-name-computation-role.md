# Definition Name: value reference and introduced computation

Status: independently reviewed constructive source/native correspondence and
partial actual runtime bridge. Empty-cell materialization,
whole typed-runtime adequacy and the original reachability parent remain OPEN.
Baseline: `ab99531a329a9b99008c4d02c2e2c8bb0139faa0`; runtime `35e87f844`.
Authority: initialization correction bundle `1e62dfdc3`; ordinary computation
package's whole-argument introduction/entry laws and runtime charter §21;
top-level inference principles. Sole lease: this new note. No production edits.

Independent review: compiler-referee `runtime_semantic_review` returned CLEAN
at producer SHA-256 `87a1e004dc9cc9db9d46aa166a4ac03c818757de7ed160586c2c9678786ff0d1`.
This closes the stated native Name/Apply and populated-cache role bridge.
It does not derive caller-handler ineligibility from Name purity: a synchronous
initializer may handle requests internally and still return only a Value.
The source-justified execution context for an empty global remains the exact
parent premise; another value/Apply transport lemma cannot supply it.

## 1. Statement, original identities and native conclusion

Fix an authentic LocalSource occurrence u resolved as ModuleDef(d), d's original
stored value root A_d, one actual DefinitionUse(u,d), its original use level,
and one joint source assignment. Let I_d and E_init(d) denote d's initialization
computation and effect separately. Neither initializer purity nor whole-module
source validity is assumed. Preserve d/u, original binding and occurrence
owners, declaration/formal roles, and the original complete argument code.

The source reference computation is the value-reference computation
`Comp(empty, FreshUse_u(A_d))`; for a nongeneric internal SCC use the value root
is shared rather than instantiated. Native checking realizes this directionally:

```text
bottom <: E_u <: empty
internal: A_d <: V_u
incoming: FreshUse_u(A_d) <: V_u
```

This does not equate independently synthesized endpoints. V_u is the original
use's checking row; contextual upper demands may constrain it. FreshUse retains
all reachable value structure, latent function effects and original evidence.
The claim concerns the **evaluation effect of the Name**; it does not declare
all effects inside A_d absent, erase profiles, or make empty profile complete.

When u is the argument of an application, the introduced computation is
Delay(code(u), lexical environment). Computation-formal checking may impose its
own value/effect upper interface on this very computation; it cannot replace
code(u) with code(I_d), identify E_u with E_init(d), or create a second global
indexed by the consumer's expected type. For pending's published Int, this is
a delayed pure Int reference; unresolved initialization remains separate.

These source/native facts are established at the actual constructors below.
The runtime realization is complete for the stored-value Name branch. The
uninitialized global branch is the exact residual, identified in §5 rather
than hidden inside an assumed materialization lemma.

## 2. Actual native Name generation and use admission

`crates/yu-solver/src/candidate_source.rs:942–977` distinguishes Parameter
names with registered Computation role from every other Name. Only that
parameter branch generates FormalNameEffect and later links the entry effect
(:1353–1356). ModuleDef is in the other branch: it emits bottom <: E_u and
E_u <: empty, retains those facts, records PendingDefinitionUse with original
parent/target/u, and schedules Action::Module(u). There is no traversal into
d's initializer at this Name constructor and no effect role inherited from d.
Any successful solution of these ordinary unweighted bounds has E_u empty.

Action::Module at :1370–1377 constructs DefinitionUseId from the collection
artifact and u. It routes either the registered internal/open use or the
incoming use; it does not replace u by an initializer occurrence.

- `lib.rs:15890–15912` validates the internal use and routes the original
  target_root_component to original use_value_component, retaining u/cause.
- `candidate_scheme.rs:1060–1082` captures the stored live **value** root,
  its boundary and actual source frontier. The incoming instantiation at
  :1428–1474 freshens that graph at the original use level, restores its bounds,
  and routes its root to record.use_value_component. The FreshRoute retains
  the use ID, graph and actual remapped rows.
- Graph reconstruction at :1237 onward preserves structural Function slots;
  bound restoration at :1400–1425 transports the original relation, attachment
  bundle and antecedent evidence as FreshUse. It is not initializer execution.
- `lib.rs:16996 onward` admits the directional value constraint with original
  occurrence/cause and retained routed-use provenance, once for that use.

Capture may retain effect rows reachable through the value interface and its
source evidence. That is necessary typed transport. It supplies no assignment
of d's separate evaluation effect to the newly constructed E_u: the route's
consumer is use_value_component, while E_u already has the two original pure
bounds. Stored graph restoration is constraint restoration, not activation of
initializer code or proof of runtime initialization availability.

Thus the actual native source constructor establishes the claimed value/effect
separation independently of whether an implementation later materializes d
correctly. This is stronger evidence than merely knowing that Name is pure in
the older Oracle lowerer.

## 3. Application checking retains that computation

`candidate_source.rs:1011–1051` creates the Apply recipe from the original
callee/argument endpoints and their own effect components. ApplySourceInput
retains the original argument occurrence, owner, checking cause and native
argument value/effect. For u as argument, these are V_u and E_u from §2.
There is no recipe field selecting the initializer as a replacement argument.

`shadow_apply.rs:1553–1599` admits the ordinary negative Function demand:
argument value V_u, argument effect E_u, fresh invocation-effect row and result
checking row. The argument effect is positive in the negative demand, as required
by ordinary Function variance. Comparing it with a Computation formal's declared
interface can check its empty effect against the formal allowance; it adds no
E_init(d) operand. The non-effect experiment branch uses the explicit existing
bottom/empty leaves and also performs no initializer substitution; this note
does not promote that experiment to effect-inference adequacy.

At :1664–1686 the application effect joins callee evaluation and the actual
invocation effect. It does not make the argument's initialization an independent
caller-side prefix. Formal annotation/context/hygiene evidence can constrain
these actual slots and preserve a receiving view; none changes source argument
identity. In particular an effect allowance [signal] is not evidence that a
pure pending:Int Name executes signal's original definition initializer.

## 4. Actual runtime roles, source ownership and result consumers

`runtime/program.rs:349–366` chooses Execute only for a resolved Parameter
whose declared role is Computation; every ModuleDef Name is Observe. Supplied
NameConsumption evidence contradicting that choice is rejected. At :450–455
the Code retains the authentic SourceRootId, occurrence and range; Name retains
the authentic ModuleDef ID. Labels refer to this code rather than a fabricated
Def/Lambda wrapper. An expected consumer never changes this resolution.

`machine.rs:650–673` allocates inert Delay with the **original argument label
and lexical environment** after callee evaluation, before argument execution.
The allocation's diagnostic SourceSite is the application; its executable code
still names the original argument occurrence and its own SourceSite. Allocation
runs no Name prefix and substitutes no definition body. direct_formal_root only
recognizes a Computation Parameter Name, so it cannot invent a ModuleDef root
receipt. The following actual role paths preserve the introduced code:

| Consumer | Actual transition and Name consequence |
| --- | --- |
| Closure Value formal | Execute Delay; evaluate original u; ValueEntry binds the returned value, then enters body. |
| Closure Computation formal | Bind Delay unchanged; receiving.enter may add the authentic formal schema/view/receipt; body starts without running u. A later formal Name Execute runs that Delay. |
| Raw continuation application | ResumeArgument first executes the same Delay for its response; it does not turn u into I_d. Template entry/resume adequacy is its separate gate. |
| Native operation Value port | Execute Delay to obtain payload, create the operation carrier, return from invocation, then declared OperationResultConsumer executes that carrier. |
| Native operation Computation port | Retain Delay as payload; no argument prefix executes at entry. Other payload/handler support gates still apply. |

These are the explicit branches at :675–793. ReceiverReturn and ValueEntry
(:797–831) preserve the returned value/view and use the current invocation;
Name lookup does not reset an owner or restore a lexical maker configuration.
The declared operation result consumer at :649,:765–771 is distinct from Name:
its request is the operation carrier at that original application, after native
return. It cannot justify evaluating a different definition's initializer.
Ordinary closure return has no shape-based recursive execution rule.

At :1556–1588, execute distinguishes Delay (evaluate its retained code) from
Request (emit the original operation event and observations). It does not
recursively execute whatever data a Delay returns. Therefore, for stored
pending:Int, executing Delay(Name pending) returns Int. Passing that computation
to an effect-permitting formal does not create an operation event. If A_d itself
contains a function or computation value, its latent execution needs the actual
separate source consumer; observing ModuleDef alone still does not force it.

For a populated global cell, :449–464 obtains its original ReceivedValue and
calls consume with Observe. consume at :1487–1502 authenticates the view/value,
records the genuine current-owner receipt and returns that same ReceivedValue.
No initializer or latent executable is run by this branch. This closes the
actual stored-Name realization of §1, including its occurrence/view retention.

## 5. Exact operational residual and application to the parent

The very next machine branch (:464–481) handles an empty ModuleDef cell by
installing GlobalRead and evaluating d's original definition body in environment
0 under the current execution configuration. Its Return (:912–927) caches the
value, removes the active initialization marker and only then applies Observe.
Thus **before Observe**, this branch can perform initializer work which the
source-use/native computation in §§1–3 does not license as a Name effect.
The original code inspection, rather than expected formal role, identifies
this exact discrepancy. It is not evidence of a valid whole-source request.

Consequently the following tempting derivation is invalid:

```text
pending : Int
expected argument : Comp([signal],Int)
therefore Delay(Name pending) executes pending's signal initializer
```

Actual Name/Apply construction gives Delay(original pure Name) and leaves the
initializer/root obligation separate. The missing parent premise is which
source-justified materialization rule accounts for an empty global *before*
this pure reference can obtain its published value, with its original effect
and delimiter. Pure Name plus an effectful formal cannot discharge that premise.
No initializer purity, blanket forward rejection, barrier, owner reset, store
copy, publication choice or per-signature global store is adopted here.

The forthcoming Oracle artifact characterization was inspected at hash
0fc04a0f084a9328fdff8d0a6e0f11cc22d381dd7700f14153564d0c3198ebfd:
it reports original pending split into Int-root m3 and consumer Thunk use m5,
with escaped ExprId15 at the later m3 root. It is characterization, explicitly
not original source authority or a proof that consumer specialization may
change global identity. No proof step here assumes its readiness means valid
source admission. The initializer-admission note's projection obstruction also
remains separate; neither artifact repairs the empty-cell bridge automatically.

This packet contributes an unconditional actual source/native role theorem and
its actual populated-cell realization. It identifies one precise unproved
runtime constructor, rather than calling complete runtime correspondence
proved under an invisible cache-availability assumption. The original full
source/runtime and repeated-write reachability parents remain OPEN.

## 6. Frozen inputs, checks and commit packet

```text
candidate_source.rs efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38
candidate_scheme.rs 2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e
shadow_apply.rs 357b274d0de509931bda3015a99b1a1cf2ac86d75a45d230d62ab456c56740ba
yu-solver/lib.rs 199963ac9cd13eebca44c4881b859eeb1f801259cc944bf1d5a57df78dc0c070
runtime/program.rs b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748
runtime/machine.rs e30bb19c54b1a4ee07f3b1d2f0a5e88e57f2226fd055071a6d1ca5f1bdfd5e3a
runtime/receiving.rs 5443c8ca55e58a37b6d003cf5b2985214d37776094f02637adfbe30200cc36bd
ordinary-computation package ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917
runtime charter 547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed
```

Checks: bounded source/authority reads, hashes and artifact whitespace. No
production/test edits, tests/builds/probes, Git mutations, delegation or
measurements. Requested Sol/high; observed runtime model/effort unknown.
Independent review pending; no producer promotion.

Commit packet: sole new path
`notes/theory/2026-10-16-definition-name-computation-role.md`; baseline
ab99531a329a9b99008c4d02c2e2c8bb0139faa0. Suggested checkpoint:
`research: bridge definition Name value role through native demand and Delay`.
Primary shared-record delta: consume the actual pure-Name/directional-value
constructor theorem; leave empty-global Name materialization and original
parent OPEN at machine.rs:464–481. Next action belongs to that initialization
source/control owner, with no inference of a new publication law from expected
argument type or Oracle's per-signature artifact.
