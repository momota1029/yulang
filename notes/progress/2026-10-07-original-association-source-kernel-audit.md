# Original association: bounded source/kernel clause audit

Date: 2026-10-07
Baseline: `1777ccec8369915ad2829f324e3e6d6dd08f697c`
Branch inspected: `research/simple-sub-intrusion`
Status: frozen, independently spec-audited research-only characterization; no findings
Claim class: bounded source-rule characterization and conditional last-rule derivation
Review: spec_auditor PASS on SHA-256 `69219873dd13a4a43112251b5efb5d54a3348e35d85872b4dfbf4bd343ed8c95`; scope is exact conformance of displayed source/kernel clauses and boundedness of the absence claim
Exclusive lease: this note only
Semantic/implementation authority: none

## Objective, method and exact target

Audit the assigned source clauses for a constructor that types a **complete
invocation contribution** and associates it with an original static
signature slot before pending comparison `Q`, for exactly

```text
my apply f = { my step x = f x; step }
```

The method is clause-by-clause input/output sort analysis and last-rule
inversion. It does not inspect Rust, Frozen Oracle code, or an executable
model. The selected sequential Bind, final function return and capture of the
same outer `f` are fixed inputs, not alternatives reconsidered by this audit.

Use the target notation from the assigned composition §4:

```text
OriginalAssocType_X(beta,p,j_call; s,c)
```

Here `j_call` is the rooted complete invocation expression; `s` is an original
static signature slot; `c` is an original complete contribution witness/contract.
The incidence can be recorded as `(beta,p,s,c)`; the composition writes the
same fields as `(beta,s,p,c)`. Neither field order creates an interpretation.
The source computation metavariable called `c` in typed-core grammar is a
different sort; below it is called `c_expr` to avoid that accidental cast.

**Result.** The inspected clauses generate a source/consumer skeleton and,
under their independently typed inputs, a complete Call expression/image and
transported profile incidence. No displayed clause in the exact inventory
below introduces or interprets the pair `(s,c)` as associated with that Call
operand. This is a bounded result about those clauses, not a whole-repository
absence claim, an impossibility theorem, a source counterexample, or a claim
that the selected language meaning needs another user decision.

## Authority and hypotheses

The authority order is [design authority](../../rules/design-authority.md).
[FVIEW](../design/2026-10-05-inferred-function-call-views.md) and the
[nested addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
are Authoritative within their declared scopes. FVIEW explicitly says it
does not supply completed typing/inference rules (lines 12–15).
[Directional](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
records the current explicit user direction; its formalization remains Draft.
[Typed core](../design/2026-10-02-typed-computation-core-elaboration.md),
[typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md), and
[source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
are conditional research constructions, not newly adopted source rules.

All statements retain one original candidate row `X`, its
`xi=(nu,K,D)`, binder scopes, source identities and provider/environment
dependencies. No satisfying row, completed profile or admitted context is
selected to manufacture the association. Formation/admission remains
independent of `Q`; upper-origin evidence and lower/provider evidence remain
distinct, with no reverse protection from the former to the latter.

Three hypothesis levels are kept separate:

1. `H_shape`: exact selected syntax interpretation, lexical resolution,
   source annotation absence and generated ordinary source tags/endpoints.
   This gives symbolic obligations and an inert closure/Bind/return skeleton.
2. `H_typed`: a finite ordinary derivation with the source interfaces,
   complete callable interpretation, typed paths/profiles, owners and shared
   dependencies required by typed-core §§2–3/6/9 and typed-boundary §6.
   This is not an existence theorem for the raw source.
3. `H_root`: independently interpreted descriptor and active kernel clauses,
   local descriptor typing lemmas, exhaustive source membership/admission
   inventory and certified transport from source-contract §§2.2–3.
   Any original association included in these supplied clauses is an input
   to the conditional realization theorem, not its newly constructed result.

For the negative localization, none of these supplied inputs is silently
extended with the target association or a conversion from a profile/Call
expression to `(s,c)`. If such a clause is supplied, the localization must be
revisited at that clause.

## Clause inventory: formation and source identity

Locators below name the inspected sections and numbered source lines at the
pinned baseline. The table records outputs, not only occurrences of the
words “slot” or “contribution.”

| Clause / exact locator | Consumed input sorts | Produced or required output sorts | Association consequence |
| --- | --- | --- | --- |
| FVIEW §1.1, lines 49–82 | Written contract/holes, inferred scheme, internal view/evidence | Distinct annotation, public-scheme and internal-evidence layers | A written arrow or inferred printed arrow is not a definition of `c`. |
| FVIEW §2, lines 92–102 | Relevant declarations/definitions/uses/component; source position and its contract | One shared role-indexed contract; stable `beta`, `Slots(beta)` and retained annotation/scope identity | Specifies stable identity and preservation; supplies no clause typing a member `s` together with a complete invocation `c`. |
| FVIEW §2, lines 104–114 | Source resolution and typed Name/capture/receipt/Call elaboration; one original `nu,K,D` | Required paths/Flow, ownership/receiver relationships and independent admission | Explicitly states the exact constructing judgments remain open; success of `Q` cannot be the producer. |
| FVIEW §3, lines 118–134 | Unannotated formal/use pattern and ordinary-value use evidence | Selected protected internal seed and scoped `NonHandlerFormal` refinement on one relationship | Not actual provider role/entry, not a generic Value-entry-implies-Pure rule, and not contribution typing. |
| FVIEW §4, lines 138–151 | Actual annotation occurrence/current endpoint; retained local evidence | Scoped `io` removal permission; direct boundary comparison and target export retaining evidence | The rule relating permission to its particular contribution remains to be specified. A permitted boundary comparison is not success of pending `Q` and is not a construction of an unannotated `(s,c)`. |
| FVIEW §5, lines 158–184 | Required future source generation/proof work | Construction/preservation of contract, slots, paths, owner/receiver incidence, annotation association and admission is demanded | An obligation list supplies no inference-rule head. Existing decorated-context theorems retain their premises. |
| Nested §§1–2, lines 19–70 | Exact candidate and one-parameter header expansion | Sequential Bind; final `step` value; resolved outer `f`, inner `x`; lexical capture; displayed Lambda/Call core shape | Fixes source identity and observable capture. It gives no new call-view registration or `(s,c)` interpretation. |
| Nested §3, lines 74–88 | Same selected interpretation | Preservation of existing callback, entry, boundary/protection and joint-evidence decisions | Effect execution, handler selection, recursive groups and general local polymorphism are outside this decision. |
| Directional §2 and §3, lines 40–105 | `ProtectedVarAt(k,v,sigma,u)` and original `SourceUpperUse(u,v,U,sigma)` | `NewProtection(k,u,outEff(U))` on that upper occurrence | Constructs a protection conclusion given an exposure; no membership, receipt, complete invocation contract or lower/provider backflow follows. |
| Directional §4, lines 115–132 | Original formal/shared root and exposure witness | Optional proof index `(k,beta,u,sigma,outEff(U))`; retained upper/lower occurrence distinctions | Upper-use count is not `Slots(beta)` cardinality; the index does not type `s` or `c`. |

## Clause inventory: computation, active kernel and transport

| Clause / exact locator | Consumed input sorts | Produced or required output sorts | Association consequence |
| --- | --- | --- | --- |
| Typed-core §2, lines 57–85 | Finite source derivation, roles/entry/result ports, annotation positions, typed paths/Flow/receipts, handler declarations and joint `nu,K,D` | Judgments `Value(A)` and `Comp(E,A)` over the supplied decorated derivation | Declarative input is already typed/decorated. `Comp(E,A)` does not define the separate original contribution-contract sort. |
| Typed-core §3 Name/Lambda/Reify, lines 117–135 | Lexical value references and typed evidence; child derivations | `V[name x]=lookup(x)`, inert Closure/Delay; `X[result(d)]=Return(V[d])` | Lookup can preserve an association present in the environment; it does not originate one. Closure creation executes no latent Call. |
| Typed-core §3 Bind/Call, lines 131–171 | Callee computation, inert whole argument, actual callable entry/definition/result consumer | Ordered rebind and complete `X[cf] >>= (f -> ExecuteCallable(f,Delay(X[ca])))` with receiver/receipt | Types/translates the ordinary invocation under supplied premises; no signature-contribution introduction is displayed. Receipt is not the target static slot. |
| Typed-core §6 parameter table, lines 337–379 | Ordinary parameter syntax and admitted annotations/typed-flow premises | Fresh Value endpoint or retained Computation tag; finite binder/receipt/entry skeleton and coherent renaming | The unannotated formal binds `Value(A_f)`; outer parameter entry alone does not determine nested original paths or profiles. |
| Typed-core §6 Name/Lambda/Bind, lines 396–410 | Known `Gamma` and child interfaces | Name copies `Gamma(x)`; Lambda has `Value(Fun(P,Result(I_b)))`; Bind installs `Value(A_r)` | Produces source result roles and shared lexical roots. These are not complete-call schemes or an original association rule. |
| Typed-core §6 application, lines 402 and 412–423 | Child normalized derivations; existing complete invocation and whole-argument/path/contract obligations | Symbolic `Computation(E_call,A_call)` and `reify(call(n_f,n_a))`, normalized for consumption | This is the available complete-call computation judgment. Its endpoint obligations consume the original interpretation; no conversion to the target `c` is defined here. |
| Typed-core §6 transport, lines 469–506 | Admissible endpoint substitution consistently renaming typed binders/paths and retaining typing/source tags | `Result`/`Normalize` commute; skeleton and matching `K,D` transport | Preservation can carry supplied associations. It cannot discharge an unproved typing premise or manufacture their interpretation. |
| Typed-core §9, lines 918–996 | Whole `J_arg`, original provider/entry/environment/current configuration | Complete relational `J_call` including entry, typed rebind, body, result consumer and native delimiters | Distinguishes `J_call` from `J_body`; a complete image exists conditionally. The symbolic image remains an inference obligation. |
| Typed-core §9, lines 1000–1083 and 1087–1121 | Resolved typed interface graph, shared nodes, original complete challenge domains/observations | Typed interaction directions and conditional whole-domain/whole-observation containment | Direction propagation retains original slots; it creates neither them nor grants. Complete symbolic invocation/challenge presentation remains open. |
| Source-contract §2.2, lines 109–142 | Already presented `M_E,A_E`, independently interpreted `DescMem`, retained incidences and binder environment | Complete constrained-root membership/admission interpreted jointly at the original incidences | Semantically active incidence is a hypothesis, not a generation rule. Independent local typing must prove `DescMem`; labels or four Function children cannot supply it. |
| Source-contract §§3.1–3.2, lines 148–204 | Decorated graph already supplying roles/entry/paths/owners/receipts/resumptions/consumers and original tuple | Required original Name root, inert closure capture, Result/Bind, and complete Call relation with whole argument/receiver/entry/body/consumer/return | Specifies required relation content and exhaustive accounting, conditional on the decorated source and primitive typing. It gives no displayed `(s,c)` interpretation. |
| Source-contract §3.3, lines 208–222 | Source-typed initial punctured context, typed responses/raw resumptions and future uses at original ports | Independent admitted histories, including divergence and arbitrary finite developments | Source-typed slot/provider/path are admission premises; admission is not reconstructed from `Q` or a successful return. |
| Source-contract §3.4, lines 226–239 | Already certified freshening/graft/equivalence/fresh definitions/joint hiding and known literal B boundary | Original-scope whole transport and fresh use, keeping all `K,D` incidences joint | Does not generate an original missing incidence. Known-context B is not a rule for constructing this unknown formal's original association. |
| Source-contract §§3.5–3.6, lines 243–280 | §2 interpretation, local descriptor lemmas and exhaustive §§3.1–3.4 conformance certificate | Bidirectional source-base membership/admission correspondence and finite syntactic conformance checking | Reverse induction requires original typing and exhaustive last-rule accounting; it cannot supply the missing local lemma as its own premise. |
| Source-contract §3.7, lines 295–338 and 363–408 | Whole source base/envelope plus independently interpreted/certified `W,Z`, admission and transport | Conditional positive production abstraction including unanchored extras | `W,Z` are unselected hypotheses; this is not a source-only membership policy and is no current association producer. |
| Source-contract §6.1, lines 724–752 | Independent finite source typing retaining non-coverage kernel/binder tree | Conservative allowance obligations for Call callee evaluation and complete receiver output, including hygiene | Retains the non-coverage kernel; allowance coverage does not construct it or type the original `(s,c)`. These allowance clauses are candidate assumptions. |
| Source-contract §§8–10, lines 948–1013 | Stated form/interface/scope and abstraction premises | Bounded applicability, explicit independence failures and remaining source/production obligations | No all-source, resolver-completeness or production claim follows. No rejection or semantic adoption is inferred from a failed certificate. |
| Typed-boundary §6 introduction, lines 669–700 | Fixed finite ownership/signature descriptors, assignment and source-elaborated profile | View `(v,t,e)`, dynamic boundary `b=(r,a,Gamma,endpoints)` at applicable positions | Introduces a dynamic boundary from a supplied profile; deriving all profiles is explicitly outside this rule. Signature position `t`, callback binding `a` and static `s` are not identified by a clause here. |
| Typed-boundary §6 image, lines 704–790 | Tagged typed maps `M_i`, source packets `(v,t,chi,K,D,L)` | Indexed profile/dependency image; shared `K` and inherited `L`; binding/capture/read/result/projection correspondences | Transport preserves the exact input witness/domain and creates no original contribution interpretation. Equality of values/families is not a map. |
| Typed-boundary §6 observation, lines 794–868 | Actual typed binding receipt, executing CallView/Observe, matching profile/Flow and current owner/receiver/handler activity | `Receive`, `Path`, `Inc_C`, candidate protection, local `Grant` and visibility | These are dynamic event/use/activity conclusions. A callee's own invocation is not automatically a recipient of its callee view; no static `(s,c)` follows from an event. |
| Typed-boundary §6 theorem/boundary, lines 872–1027 | Typed maps and input witnesses, equal route/receipt/observation context, exact activity and supplied re-entry owners | Image composition, no authority creation, depth/lifetime preservation and finite conditional territory query | Inverting image membership returns an input profile and path witness. Complete source profiles/correspondences/re-entry ownership and source safety/principality remain separate premises/gates. |

The assigned [composition](2026-10-07-source-view-to-original-attachment-composition.md)
§§3–4, lines 100–236, is a research dependency, not an original source clause.
Its stronger reached-transition envelope already joins the complete Call
operand to the exact captured callee read and transports the upper profile.
This audit does not repeat that composition proof. It checks its missing
output against the original clauses above. Likewise, the assigned
[minimal-clause note](2026-10-06-main-source-generation-minimal-clause.md)
§§5–6, lines 241–363, explicitly labels `U_c` and `Foot_S` as needed
interpretations. Naming either obligation supplies no definition of `(s,c)`.

## Derivation on the exact candidate and reverse boundary

Under `H_shape`, let the resolved binders be `d_f,d_x,d_step` and their uses
`u_f,u_x,u_step`. The nested addendum fixes these resolutions and `f` capture.
Typed-core §6 gives

```text
Gamma(d_f)=Value(A_f), Gamma(d_x)=Value(A_x)
n_f=result(name f), n_x=result(name x)
Result(I_x)=Comp(empty,A_x)
I_fx=Computation(E_fx,A_fx)
step body/result skeleton=Fun(Value(A_x),Comp(E_fx,A_fx))
```

The last equation is a body/result skeleton with retained Call obligations.
The `empty` belongs to this rebound ordinary Name result, not to the whole
external argument carrier entering `step` or to every provider passed to `f`.
Sequential Bind returns the local closure value without invoking its body.
Neither this derivation nor the approved capture adds a Handler activation.

Under the stronger `H_typed`, §§3/9 construct the invocation operand

```text
j_call = J_f >>= (actual_f ->
           ExecuteCallable_X(actual_f,Delay(J_x); environment,current_state))
```

with the whole receiver entry/body/result-consumer behavior and original
dependencies. The directional rule gives protection at the separately
justified upper `outEff(U)`. Typed-boundary can transport a supplied applicable
profile through typed result/capture/read maps and, if reached and observed,
derive dynamic event incidence. These are concrete antecedents for a possible
association interpretation, but none is an interpretation of `s,c`.

**Restricted last-rule proposition.** Let `R` be the displayed formation,
ordinary constructor, transport and inverse-certificate clauses in the two
tables, with exactly their stated premise sorts. Do not add an implicit sort
conversion, an opaque local lemma whose conclusion is the target, or an
association already carried by `Gamma`/the active kernel. A finite derivation
using `R` from inputs without `OriginalAssocType_X` has no newly introduced
`OriginalAssocType_X(beta,p,j_call;s,c)` conclusion.

Proof: inspect the last clause. Formation/Name/Lambda/Bind/Call/Normalize
conclude source interfaces, constructor obligations or computation images;
directional introduction concludes upper protection; boundary introduction
concludes a profile-bearing dynamic view; transport concludes an image with
the original input witness; receipt/Observe/Path/Inc conclude event/use
relations; constrained-root interpretation consumes `M_E,A_E,DescMem`;
realization/renaming certificates conclude correspondence or preservation
of those already interpreted predicates. None has the target conclusion or
a displayed conversion to its pair of output sorts. Recurse through a
preservation clause until its input witness is reached. If that witness
already carries the target, the conclusion reuses the premise, contrary to
the proposed new introduction. The finite derivation assumption ensures
this last-rule descent terminates; recursive source references reuse roots
and do not add another rule head. This proves the restricted proposition.

This is syntactic localization over `R`, not a theorem that an independent
original kernel could never give the same coordinates an association
interpretation. Such an interpretation requires its own stated rule or lemma.

| Attempted reverse route | What inversion can recover | Precise remaining premise |
| --- | --- | --- |
| Invert typed-core Call or `Comp(E_fx,A_fx)` | Callee/whole-argument typing premises, complete receiver image and retained constraints | A lemma interpreting this complete image as the original contribution contract and identifying its static slot |
| Invert `chi_out=M_*chi_in` | Original profile position/boundary witness and matching typed correspondence | The original contribution-contract association, not implied by an effect-profile position |
| Invert `Path`/`Inc_C` | Actual Observe/receipt/Flow and current activity witnesses | Static association/source licensing; event occurrence is not an exhaustive source-incidence inventory |
| Invert C-realization | A source constructor under supplied local `DescMem` typing and exhaustive original membership/admission clauses | Those independent original clauses/local lemmas themselves; assuming their association content cannot prove its source introduction |

Consequently neither attachment soundness nor exhaustive origin/licensing
inversion is discharged. The exact blocker is the independent interpretation
and source introduction converting the complete Call operand plus its upper
profile/source incidence into original `s,c` on the same `X`. It persists even
if all the relevant receipt/result/capture/read transitions occur.

## Independence, coverage and stopping conditions

This audit's evidential oracle is the pinned text of the assigned clauses.
There is no Frozen Oracle, independent semantic implementation, random
generator or supplied transition checker. It shares the primary's selected
source meaning and the research clauses' explicitly supplied typing/profile/
admission hypotheses. Its independence is a new direct source-clause audit;
it is not independent review of this producer artifact or a claim of a new
semantic oracle. A checker instantiated with an association rule could
establish consistency relative to that rule, not prove that the source
clauses authorize it.

Coverage is exactly FVIEW §§1.1–5; source-contract §§2.2, 3 including 3.7,
6.1, 8–10; typed-core §§2–3, 6, 9; typed-boundary §6; nested §§1–3;
directional §§2–4; composition §§3–4; minimal-clause §§5–6. Initial combined
captures truncated; all decisive sections were reread in bounded numbered
windows. Navigation reads of `tasks/current.md`, `tasks/research-lab.md` and
the index are not semantic premises. No entire-repository absence search
was performed. Seeds/ranges and mutation counts: not applicable; no
enumeration or executable experiment was run.

The restricted result fails to apply if an independently interpreted original
kernel clause outside this inventory introduces the target, if a local typing
lemma in the consumed premises already proves the required conversion, or if
the inspected text changes to supply it. Its operational consequences also
fail outside the supplied typed-profile/entry/owner/admission envelope; this
is not a new rejection policy. Unknown shapes, general annotations, recursive
generalized-interface discharge, every source/capture/value interface,
complete initial/all-world admission, complete profiles/nonempty original
rows, Option A/2 production membership, full soundness, principality and
source adequacy remain unverified.

Claim classes: the exact nested meaning, shared-contract direction, Q
independence and absence of lower backflow are retained selected source
decisions. Active-kernel interpretation, local descriptor typing and the
allocation/abstraction clauses are explicit candidate or supplied hypotheses.
The restricted last-rule proposition is a conditional derivation over the
listed inventory. The absence of a displayed introduction there is a bounded
characterization; it establishes no new full source theorem or theorem-graph edge.

Stop condition reached: all assigned original-rule sections have been
inventoried, and no constructor of the required association output was found
in them. More image composition, larger toy cases or another event witness
would leave this precise premise untouched. One recommended next action:
the primary should locate and pin the original kernel's independent complete
contribution/slot interpretation, then assign a derivation of its Name/Call
introduction and both origin-inversion directions on this same `X`; if no
such clause is available, retain this exact premise as the blocker without
promoting a candidate definition or reopening the selected source meaning.

## Checks, resources and frozen dependencies

Read-only commands: `git rev-parse HEAD`, `git branch --show-current`,
`git status --short`, bounded `cat`, `rg --files`, `rg -n`, and numbered
`sed -n` reads. Python SHA-256/byte comparison with
`git show 1777ccec8369915ad2829f324e3e6d6dd08f697c:<path>` confirms each
dependency below equals the pinned revision, before writing and at handoff.
Note-local relative-link/whitespace inspection and `git diff --check` on the
leased path are artifact integrity checks, not semantic tests.

One leased output; zero compiler/Rust edits, tests, builds, Cargo, Oracle,
checkers, Git mutations, interactive questions or children. At most six
concurrent lightweight read commands were used; no heavy processes or search
shards. No numeric CPU, RAM or wall-time budget was assigned. CPU time, peak
RSS and elapsed wall time were not instrumented. No claims depend on an
unfinished compute run or omitted search shard.

| Dependency | SHA-256 at baseline |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/progress/2026-10-07-source-view-to-original-attachment-composition.md` | `a6f8d13d1911ebfaa1b41c60485eab1b303c4f34a661bafca0b742d30418f946` |
| `notes/progress/2026-10-06-main-source-generation-minimal-clause.md` | `495aceda697cef317f27be0375423246d9b2c7a341ea81a2bbf8df6e28910b4e` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-07-original-association-source-kernel-audit.md`.
- Baseline SHA: `1777ccec8369915ad2829f324e3e6d6dd08f697c`.
- Changed dependency hashes: none; the table pins every direct premise.
- Claim/review status: spec-auditor PASS, no findings in the bounded audit and
  conditional last-rule derivation; no theorem/gate closure.
- Checks already run: exact assigned section reads; baseline byte/hash
  equality; leased-note link/whitespace inspection; leased-path diff check.
- Proposed one-line commit message: `research: audit original contribution association source clauses`.
- Shared-record deltas left for primary/curator: optionally link this bounded
  inventory and its exact association-interpretation premise in
  `tasks/current.md` and the original-attachment theory record after adjudication;
  no authority/index status promotion or completed proof edge is proposed.
