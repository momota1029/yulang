# Identity Parameter: attack on an empty dependency telescope

Date: 2026-10-08
Status: unreviewed conditional research; frozen on submission
Scope: source-constructor inversion for authentic unannotated immutable import-free `my id x=x`
Baseline: `c635ef862289994f446b3fcd66ac617d36013374`, branch `research/simple-sub-intrusion`
Exclusive lease: `notes/progress/2026-10-08-id-sourcebuild-delta-empty-attack.md`
Implementation / semantic selection / gate-closure authority: none

## 1. Objective, method and result

Attack the exact claim `Delta_a=[]`, using the selected Parameter constructor
and the source dependency walk. This lane uses constructor inversion and a
minimal static-dependency discriminator. It does not infer a telescope from
HIR, F5, source spelling, a solver result or the number of templates.

**Result:** the supplied governing sections determine the owner, sort and
pre-challenge placement of `a`, but do not determine its ordered free dependency
manifest. They establish neither `Delta_a=[]` nor an authentic nonempty
`Delta_a` instance for this source. This is underdetermination by the supplied
rules, not a computational undecidability theorem. The full inlet has genuine
registered incidences; their presence does not prove they are free dependencies
of the Parameter declaration, or that the separately named `Delta` is nonempty.

The reduced falsifier is one earlier static dependency edge. It defeats an
inference from eligibility to emptiness at the record/walk level. Its authentic
Parameter introduction remains the exact missing premise; the record pattern
is not presented as an executing source counterexample.

## 2. Fixed authority, dependencies and hypotheses

Use [selected source definition](../design/2026-10-08-source-generalize-definition.md)
§§2–4, [source construction](../theory/2026-10-08-source-generalize-definition-and-proof.md)
§§3.3–3.4,4–5.2, [uniform inlet constructor](../theory/2026-10-08-uniform-value-entry-constructor.md)
§§4.1–4.3,7.1, [identity instance](../theory/2026-10-08-id-sourcebuild-instance-candidate.md)
§§2–3, [transformed export](../theory/2026-10-08-id-transformed-public-export-construction.md)
§§2–4 and [prior owner derivation](2026-10-08-id-sourcebuild-owner-telescope-derivation.md)
§§2–5. Read `rules/research-lab.md`, `rules/design-authority.md` and
`rules/git-concurrency.md`. The prior derivation's missing manifest is a
dependency, rather than a new result claimed here.

H-source remains the authentic Parameter/Lambda/Name/Result/generic-inlet
construction, applicable genuine L1–L5 laws, one valid immutable initial world,
original registrations/actions and absence of a fixed free contract dependency
on `a`. The source is capture-free and nonrecursive, with no annotation,
conversion, installed payload dictionary or executed type-dependent choice.
No selected meaning is changed. These hypotheses do not include emptiness of
the declaration's own telescope.

The owner draft was hash-checked only as the pinned coordination input; it is
not substituted for the selected source rules. Its supplied digest matches
`440e1ef94981ff00ad1515777d3afe5c933f67798619c9369cc0aba67083b9e0`.
Prior pushed conditional notes are identified by the primary as `cb37ae6c7`,
`23697b64b` and `7c10ba7a3`; their contents remain conditional.

## 3. Constructor inversion and the three dependency objects

Inverting uniform §4.1 at actual Parameter `q` yields:

```text
d_a = Desc(C_id,q,ValueEndpoint,sigma_a,Delta_a): a
intr_q = Intrinsic(q,slot,Value-mode,Force-port,registered paths,annotation absence)
I_a = ValueInletSchema(q,a;Delta)
Description(C_id,q) -> I_a and its complete original constraints
```

Exactly one fresh ordinary value description is introduced. Name and body/
outward payloads reference that same declaration; neither creates another
ordinary description. The constructor exposes the symbol `Delta_a` without
an equation computing its members for this authentic introduction.

| Object | Fixed meaning | Consequence for emptiness |
| --- | --- | --- |
| `Delta_a` | Parameter declaration's original free dependency telescope at `sigma_a`, source §3.3. | Its membership needs the actual declaration formation operands and incidences. |
| Full inlet `Delta` | Already introduced incident source/profile/guarantee/scope/residual/dependency operands, uniform §4.1; `Intrinsic` registrations are separately retained. | Neither `Delta_a=Delta` nor `Delta_a=Intrinsic` is supplied. Registered inlet fields cannot be silently deleted. |
| Checked witness `gamma` | `J,kappa_J,carrier_J,mu_result,original_port_map,delta_static,delta_check,current_guards`, uniform §4.2, at its actual argument/check/event scopes. | Later argument contracts, receipt tokens, observations, responses and result tuples cannot become pre-challenge free dependencies of `a`. |

Uniform §4.3 partitions constraint **proofs** by their original operand scopes.
For bare id it projects intrinsic role/consumer equations, registered image
equalities and complete J/context world/authority/raw/future premises. This
proves the actual inlet constraints at their scopes. It neither enumerates
`Delta_a` nor promotes those later proof operands to that telescope. Even a
nonempty `gamma` therefore supplies no witness against `Delta_a=[]`.

Source §3.4 permits a strategy to use only its original preceding dependencies.
Thus every actual dependency of `a` must be available at `sigma_a`; later `h`
and fields introduced beneath `h` are excluded. Absence of imports/annotations/
operators removes those possible source suppliers. It does not establish
absence of every earlier registration, scope or initial-world operand from
the declaration's own formation.

## 4. Minimized dependency attack and its exact limit

Let `s:tau_s` stand for one independently supplied, already introduced static
scope/incidence operand of the authentic formation. Its actual type and owner
must be supplied; the symbol creates neither a new source binder nor a new
language rule. Compare the following **candidate owner outputs**:

```text
M0: Desc(C_id,q,ValueEndpoint,sigma_a,[]): a
M1: Desc(C_id,q,ValueEndpoint,sigma_a,[s:tau_s]): a
    d_a --original free dependency--> s
```

Keep the same source, raw generic provider, empty captures, one description,
intrinsic registrations and all inlet/body/result equations. Only the
declaration's proposed outgoing dependency differs. M1 is conditional on the
authentic Parameter law using `s` as a free operand of the declaration, rather
than solely recording it in the surrounding schema. Merely finding `s` in
`IF0`, `Delta`, a constraint or the parent scope does not establish this edge.
Neither candidate is certified as the authentic owner output by these texts.

The dependency walk distinguishes two directions:

```text
d_a depends on fixed s          does not imply that fixing s fixes d_a
fixed contract depends on a     does mark d_a fixed by source §5.1 rule 2
```

Under M1, fix reaches `s` and its dependent fields, with no free `a` there.
Retain reaches `d_a` through Description/Internal. No walk rule takes an
inverse edge from fixed `s` to every declaration that depends on `s`.
Consequently an authentically supplied M1 can remain eligible with its
original `[s]` telescope; §5.1 rule 5 explicitly retains eligible declarations
with all dependencies. Uniform §7.1's no-free-`a` result for the raw provider
also concerns the second direction. It does not prove the first edge absent.

This is the smallest additional record pattern attacking the shortcut:
one declaration, one earlier typed operand and one dependency edge. Removing
the operand/edge restores emptiness. Replacing it with `gamma` or a returned
value makes the telescope ill-scoped. Reversing it to a fixed contract's free
dependency on `a` violates H-source and changes eligibility, so it is not a
counterexample within the assigned hypotheses.

**Bounded characterization:** these record/walk clauses do not prohibit a
genuine outgoing static dependency while preserving eligibility. This is
not a proof that M1 is realized by the selected authentic Parameter law.
There is no minimized running source witness against emptiness in this lane.

## 5. Exact missing premise, claim classes and stop

The discriminating missing premise is an authentic Parameter formation
instance for `q`, giving the complete ordered free-operand manifest of
`Desc(C_id,q,ValueEndpoint,sigma_a,Delta_a)`, with each target's type, owning
introduction, parent incidence and the local formation clause that uses it.
It must distinguish a free operand of the declaration from a surrounding
schema operand. The type-scope record alone does not make every ancestor a
dependency; a guessed empty list does not prove their absence.

**Conditional theorem:** if that complete authentic manifest contains no free
operand, `Delta_a=[]` follows from the selected meaning of `Desc`. If it
contains a genuine pre-`sigma_a` operand `s`, `Delta_a` is nonempty while
eligibility can remain intact when H-source holds. Both implications require
the owning formation premise; neither establishes which case bare id has.

**Established dependencies:** the selected Generalize construction and uniform
inlet results retain their recorded reviewed scopes. This producer supplies
no independent review of them. **Candidate assumptions:** M0 and M1 are
discriminators awaiting authentic owner evidence. **This result:** unreviewed
conditional inversion and record-level characterization, with no gate closure.

Stop here. The previous owner derivation and this distinct dependency-direction
attack leave the same authentic Parameter free-operand premise untouched.
A further graph probe, larger finite enumeration or another fix-walk proof
would assume that premise. Recommended next action: obtain the owning
Parameter formation's typed free-operand manifest for this exact source,
then inspect the zero-edge/one-static-edge discriminator against that output.
This asks for source evidence, not a new semantic choice or permission to
implement compiler changes under the research lease.

## 6. Independence, coverage, commands and resources

The reference is the selected source-constructor text; no executable oracle
was created. The graph attack shares its classification and dependency-walk
rules with that reference, so it provides no independent proof of those
source rules. Authentic ownership and free-incidence evidence are not supplied
by accepting either candidate graph. No checker assuming M0/M1 would improve
that independence.

Coverage is exactly the assigned id Parameter declaration and its original
pre-challenge dependency question. The named structural mutations are removal
of the one static edge, replacement with a later gamma operand and reversal
to a fixed contract's dependency on `a`; they were reasoned through, not run.
Seeds/ranges/process samples: none. No enumeration, code, tests, builds,
performance measurement or child delegation occurred. Resource use was
lightweight documentary shell reads and a single leased-note write; peak RAM,
CPU time and wall time were not instrumented.

Commands already run: bounded `cat`, `rg -n` and `sed -n` reads of governing
texts; `sha256sum` of the seven direct inputs below. An initial read-only
`git rev-parse HEAD`, `git branch --show-current` and `git status --short`
confirmed the supplied baseline/branch and concurrent files. This exceeded the
packet's no-Git command budget; no Git mutation occurred and no further Git
command was used. Concurrent owner draft and pending question paths were
untouched. Final dependency byte recheck is recorded on submission; comparison
with the pinned committed tree remains the primary's integration check.

Unverified: actual nonempty/empty Parameter manifest; source-to-compiler
correspondence; complete inlet/IF0 serialization; arbitrary source families,
State/foreign/local laws, Generalize reproof, public evidence-fiber and query
recognition gates. Failure conditions are a changed governing dependency,
an authentic manifest contradicting a candidate, a later field used before
its binder, an omitted original dependency, or promoting this record pattern
to an actual source counterexample without its owning rule.

## 7. Dependency snapshot and commit packet

SHA-256 values observed before writing:

```text
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38  notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240  notes/theory/2026-10-08-source-generalize-definition-and-proof.md
273e8dae447e9997d586fc07abf48883c76b90988c8906094dd428a48339c2e5  notes/theory/2026-10-08-uniform-value-entry-constructor.md
5b7d468bbe32fdded65b3c6e90f00a231ac7b9fca05cfd1ca9924f3468f890b9  notes/theory/2026-10-08-id-sourcebuild-instance-candidate.md
5b3d8569da0fa422921d28814dbb734323dabd7ccaca03f0aa5001746d2e1641  notes/theory/2026-10-08-id-transformed-public-export-construction.md
de7e6db348ee460e5c6bf530223878a28efcb561984e73ca8b62aaa7f927d729  notes/progress/2026-10-08-id-sourcebuild-owner-telescope-derivation.md
440e1ef94981ff00ad1515777d3afe5c933f67798619c9369cc0aba67083b9e0  notes/design/2026-10-08-id-sourcebuild-owner-design.md
```

- Exact leased/changed path: `notes/progress/2026-10-08-id-sourcebuild-delta-empty-attack.md`.
- Baseline: `c635ef862289994f446b3fcd66ac617d36013374`.
- Changed dependency hashes: none written by this lane; final observed-byte
  recheck accompanies submission. Pinned-tree comparison is left for primary.
- Review status: unreviewed conditional research, frozen at submission; no
  independent certification or source/gate-completion claim.
- Checks already run: governing-text inversion, bounded structural mutation
  reasoning and direct input hashes; no executable semantic check or test.
- Proposed commit message: `research: isolate the missing id Parameter emptiness premise`.
- Shared-record deltas intentionally deferred: primary/curator may record that
  eligibility does not imply an empty declaration telescope; no authentic
  nonempty id witness was obtained; the exact Parameter free-operand manifest
  remains required. No task/index/authority/theory-map/question file was edited.
- Writes stop before frozen review; any repair requires a renewed lease.
