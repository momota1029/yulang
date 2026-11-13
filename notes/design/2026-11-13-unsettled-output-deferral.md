# Unsettled outputs: head provenance and the remaining termination budget

Status: **Draft implementation; proved conditional termination reduction.**
Date: 2026-11-13. Scope: an additive relation on the existing
`GeneralNominalSupport.Tracked` carrier. Full B4(1) remains open.

Authority: [spec §6, decision of 2026-11-13](../../spec/06-roles.md),
“片付いていない impl の出力を根拠にした展開は保留する”, and
[B4 draft addendum 7](2026-11-08-b4-main-statement-draft.md).
This applies the owner's lazy choice to the
[fresh-analysis pump](2026-11-13-termination-fresh-analysis.md).
The earlier note's owner question is answered; its infinite schedule concerns
the older value relation, not the relation defined here.

## Result and limits

The new guard excludes unfinished packets' output equations from head
explanations, even when ordinary refresh has already recorded their consequences.
It checks the provenance of captured input observations as well as output facts.
It preserves the full ordinary journal, merging, and K2. The old pump's first
recursive child is blocked by a scalar cut model on paper. Lean proves this
blocking result with explicit finite-prefix and inspection certificates; it
does not construct the actual P/E/W prefix. Lean also proves accessibility from
a finite future-signature cover, using a concrete missing-fact measure. The
source-derived cover is not proved. No new infinite trace has been established.
Neither unconditional termination nor a complete implementation of resumption
is claimed.

## 1. Settlement on the existing carrier

`Settled s d` is the existing inductive `Discharged s d`. Its constructors are:

1. An installed packet for d whose every emitted where-child is settled.
2. Transport from a settled occurrence through the state's same-input alias
   relation, with both sites retained in the state.

Because this is inductive, a cycle of unfinished where-children is not a
settlement proof. Children that are pending, ambiguous, or rejected have no
completed dictionary and do not settle their parent by this rule. Nominal bodies
are never inspected.

An output fact refers to an **exact packet**, including its capture and children.
Define `PacketSettled s p` by p being installed and every member of p.children
being settled. Define `Unsettled s p` by p being installed and at least one child
not being settled. For installed p these are complements (classical logic).
Packet settlement implies settlement of its occurrence. The converse is not
used: an older packet, or an alias, might settle the occurrence without settling
a different packet's current children. This prevents authorizing every historical
output solely because one packet for its occurrence completed.

`settled_monotone` proves preservation under every new transition, using packet
and alias retention. No new settlement field or fuel is inserted into formation.

## 2. Two model sets, and an additive Step

Ordinary constraints continue to use `Models state.current`, exactly as before.
In particular, every installed output equation remains there. This includes
equations of unfinished packets, and their consequences obtained by ordinary
equating or refresh. They remain available for same-input merging and K2.

Head explanations instead use finite lists `facts` and the predicate

```text
ExplanationModels(state, facts, M) =
  SourceModels(state.source, M) and every fact in facts holds in M.
```

`Trusted state facts` is an inductive derivation:

- Start with the empty list and the original source constraints.
- Add an installed input fact only after `Readback`: every exact observation
  at an inspected slot of that packet follows from the preceding explanation.
- Add an installed output fact only when that exact packet is settled and its
  input fact already occurs in the explanation.
- Add an installed merge fact when equal inputs have a preceding explanation.
  Both original sites' `SiteHolds` must also follow from that explanation:
  retained actual origins must exist and fit their occurrence intervals, without
  borrowing these facts from the full journal. The participants themselves need
  not be settled. Missing retained origins may
  be recovered as point endpoints, but equality of those endpoints must follow
  from the preceding explanation. The recovery snapshot is retained in the
  certificate, so future refreshes do not change its meaning.

Membership in the full historical ledger is required for each added fact.
Support labels alone confer no authority. The induction proves
`trusted_outputs_settled` and `no_unsettled_output`. Every ordinary model is a
model of every trusted explanation (`all_models`). Explanations survive all
transitions (`head_step`), including installations, merges, and reobservation.

The exact readback requirement matters. Suppose an input expression q is L² B,
and a known source t is L int. An unfinished output forces B=int. Ordinary
refresh can then record q=L t. The outer L tag was independently known, but
copying q's precise descriptor into a new input fact would also copy B=int.
Checking only the tag allows this provisional equality to become an apparently
input-only explanation. `Readback` demands the full q=L t observation from the
preceding explanation; that particular derivation is unavailable. It does not
delete q=L t from ordinary constraints or forbid installing an otherwise
independently inspectable packet. It restricts later use of that packet's input
fact as head evidence.

`HeadJustified` means that some trusted explanation entails an observation for
the requested source identity and head test. `ReadyAt` additionally requires a
current observation of that test. The new `DecisionGuard` requires this for
every unnamed lower root and for all reads of every visible same-role candidate,
including negative applicability decisions. Named outputs are not waiting roots.

`GeneralNominalSettledSteps.Step` has the old administrative and merge
constructors. Its installation constructor adds this `DecisionGuard` to the
existing value `PacketGuard`. The state update and facts installed are unchanged.
`step_old` proves inclusion in the old value relation. Source formation is the
old empty-journal initial source followed by these new steps; no budget is
hidden inside it.

`GeneralNominalSettledBoundary` connects this relation to `B4TargetV5`'s existing
initial-state interface. Missing justification is inspection pending. Root and
inspected-position K2 keep their existing rejection priority. No declaration
rejection is added. Model decrease and stable closure are proved. There is no
new final executor or inference/generalization bridge in this change.

This is a conservative implementation of the provenance rule. A general theorem
that every legitimate source/settled explanation can be reconstructed as
`Trusted` remains open, particularly for broad interval descriptors. The old
value guard is also still conjunctively required. Thus existence of new head
evidence alone is not a proved sufficiency theorem for resuming every demand.
These are implementation coverage obligations, not extra owner decisions.

## 3. Why the first pump child stays pending

Use the checked registry and source in the earlier fresh-analysis note:

```text
P0 = P(L³ A0, L B, L U)
E0 = Extract(L A0, item=z0)
W0 = W(L A0, L B, L U, out=z0, middle=t0)
P1 = P(L A0, L² B, L U)
C0 = C(L B, L U, item=A1)
```

P0 emits E0, W0, P1. E0 settles and gives z0=A0. W0 emits C0 and
z0=L² A1, t0=L A1. U remains unconstrained: matching C's second input needs
U=int, so C0 stays pending and W0 is unsettled. P0 is also unsettled.

For a contradiction, suppose P1 can expand. Its P candidate needs a list head
at A0, the second list position of P1's first input. In the original source
this is identity 3. Even if full-journal refresh has recorded A0=L t0, the new
guard requires a trusted explanation of that head.

Delete all output facts of W0, including every support-labelled copy, for this
argument only. Keep the original source, all packet input facts, E0's output,
P0's output-routing constraints, and all other facts of this finite prefix.
There is a model of this cut with A0=int: take B=U=int, z0=int, assign compound
child inputs their displayed values, and leave W's fresh A1 and t0 arbitrary.
Assign both endpoints of a materialized compound its value. E0's equation and
P0's shared output-only routing are consistent with these assignments. W0's
input facts constrain its C child's inputs, not A0's head. Fresh allocation
keeps these assignments distinct. Refreshed observations are not source facts
and are therefore absent from this cut unless independently justified.

Every trusted explanation is modelled by this cut: each fact other than a W0
output is retained; a W0 output is impossible by `no_unsettled_output`. But int
has no nominal list head in the actual general carrier. This contradicts the
required explanation. P1 stays pending; no P1 children are generated. This is
not a K2 rejection, nor does it discard W0's equations from ordinary solving.

The Lean version separates the obligations precisely:

- `OutputCut` states the source model and validity of all ledger facts except
  the exact producer's outputs; `cut_models` proves validity for every trusted
  explanation using unfinishedness.
- `cut_excludes_nominal` uses the actual nominal/scalar separation theorem.
- `InspectionPoint` records the visible candidate, actual located bounds,
  read-list membership, and cached nominal descriptor.
- `first_recursive_child_not_installable` specializes these to the pump roles,
  registry, source, and identity 3. `FirstPrefix` still supplies the finite
  ledger cut and W0's unfinishedness. `pump_source_formed` is unconditional.

**Formal gap:** neither `FirstPrefix` nor the P1 `InspectionPoint` has been
constructed for a source-reachable P0/E0/W0 execution. The old work proved the
checked registry, source formation, emitted pattern recurrence and finite
algebraic models, not this operational prefix. The new conditional theorem must
not be reported as an unconditional executable pump regression.

## 4. Infinite traces and the proved measure

Every infinite new-Step trace from a source-formed state has novel installations
beyond every cutoff. Otherwise a suffix consists entirely of `Passive` steps;
the inherited administrative accessibility forbids an infinite such suffix.
`infinitely_often_installation` proves this with the new guard included in each
witness. Novelty means a packet is not `Committed`; it need not be a new ID.

Here is the exact finite-basis reduction, with no assumed rank. A signature is

```text
(parent occurrence, literal child occurrences, semantic delta)
delta(M) iff Inputs(packet,M) and Outputs(packet,M).
```

The signature omits the cached raw context. By `packet_exact`, that context is
already satisfied by an old-state model when the packet is installable. The
signature deliberately retains captured identities, output sharing, and literal
edges; outer role/head tags alone do not suffice. Support multiplicity has no
semantic effect on these facts and is erased here.

Let `Holds(s, sig)` mean that every ordinary model of s entails sig.delta and
every edge in sig is present. For a finite list F define

```text
remaining(F,s) = number of entries sig in F for which not Holds(s,sig).
```

Duplicates in F are harmless. All steps preserve `Holds`, by model decrease and
edge retention, so `remaining` never increases. If sig represents a novel
installable packet, `Holds(s,sig)` is false: otherwise `packet_exact` and its
edges prove `Committed`. After installation it is true. Thus every installation
represented in F strictly decreases `remaining`.

`SignatureCover R root start` supplies one finite F covering every novel guarded
installation in **every** new-Step state reachable from start. Strong induction
on `remaining`, with the independently proved `Passive` accessibility as the
inner induction, proves `accessible_of_signature_cover`. Passive steps either
decrease the count or descend in the inner accessibility proof; installations
strictly decrease the count. No fairness or scheduler is assumed.

`SourceBudget roles` names exactly the remaining theorem: for every Checked
registry and every existing `InitialSource`, such a cover exists.
`checked_initial_accessible` and `boundary_progress` derive the requested
initial and reachable-state accessibility from this named hypothesis. Checked
is used to request that cover; its Paterson conditions have not been turned into
the cover by these theorems. This is a more concrete reduction than an arbitrary
`InstallationOrder`, but is still conditional B4(1), not its completion.

## 5. What would bound settled outputs, and what does not yet follow

There is a useful bounded-tree argument, but its hypotheses must be kept visible.
In a finite first-order instance with one coherent normalized substitution,
strict Paterson descent gives child input size < parent input size. If the
parent's size is at most n, a completed dictionary has depth at most n and at
most 1+b+...+b^n nodes, where b bounds declaration arity of where-children.
Output-only variables are supplied by child outputs. Induction over the completed
dictionary therefore eliminates those variables: the root output is a finite
term over its input leaves and declaration constructors, with no fresh opaque
output leaf.

For an explicit conservative bound, let K bound the sizes and variable
occurrence counts of every output template, and take K≥1. Captured input terms
have size at most n. With b bounding the number of child results used, a
nondecreasing bound is

```text
F(0) = K
F(n+1) = K * (1 + (n+1) + b * F(n)).
```

The induction substitutes at most K occurrences of input/child expressions into
a template of size at most K; each child has a smaller input. Increasing K or b
to cover all named outputs makes the displayed bound conservative. This proves
a bound **given a fixed bound n on coherent input terms**. It is not a proof of
a source-fixed n for the general interval carrier, nor a theorem that arbitrary
semantic assignments to unknown sources have bounded size.

The missing bridge has four parts:

| Name | Required statement and scope |
|---|---|
| Settled readback | Every settled output used by `Trusted` has a coherent finite normalized symbolic expression over the appropriate input-origin leaves. It respects interval captures, actual origins, output sharing, aliases, structural rows, and normalization. No center of a nonpoint interval may be chosen implicitly. |
| Source refinement budget | For each checked initial source there is a uniform bound on the symbolic input structures used along all future trusted expansion histories, including changes to original source holes caused by settled equations and ordinary equality. This must derive from source constraints, declaration checking and K2, rather than assume that finite settlement proofs have uniformly bounded heights. |
| Invocation sharing | A finite set of semantic input/support signatures bounds actual installed invocation origins, despite retaining diagnostic occurrences and revisiting packets. Same-input merging must be connected to this statement; counting only role and outer head tags is insufficient. |
| Finite report enumeration | From finite invocation/source identities and finite declaration query syntax, enumerate the possible capture reports, semantic deltas, and emitted edges, modulo the context erasure in `packet_exact`; construct `SignatureCover`. |

For point terms, eliminating fresh opaque leaves suggests a finite source-hole
dependency argument: a newly justified constructor must be built from existing
leaves, and a return to the same leaf through constructors is K2. To obtain a
bound, however, one must also bound the contexts built before a leaf is refined,
and prove that this accounting survives ordinary refinements. This is still a
proof obligation, not an established argument for all general carriers.

In particular, neither “all justifications use settled outputs” nor “each
settlement proof is finite” implies a finite set of future signatures. A family
of finite trees can have unbounded heights. The old pump is excluded, but
excluding one pump does not establish the source refinement budget. I do not
have a rigorous unconditional proof of that budget or a new source-formed
infinite trace. No further semantic change is proposed on that basis.

## 6. Formal scope and validation

New modules: `GeneralNominalSettledSupport`, `GeneralNominalSettledSteps`,
`GeneralNominalSettledPump`, `GeneralNominalSettledBudget`, and
`GeneralNominalSettledBoundary`, all appended to `Yulang.lean`'s imports.
Separate audit: `Audit/GeneralNominalUnsettledDeferral.lean`.

The primary constructed the proofs directly. The skill's configured prover
role/configuration is absent here; no registered prover run is claimed. A
separate read-only reviewer checked the provenance design, cut-model scope,
and finite-cover reduction. Its merge-provenance objections led to explicit
trusted site-validity and endpoint-recovery premises. General resumption
completeness remains open.

Final checks (commands shown from the repository root):

| Exact command | Exit | Result |
|---|---:|---|
| `cd lean && lake build Yulang.GeneralNominalSettledSupport Yulang.GeneralNominalSettledSteps Yulang.GeneralNominalSettledPump Yulang.GeneralNominalSettledBudget Yulang.GeneralNominalSettledBoundary` | 0 | Five new modules, 668 jobs. |
| `cd lean && lake build Yulang` | 0 | Aggregate build, 2031 jobs. |
| `cd lean && lake env lean Audit/GeneralNominalUnsettledDeferral.lean` | 0 | All 45 new public theorems; dependencies only `propext`, `Classical.choice`, `Quot.sound`. |
| `git diff --check` | 0 | Whitespace check. |

An inline Python scope check exited 0: all previous `Yulang.lean` bytes remain
an unchanged prefix followed by exactly five imports; the only other tracked
change is the design INDEX entry; the seven new files have the expected paths;
all 45 public theorems have audit entries; prohibited proof constructs are absent;
new-file trailing whitespace and note links are checked. HEAD is still
`62cba43b5` on `astra/unsettled-deferral`. No frozen file or git ref was changed.

Development invocations of `lake build Yulang.GeneralNominalSettledSupport`,
`lake build Yulang.GeneralNominalSettledBudget`,
`lake build Yulang.GeneralNominalSettledPump`, and
`lake build Yulang.GeneralNominalSettledPump Yulang.GeneralNominalSettledBudget`
had exit 1 before fixes to the new files (a library lemma name, explicit carrier
parameters, a data-bearing certificate's universe, and a reserved identifier).
The final commands above passed. No full legacy audit, parser execution, or Rust
suite was run. No complete B4V5 executor or source-budget proof is claimed.
