# R189 — selected ViewLogic witness stops at the formation denotation

Outcome: **BLOCKED_AT_EXACT_FORMATION_EQUATION**.
Author: `/root/r189_selected_viewlogic_witness`; handoff revision 1.
Contract: `tasks/agent-loop/sprints/viewlogic-selected-witness-r189.md`,
SHA-256 `2550c149c6f9798d53ee8fcf69764493eb0fada1781f220824638262429c7076`.
This is a source/declaration audit, not a checked or reviewed theorem.

## Parent and exact application

The unchanged parent is `YulangClosure.SourceProblem.InferenceSoundness`
(`Contracts.lean:128–130`), with all quantifiers retained:

```text
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a.
```

The packet concerns only the outer `Judgment.existsE` for an unannotated
`App_q(f,arg)`. Write `b_q = ⟨q,.viewLogic,0⟩`. The original constructor
(`OriginalSourceGeneration.lean:751–754`) requires one
`v_a : ScopedValue V`, `k.admitted E b_q v_a`, and the body judgment in
`E.extend b_q v_a`. It does not require admission of every raw domain element.
No pinned equation examined here makes that stronger universal law necessary.

For this application the value must decode the witness selected by the same
solution `a` at this binder in the original telescope `Δ`. A different logical
payload, occurrence, environment, description frame or telescope cannot fill
the premise. **App sub-obligations discharged: 0. Parent premises discharged
or refuted: 0.** Other App premises and the full parent remain OPEN.

## First unresolved generated formation equation

The actual source-rule constructor at
`OriginalSourceGeneration.lean:111–123` places the following first local atom
inside that existential binder:

```text
A_q : Atom := atom .descriptorFormation q Γ [f.site, arg.site]
```

Its `Atom` fields and source references are fixed by
`OriginalSourceSyntax.lean:307,331–351`; it is a name for an independently
interpreted local relation. It is not itself a mathematical definition of
formation. The declared semantic interface is exactly
`Kernel.atom : Environment V → Atom → Prop`
(`OriginalSourceGeneration.lean:670–672`). At the selected extension
`E_a = E.extend b_q v_a`, its source-side proposition is exactly:

```text
k.atom E_a (atom .descriptorFormation q Γ [f.site, arg.site]) : Prop.
```

The first missing independent equation for the attempted generated object is:

```text
⟦DescriptorFormation(q,f,arg,v_q)⟧_(a[v_q↦z_a],Δ) = ? : Prop
```

Here `DescriptorFormation` is precisely the occurrence displayed in the R187
App object (`2026-11-02-yulang-canonical-inference-model-r187.md:100–109`),
and the required correspondence is to the source atom above, for the same
selected payload and extension. This displayed question marks an unfinished
defining equation; it introduces no new predicate, constraint or hypothesis.

R187 supplies ordinary meanings for shared conjunction and existential
binding (`:70–91`), but requires an independently defined binder domain.
Its App display expressly remains a representation attempt: neither actual
Simple-sub emission nor solving of those clauses is proved (`:112–118`).
It supplies no independent expansion of this formation occurrence which
could be evaluated on `a` to recover selected logical admission. Therefore
neither extracting `z_a` from an actual defined ViewLogic interpretation nor
deriving its admission has been completed here. A generic existential
connective cannot supply its still unconstructed domain or leaf denotation.

This is the stopping equation, before the later complete-Call denotation
boundary R187 separately records. No new owner was opened to fill it.

## What the available raw representation actually reduces

The admitted heterogeneous environment gives a useful diagnostic without
supplying the missing equation. Its independent raw logical data type is:

```text
Logical s View = {
  descriptors : List (Endpoint × s.Descriptor),
  interfaces : List (Endpoint × s.Interface),
  viewMeaning : View → s.Interface,
  eta : s.Assignment,
  witness : s.JointWitness
}
```

This is the actual record at `OriginalSourceEnvironment.lean:249–254`.
No source-success predicate occurs in it. The existing raw readout is
`scopeCandidate E n (.logical .viewLogic L)` (`:644–646`). Neither this record
nor that constructor identifies the exact `D_q(E,Δ)` or the actual selected
`z_a`; treating the whole record type as the canonical domain would add an
unproved identification. In particular, binder arity `0` does not select the
event occurrence `n`.

To locate the outstanding proof obligation, unfold only these existing
declarations at an existing decoded prefix
`decode readout E = some state`. For the candidate carrying the original
selected data `L_a` and occurrence `n_a`, the admission proposition reduces to:

```text
Admitted inputs readout admissions E b_q
  (scopeCandidate E n_a (.logical .viewLogic L_a))
    ↔ admissions.logical state b_q .viewLogic L_a.
```

This is a paper-level specialization/unfolding of `admitted_scoped_iff`
(`:648–653`), `DataAdmitted` (`:608–611`) and `LogicalKind.binderKind`
(`:260–264`), not a new conditional success theorem. Parent-path equality is
built into `scopeCandidate`; the logical-kind equality is reflexive. The
remaining proposition has the exact declared interface:

```text
LocalAdmissions.logical :
  Decoded s View → Binder → LogicalKind → Logical s View → Prop
```

It remains an independent input (`:596–600`). It is evaluated at the prefix
`state` decoded from `E`, before the ViewLogic extension. Evaluating formation
in `E_a` does not silently change this admission prefix. `admissionKernel`
(`:724–729`) and `functionKernel` (`:1100–1106`) install `Admitted` without
constructing `admissions.logical`. The original abstract `Kernel.admitted`
remains independent as well. This adapter reduction identifies a missing
local certificate; it does not prove that every accepted source kernel uses
this adapter or that a solver-selected payload has the certificate.

The App `descriptorFormation` atom has no independent interpretation installed
by the examined literal/Name adapters
(`OriginalSourceInterpretation.lean:852–862,879–889`;
`OriginalSourceEnvironment.lean:963–979`). Their fallback retains the supplied
original local semantics. No equation connects the actual selected formation
clause to the logical admission field.

## Reused evidence and rejected shortcuts

- R188's reviewed stop is reused as the source-constructor locator. Its
  universal raw-domain admission law is not reused as a necessary premise.
- R187's whole-assignment/telescope representation is retained with its
  explicit incomplete status; its App display is not promoted to an actual
  generation or satisfaction theorem.
- Source-Generalize §2 (`:80–89`) fixes ViewLogic frame placement and sharing.
  It does not specify this raw binder interpretation. Section 3 retains
  genuine local laws as obligations, rather than deriving them from scope.
- Source-contracts §§2.2, 3.3 and 3.5 retain independent admission and local
  descriptor laws; their conditional C-realization does not instantiate this
  formation equation. Its admission inventory concerns complete histories,
  not a new definition of this ViewLogic logical binder.
- Native signature formation §§2, 4 and incidence construction §§2, 4.3, 6
  construct support/provenance and preserve independent evidence. An anchor
  may have an empty fiber; joint hiding retains an admission certificate as
  an input. These constructions do not manufacture the selected certificate.

`Satisfies` at `OriginalSourceGeneration.lean:847–848` already conjoins
`k.admitted` in its existential case. Using that source-side satisfaction
definition as the solver relation would assume the missing conclusion.
No `WellFormed → admitted` law, new admission constraint, source-success
domain, complete C0 assumption or alternate witness is used. Varying the
uninterpreted admission field to construct an abstract countermodel would
not be a counterexample to the accepted source semantics; none is claimed.

## Evidence boundary and next owner action

The exact original consumer is `Judgment.existsE`; the exact first local
formation occurrence is the `descriptorFormation` atom; the remaining adapter
certificate is `LocalAdmissions.logical state b_q .viewLogic L_a`.
Actual independent generation/solving and its transport through accumulation,
propagation, levels, extrusion, qualifying intrusion and generalization have
not been constructed by this packet. No bypass or weaker ordinary inference
rule is proposed. Rust/native correspondence is outside scope and supplies
no evidence here.

TODO **R189-FORMATION-SELECTED-1**, owned by Luna for exact source/construction
assignment: obtain or register the independently defined denotation of this
actual formation occurrence and the same-assignment binder-domain/readout,
then derive the selected local admission certificate at the original prefix.
Required inputs are the actual emitted formation clause, its independently
interpreted fields, `a`, `Δ`, and the original local admission meaning.
Falsifier of a proposed completion: it requires an extra local-law premise,
inserts admission into solving, changes the selected payload/prefix/telescope,
or cannot show that the actual generation emits the interpreted clause.
This TODO is not a lease, semantic change or production-code authorization.

There is no further step inside this packet after its exact stopping equation.
Semantic under-specification, impossibility and a source-qualified
counterexample are all **unestablished**. No Lean declaration was added;
theorem types were read from source only and axiom dependencies were **not
audited**. No checker, Lean/Lake, build, tests, Rust/Cargo, environment/cache,
scratch, Git or descendant work ran. Checks were SHA-256 authentication and
bounded direct-source inspection. Requested and observed runtime model/effort
are UNKNOWN in available launch metadata. Grant: 1800 seconds, no renewal;
precise elapsed active time was not instrumented, so charge the full grant.
Only the two leased output paths are new; no scratch paths exist. Writing
stops on freezing revision 1; independent review and integration belong to Luna.

## Authenticated direct dependencies

Every listed digest matched before the corresponding content read. The
artifact's author is the sole contributor; there are no descendants.

| Input | SHA-256 |
| --- | --- |
| `tasks/agent-loop/sprints/simple-sub-inference-soundness-r184-v4.md` | `518ee36cf16c5266a9cd7aabfec25eb7e42ceba9c9e6f7e9ce5970873d07b640` |
| `tasks/agent-loop/sprints/yulang-canonical-inference-model-r187.md` | `999213b617db69cc2511692b6338f4c814fe8768d119ba477749124ee07b6218` |
| `notes/theory/2026-11-02-yulang-canonical-inference-model-r187.md` | `da0f7aa365db0d3a97b6ba9988850c786e88eb9ffa6349eddfe964d25d7fd7c1` |
| `tasks/agent-loop/history/complete-app-soundness-r188-outcome.md` | `312ca654be93d2f77a01bcc570f350cbf5b5db24d72305f1f2412291fc19a95b` |
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` |
| `notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean` | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-08-native-signature-formation-definition.md` | `e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9` |
| `notes/theory/2026-10-08-source-signature-incidence-construction.md` | `7367ce8eb69376583386c6d675d067712ec6fa173e96f458ee34ce390dc8901a` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
