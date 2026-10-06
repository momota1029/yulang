# Mandatory Record width: source-licensing audit

Date: 2026-10-06
Status: bounded source-rule characterization and conditional derivation;
independently spec-audited (one minor locator repaired, no remaining findings);
research-only
Implementation authority: none
Assigned baseline: `7e290d9b00c7abc8db4824f93e8e81302d0380b4`
Write lease: this file only

## Objective, method and result

Determine whether an existing governing source rule licenses the *same actual
callable* `our k(x:{a:Int}) = 42` at the target view
`{a:Int,b:Int} -> Int`, using mandatory Record width as inclusion over the
complete Value-entry challenge domain. Method: read the source authority and
trace each proposed implication to its actual premise. No Oracle,
implementation acceptance, structural-FMP-to-source transfer, or toy checker
is used.

**Result:** the audited sources provide a conditional complete-domain
containment law, but do not supply the Record source-licensing premise.
In particular they do not derive identity realization, complete admission
inclusion, or the target Function query from mandatory field presence.
This is a bounded absence finding in the named dependency set, not proof
that the program is forbidden or that no rule elsewhere could license it.
It does not reopen the selected role, entry, result or transport semantics.

## Pinned dependencies and exact governing sections

All semantic sources below were read from the assigned commit with `git show`.
Their full-file SHA-256 hashes matched the live worktree during the audit.
The observed worktree HEAD was `a9e719cbde76e210c6023e648826da65de6f0ebb`;
it does not replace the assigned semantic baseline.

| Dependency | Sections used | SHA-256 at assigned baseline |
| --- | --- | --- |
| `rules/research-lab.md` | One semantic baseline; compact assignment; evidence quality; writes/review | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | Authority order; approval gate; legacy compatibility | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | Disjoint-file mode; research checkpoint; integration ownership | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | §§13, 16–18, 21, 24 | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | §§2, 6–9, especially §7 checking and §9 joint containment | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-source-result-synthesis-choice.md` | §§2–4 | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` |
| `notes/design/2026-10-03-concrete-compatibility-boundary.md` | §§1, 3, 5–5.1, 7–8 | `5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16` |
| `notes/design/2026-10-04-structural-fmp-fence-completion.md` | §§1–2 | `29f7b04196d577f77ff9040dab19a1d83172ba323ff9bebd81ea5177ff6e926e` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | §§2–3.5, 5.1–5.3, 6.1–6.3, 8–10 | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `syntax-reference/en/src/types/named-record-type.md` | §1 authority/scope | `87554267c8a463834f1f13bfd4bea0c9ba54da41f3524257bf2ffa288319fa5a` |

The assigned question artifact
`notes/progress/2026-10-06-principality-proper-domain-view-boundary.md`
does **not** exist at the assigned baseline. It was read separately as the
primary-supplied problem statement, with SHA-256
`c9175bdb695efbbc110a2f0b2122583284b6f02ac617e08d11634e200e472591`.
Its own reported baseline is `2d378d0cf84b110e034d792d680f94b9369ad90d`.
Its prior review status is not inherited by this note. The primary was
notified of this dependency distinction. Navigation through `INDEX.md` and
the task records supplied locators only, not semantic premises.

## What is already selected

Charter §21 assigns the ordinary value annotation `x:A` Value entry.
Charter §§16–17 require inert construction of the whole argument, receipt
before one argument Force inside the same actual invocation, result rebind,
then body execution. Ignoring `x` does not remove entry effects or divergence.
Charter §18 and result-synthesis §4 give the literal body's
`Result(Value(Int)) = Comp(empty,Int)` skeleton. This is a body result,
not a proof of an empty complete call effect.

Charter §24 preserves the source/context-selected callable role as an axis
distinct from Value versus Computation entry. A checked target view does not
rewrite the actual callable's role. Charter §13 requires corresponding typed
value-path transport with activation-scoped authority and the original joint
dependencies. These selected facts constrain a future bridge; none chooses
the Record inclusion judgment or constructs its complete challenge domain.

## Conditional bridge, with the unresolved premise exposed

Fix one already licensed original decorated source derivation, its original
scope, solution `s`, history/configuration `h`, and one joint
`xi = (nu,K,D)`. Let `A={a:Int}` and `B={a:Int,b:Int}`. Write
`D_A` and `D_B` for *complete* admitted challenges: carriers, configurations,
typed response obligations and all finite future/raw-resumption histories.
Write `P_A(d)` and `P_B(d)` for complete joint observation bounds.

The exact sufficient hypotheses are:

1. The original callable satisfies its complete `A` description, including
   its actual role, entry, receipt, body, result consumer and return delimiters.
2. An independently licensed same-value Record checking/transport derivation
   retains the original whole carrier/provider evidence and proves
   `D_B(s,h;xi) subseteq D_A(s,h;xi)`. Its derivation covers admission of
   the initial context **and** all extensions by responses, raw resumptions
   and future uses. It preserves typed incidences, activation/protection,
   scopes and the original joint assignment; it does not merely prove
   returned payload field presence.
3. On every `d` admitted by `D_B`, the same actual invocation gives
   `P_A(d) subseteq P_B(d)`. In the proposed unchanged-output case this
   follows if the complete observation predicate and original operands are
   retained identically on that restricted domain. The literal `42` alone
   does not prove this premise, because entry can expose requests.

Then, for any checked challenge `d`, hypothesis 2 makes it an actual
challenge. Hypothesis 1 places every actual complete observation in
`P_A(d)`, and hypothesis 3 places it in `P_B(d)`. This is precisely the
typed-core §9 sufficient containment law. Under §7's representation-preserving
checking premise, erasing only the proof labels retains the executable
instruction graph, source boundaries and symbolic constraints. All prefixes
and future histories are covered by the hypotheses, with no separately
chosen witness for a value, row, state or family.

This is a **conditional semantic theorem**. Hypothesis 2 is still the
unproved source bridge. A local source proof would need a Record descriptor
typing/identity rule plus admission transport for each of source-contracts
§3.3's four admission constructors. The immutable-record emission row in
§3.2 preserves the original field-provider tuple and sharing; it does not
state those typing/inclusion/admission clauses. Finite induction over an
inventory cannot supply its missing primitive cases. Also, the semantic
theorem does not establish that an effective direct-query resolver has an
evidence alternative for this unequal-domain case.

## Where the attempted source derivation stops

| Proposed implication | What the source actually supplies |
| --- | --- |
| Mandatory width `B <= A` implies decorated-value inclusion | FMP §2 defines the proper-tree structural order; FMP §1 explicitly selects no production Function/effect semantics. Concrete-compatibility §3 limits transfer to general concrete checking. No descriptor-to-source-value interpretation lemma is supplied. |
| Extra `b` can be ignored with identity realization | Concrete-compatibility §5's Record rule is explicitly a candidate, not an adopted source or runtime rule. §5.1 says `ProvenIdentity` needs independent source/runtime proof and cannot follow merely from acceptance; omitted/extra-field realization remains open. |
| Same returned values imply complete Value-entry admission inclusion | Typed-core §7 defines `VIncl/CIncl` as semantic propositions and disclaims proving arbitrary inclusions. §9 requires joint domain inclusion and observation containment. A payload witness omits receipt, entry requests, responses and resumed state. |
| Known syntax supplies missing Record semantics | Named-record syntax §1 explicitly excludes field semantics, checking and lowering. Typed-core §6's result-synthesis table has no Record construction/checking row. |
| Common allowance allocation supplies the changed value interface | Source-contracts §§5.1, 5.3 and 6.3 fix the non-coverage/value interfaces. Its displayed Function certificate demands domain equality; its coverage/Absorb leaves do not infer Record conversion or a different input domain. |

Consequently a proof that assumes a presence-only Record membership predicate
and assumes view-neutral receipt/admission transport would prove a consequence
of those assumptions. It would not prove that they are the selected source
rules. Enlarging a field-only toy domain leaves both missing premises intact.

## Smallest discriminator and failure conditions

For the *assigned* nonempty `A`, the original candidate adds the minimum one
required field to obtain strict mandatory width. Under a presence-based
same-value interpretation, the pure carrier returning `{a=0}` belongs to
`D_A` and not `D_B`, while the pure carrier returning `{a=0,b=0}` belongs to
both. This conditional payload discriminator already appears in the assigned
note; this audit does not claim a new source counterexample from it.
There is no established accepted-program witness or source-preservation failure.

The conditional bridge fails if complete admission depends on a changed
receipt/profile/path, if checking rebuilds or executes the Record, if an
original constraint is lost, if a binder or joint dependency is freshened
separately, or if entry/future response observations exceed the checked
bound. These are proof obligations, not allegations of actual behavior.
Strictness additionally needs an independently admitted `A` challenge excluded
by `B`; mathematical field masks alone do not establish its source admission.

## Checks, coverage, resource use and remaining scope

Commands were narrow `git show BASE:path`, `sed`/`rg` section extraction,
`git ls-tree` source-location inventory, and Python `hashlib.sha256` over
baseline bytes versus live dependency bytes. All pinned direct dependencies
matched. The missing baseline question-artifact lookup failed as reported
above. A locator search for `spec/` found no such directory; the named-record
syntax reference was inspected instead. This is not an exhaustive repository
search or a characterization of production acceptance.

No tests, builds, executable probes, enumeration, mutations, Oracle calls or
Git mutations were run. Seeds/ranges and reference/candidate independence are
not applicable. Source reading is independent of implementation output, while
the conditional derivation shares the original licensed source derivation and
all typed-core premises explicitly listed above. No independent review of this
artifact occurred. CPU, peak memory and total wall-time were not measured;
only lightweight reads and one hash process were used, with at most four
independent read commands in one batch. No heavy process budget was consumed.

Full Record descriptor membership, raw annotation admission, complete original
Function formation, resolver completeness, effects/histories beyond supplied
premises, production conformance and unrestricted principality remain
unverified. No production or shared-record path was changed.

Recommended next action: have the primary obtain or locate a source-authorized
Record identity/admission transport rule before promoting the proper-domain
candidate to an accepted-source witness. Keep the strict-domain separation
conditional until that rule's complete challenge obligations are proved.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-principality-record-domain-source-license.md`.
- Baseline: `7e290d9b00c7abc8db4824f93e8e81302d0380b4`.
- Dependency changes: none among pinned semantic/rule dependencies; the
  separately hashed assigned question note is absent at baseline and is not
  silently treated as a baseline file.
- Claim/review status: bounded source-rule absence finding and conditional
  derivation; research-only, independently spec-audited with no remaining
  findings, frozen on handoff.
- Checks already run: exact source-section reads; baseline/live SHA-256
  equality for the listed dependencies; no tests/builds/probes.
- Proposed commit message: `research: isolate Record width source-admission license`.
- Shared-record deltas left for primary/curator: link this bounded audit from
  the proper-domain/principality records; retain unresolved Record identity,
  complete admission transport and direct-query evidence premises. No theorem
  promotion, source acceptance/rejection decision or implementation authority.
