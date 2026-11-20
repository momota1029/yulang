# Cycle 291: finite exporter from resolved source data

Cycle 290's finite-complete exception used an independently witnessed
common-default overlay. Do not try to enumerate arbitrary Nat-to-table
functions. Instead use a small resolved source interface: ordered
constructor declarations with resolved key, optional layout/name
(removal is explicit), and an exclusive classifier (primitive, invariant,
or unclassified). The fallback is explicit code: absent, or the existing
example policy of a constructor with the same name and empty layout.
Nominal flags do not promise materialization of row layouts. Reject
duplicate source keys at the validation boundary rather than treating an
override as another declaration. This is a producer for metadata evidence,
not frontend parsing or a change to the old resolver.

Independent finite expectation: lookup returns the first source entry or
the encoded fallback; primitive and nominal codes are exclusive. Validate
primitive parameter shape and duplicate declarations. Export constructor,
primitive, invariant tables and prove exact observed lookups and off-source
default. Build cycle-290 overlay witnesses by construction. Recover the
existing example fixture only after pointwise, independent equalities
against its original registry and raw context, keeping raw fields intact.

Independent source-materialization check: enumerate actual app *uses*
with arity from complete explicit and where declarations and a supplied
finite resolved-default manifest. Reflect old ConstructorUse at each
entry, hence DeclarationCovered. Only claim full Coverage if the manifest
also lists **all** role defaults, with independently proved completeness;
a scan of the candidate list cannot prove that. Test true source when
row constructor is known but only captured opaquely, and false source
where decomposing that row remains unsupported despite valid Metadata.
No new parser, kernel, default policy, or termination claim.

## Finite role defaults with an independent manifest

To avoid asking callers to guess a complete default domain, provide an
optional resolved role-table constructor. Each finite row has role key,
arity, and a finite output list. An output entry `none` means required;
an absent key is undeclared, and `some term` is a positional default.
Role fallback is an explicit arity with no outputs. The constructor
requires the existing positional scopedness evidence and distinct role
IDs/output names. Prove that emitted defaults are exactly the OLD
`RoleDecl.assoc` successes of the generated table. Transport to an
existing raw role environment only given function equality. Closed
controls: an unused finite role default must be enumerated even if no
explicit declaration uses that role; a legal scoped but row-pattern
unsupported default falsifies the shortcut "explicit scan is complete."

## Actionable coverage failures without a language diagnostic change

Attach a resolved origin to every application: declaration head,
where-input, where-output equation, associated equation, or role default.
An ordinary coverage failure should say absent constructor, wrong arity,
primitive layout mismatch, missing classification, or unsupported nominal
layout. Reflect each diagnosis with the old ConstructorUse predicate, so
an empty failure list is exactly Coverage given the exact default manifest.
No diagnostic in the frozen resolver gets changed; this list describes
the finite source export's supported materialization fragment.

## Removing an unnecessary common-fallback assumption for these two codes

For this resolved source encoding, if one fallback is absent and the other
is an identity/empty-layout entry, the generated constructor functions
cannot be equal. Produce a numerical witness above the finite union of
both key domains (maximum + 1), and prove both lookups use their fallback.
The combined source checker can diagnose this case separately. If
fallback codes agree, reuse the proven overlay certificate to obtain an
iff with old Metadata, even for differently ordered source lists.
Attaching data to existing registry/state is still a separately checked
condition; neither an arbitrary frontend exporter nor a raw Step follows.

## Local compiler-domain converse

Full source Coverage is not a necessary condition for each old install.
To give a sharper boundary, prove a converse for the unchanged centered
output compiler: whenever explicit Pattern translation, or positional
default Term translation, returns a value, every application it required
satisfies ConstructorUse (and list lengths agree). Induction is on the
source syntax; application success explicitly exposes constructor,
arity and the appropriate primitive/nominal branch. Combine with the
existing completeness theorem. A request-local decision can then check
only looked-up live bodies, while a missing lookup remains failure.
This is about actual output-class Ready, not preparation of a new Frame.

## Materializing a metadata-only context without manufacturing a raw Step

An independently supplied resolved table can re-express an existing
observation state if the finite list of *actual recorded descriptor*
keys agrees. Prove that check iff its catalogue field can legitimately
be rebuilt. Replace only the constructor table and the interpretation;
prove unchanged observation/model/knownness fields and an exact
original-context identity when the source attachment equality holds.
This is a view-level constructor, not installation, transport of an
entire journal, or a claim that arbitrary retagged Contexts are reachable.
The unused-key control should be accepted as a view while old full
Metadata against the original registry still fails.

## Transport the actual recursive report through the view

The inspector's report is indexed by the entire observation state, not
only by the common slot count. Compare it via an explicit conversion of
the Capture wrapper; every slot pair, origin path, visit, test and
failure is retained. For a fixed query, inspection only sees the unchanged
state observations, so reindexing its result should recover the old
report. Separately require finite agreement on the declaration's head
keys so that the descriptor/interpretation view also produces the same
queries. No whole raw State equality is required for this local theorem.
Do not lift to Step/Frame for the retagged journal.
