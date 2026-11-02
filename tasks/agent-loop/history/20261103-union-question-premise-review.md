# Union question premise review

The user challenged the description of Union as selecting a branch. The primary
also corrects its prior conversational explanation: the questioned Union was
presented as a type union, but the cited source contract concerns relational
proof notation. No runtime selection should be inferred.

Independent reviewer `/root/union_semantics_audit` found the A/B/C question
`questions/2026-11-02-original-typed-union-rule/question.md` premature and
recommended withdrawal. Source-contracts §2.1 describes a whole-tuple
alternative in proof notation, not a runtime object or type constructor. IF
construction retains both interfaces and tagged clauses; the original relation
still determines satisfaction. `Relations.alternative` indexes a supplied
relation family by a Bool, and the left/right Lean constructors record a
particular derivation. They imply neither a unique runtime tag nor disjoint
alternatives; overlapping cases may admit both proofs.

R164 accurately records that its child/result packet correspondence is not
constructed. Its inference that supplying it necessarily requires a new
operator semantic decision is unsupported: existing relation membership may
suffice, or the auxiliary interface/provenance construction may need repair.
No new semantic rule is approved or assumed. The question is withdrawn as
premature, preserving its original text as history. The independent reviewer
performed no writes, tests, builds or Git operations.

Remaining work, not completed here: audit the connection, if any, between the
source relational Union and actual Yulang union types; formulate extensional
membership including overlaps; justify proof tags and packet maps from the
relevant original relation. The R159 dependent bridge and parent remain open.
Withdrawal supplies neither the missing map nor parent closure.
