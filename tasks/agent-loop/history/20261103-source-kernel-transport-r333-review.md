# R333 — original source transport and goal-indexed repair

Baseline `0d5c7dfb0`. The source admission image proof SHA-256 is
`a902c15f2960231478ad7800f2354b1c136941e695a06fdfd1e3683292fc7bf1`;
the publication transport proof SHA-256 is
`a6c9e70a159bf60a72bda0fcc873986564ae5358dd042bccfad166df877e7c22`.
Independent review checked every payload case, original source and goal-indexed
admission domains, exact occurrence and parents, and the exclusion of new
invocation views by the existing R328 relation. It also checked publication
success and failure, ordered histories, duplicate names, identity and all
three Judgment publication constructors. The results reduce the domain and
publication subgoals of transport; they do not authenticate native semantics.

The initial complete kernel proof SHA-256
`aea7032224a7c2d55c7f12e03fc9f150bc123f12d9b30b56906597b881b65bcf`
passed independent checking and transports R332's actual parent witnesses,
locals and both children to a constructed conservative instance.
Before commit, two extra trailing blank lines were removed; final SHA-256 is
`80929bb32afa232b26d817a50018f206c98802da5e4c096710912cefec227da1`.
The independent reviewer verified the exact two-byte difference and recompiled
both the final file and goal-indexed dependent, including their theorem audits.
Independent review found that this proof uses the goal-independent `admissionKernel` for
checking. SG's Function checking instead needs `GoalAdmitted` for each current
goal; descriptor alignment cannot be assumed for intermediate targets. The
initial proof therefore does not establish goal-indexed checking transport.

The repaired proof SHA-256
`801ce238d78c2c94bdaf36b43c1a6b6a609b5758a1518ca46a51378de6d1314d`
uses `goalFunctionKernel` at both ends, derives the original FunctionShape
through decoding, applies goal-indexed image recovery in Function checking,
and separately preserves source-admission universals. Independent source
review found that it covers every Checking, Boundary, Local and Judgment
constructor and applies the original source root inversion and R159 parent
to the same occurrence, data, candidate and children. It does not depend on
the predecessor's goal-independent root result.

The original root source judgment is still a premise. Primitive relations are
constructed as images of an arbitrary old kernel, and R328's generated-view
input is a conservative instance. Neither proves that independently fixed
native semantics select this kernel, nor constructs the genuine source EI,
all arms, R306 licensed child, result/future relationship or whole Union.
The unchanged source-to-native and parent semantic edges remain open.

Independent Lean 4.35 at `-j1 -M2048` recompiled the source admission and
publication modules and audited all 28 authored theorem types and axioms;
it also recompiled the initial kernel module and audited all 19 theorem types
and axioms. All passed with only standard Lean axioms. The goal-indexed repair
also passed independent Lean compilation and all 20 originating theorem type
and axiom audits (18 authored theorems and two Lean-generated equations).
Its independent complete audit SHA-256 is
`3ae3ab888a958f53c3c648373df31bc895532ca84084a84c4c2624a84186eaf9`.
The producer separately rebuilt the complete 59-module cone from source under
the pinned toolchain; the independent checker verified source, configuration and
artifact hashes before reusing its independently checked dependency artifacts.
