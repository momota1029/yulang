# SourceHeads context: concrete inhabitation and remaining nonempty-run gap

Strict `SourceHeadsContextProbe.lean` establishes a concrete nonempty semantic context for the existing AllocMerge source, not merely a conditional assumption:

1. Lift its actual old source initial state into the versioned initial state and prove the mixed-source Initial predicate.
2. For **every** mixed-source reachable state and **every** retained versioned Plan, show that the fixed all-Int assignment satisfies its actual headSchema.
3. Consequently Context(True, source) is inhabited.
4. More strongly, the same assignment satisfies Context(Models versionedInitial, source).

The proof does not restrict attention to one inspector trace. It obtains metadata for arbitrary actual installations, recovers the registry declaration, and splits its two possibilities. The parent declaration's head query is exactly scalar Int at the Plan's actual positional center. The constant assignment satisfies it at every possible source identity. The leaf declaration's head is empty. Both have no head variable uses. Thus this is a genuine proof of the all-futures predicate, not `Heads` assumed for a selected pair or a vacuous empty-registry trick. No body/effect satisfaction is used.

**Nonempty operational limitation:** this source's existing concrete installation/merge regression uses the old centered journal. This probe does not construct an actual nonempty *mixed-versioned* installation path for it. The separate Compound238 representative example does prove a nonempty mixed-versioned registered Plan, but this probe does not establish its all-futures SourceHeads context. Therefore the current artifacts establish concrete context inhabitation and concrete nonempty registration on separate fixtures, not their conjunction on a single verified nonempty checked source run. Do not report that stronger conjunction as proved.

## Why the general Context premise remains strong

SourceHeads fixes one assignment and demands head-schema satisfaction for every Plan on every reachable source branch, not only eventual selected events or a chosen representative's witness path. Per-installation existence of a model, source formation, or a model of the initial state does not in the current theorem supply a single common assignment for all those branches. Source semantic restriction lemmas go from later Models to earlier Models; they are not automatic forward/global model extension. A successful finite observer run does not establish SourceHeads either.

The generic certificate therefore has exact all-assignment meaning relative to Context(base, source). Without separate context inhabitation, that equivalence can be vacuous. The concrete all-Int probe removes this vacuity for the stated source and assignment, but is not a general completeness, context-inhabitation, or source-machine termination theorem. A future improvement could prove head-support preservation/global consistency for a specified source class, or weaken the context to a verified subset of representative/inspector paths; neither is claimed here.

Verification: strict Lean --trust=0 -DwarningAsError=true PASS; four theorem axiom audits only standard axioms. No source runtime files changed, no old-Step claim added.
