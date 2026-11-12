# Cycle151: independent Joint before a focus packet exists

Status: partial structural theorem; general V5 remains 6/14 supplied, 8/14 open.
Date: 2026-11-12.

## Result and actual assumptions

`GeneralDictionaryUnrecordedVariableJoint.initial_trace_joint` quantifies over an arbitrary finite actual ordinary support trace from a genuine `InitialSource`, a chosen visible checked declaration, an arbitrary current journal assignment, and every site in the focus's alias class. It derives `Joint` without a packet at the focus, a `Coherent`/`Scheduled` premise, a prior `Joint`/`BranchAt`/`BranchModels` premise, or independently assumed selected-key equality.

The structural coverage premises remain explicit. The focus and every Related site must have the SAME chosen declaration's `TreeBranchShape`, or one of the previous terminal tree/scalar leaf shapes. Each related site must have actual current selected classification, with its own arbitrary key and children. All witnesses are tested in the same current journal model, not separate existential survivor models. The underlying VariableTree shape requires variable-only child arguments, no child-output requests, no root-output requests, point internal tree edges, and injective capture names. The requirements and emitted children may be nonempty. The ordinary trace restriction remains; unrestricted histories containing descriptor refresh or reobservation are not proved to preserve the packet-extension premise used here.

Proof order is noncircular:

1. Construct an actual current `Instance` from syntax using `GeneralDictionaryVariableTree`, then use current uniqueness to identify its declaration key and children. Terminal alternatives use the independent tree/scalar construction.
2. Construct `BranchAt` for the focus and all Related sites in the one supplied assignment.
3. For each recorded packet aliased to the focus, source formation puts its actual site in the current sites. Ordinary-growth replay and that site's current uniqueness identify the recorded key with the same chosen key. This DERIVES the key-compatibility part of `Joint` instead of assuming journal coherence.
4. Only after Joint exists, apply reachable-state stability. `stable_instances_generated` derives `Instance` for EVERY current journal model and real `Generated` membership for every selected child. `stable_nonterminal_packet` derives an actual matching recorded packet when the selected child list is nonempty. Thus the old EdgeOrigin result is no longer used to obtain the premise needed to establish Joint in this structural subclass.

`GeneralDictionaryUnrecordedAliasLeafJoint` is the terminal-specialized version. `GeneralDictionaryUnrecordedAliasLeafExample` supplies a genuine nonvacuity regression: after the actual Display(List Int) source installation, the Int child is reachable, stable and inhabited but has no matching packet. Its Joint is now independently constructed from scalar syntax in every current journal assignment. This fixture does not claim nonterminality; the nonterminal theorem above is the quantified structural result.

## Residual outside the theorem

This is not general V5 EvidenceNode or GeneratedChildren. No theorem establishes that every reachable selected alias class satisfies the structural coverage predicate. Arbitrary compound where expressions create nonempty materialization schemas. Their `Models` obligations include observations of generated sources, tests on compound shapes, variable/capture equations, and pairwise compatibility of repeated actual variables. Each survivor has an existential private branch model; those existential witnesses do not imply a single model preserving the existing journal while satisfying all aliases. Named output obligations at different sites are especially not erased by SameInputs.

What is still needed for the unrestricted case is an independently derived simultaneous-model extension (or a proved invariant implying it) for newly allocated child/associated-output sources, preserving all existing packet constraints and every related site's obligations. Merely adding `∀ model, Models → BranchModels`, Joint, or common-key agreement as a hypothesis would restate the missing bridge. Whether every operationally reachable selected class admits such an extension has not been proved or refuted here. No reachable+stable+inhabited counterexample to the general V5 bridge is claimed.

## Validation

Three new Lean modules only; frozen Audit.lean and README and old semantic definitions are untouched. Each source was compiled with Lean 4.35.0, `--trust=0 -DwarningAsError=true`, using existing dependency oleans and a separate output directory. Thirteen public theorems are printed by the separate audit; the focused all-declaration gate includes all constants of the three new modules and allows only propext, Classical.choice and Quot.sound. Full project build and Yulang2 runtime were not run by this worker. Parent cycle report supplies the integrated focused build and publication checks.

Development failures were confined to command/path setup and elaboration: Lean does not accept lake's `--wfail` flag, the initial separate prefix lacked imported oleans, cross-filesystem hardlinking failed, scalar fixture interpretation required explicit definitional reduction, and a local identifier used reserved keyword `variable`. They were corrected without changing old declarations or weakening theorem statements.
