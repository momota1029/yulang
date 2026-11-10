# Draft: computed fresh demand names for an independent capture

Status: Draft. Date: 2026-11-10. Scope: B4 source boundary, existing finite structural interval capture only.

## Goal and boundary

Close the fresh local-binding namespace case of the caller-supplied bindingSource boundary. Compute an offset strictly above every existing demand name. Map each local binder to offset + binder; do not use ambient endpoint owners, coincident endpoint values, or a compound interval center as its semantic demand identity.

This is an independent-capture utility, not a language decision to freshen every revisit. An already registered invocation that must share its local variables should retain its allocated map. Associated equality, intentional cross-invocation sharing, stable invocation keys and registry lookup remain separate obligations. The new executable wrapper retains all three candidate outcomes and all where children; it does not choose dictionaries.

## Data, execution and independent judgment

Existing Demand, Result, Declaration and Goal are reused. `boundary old` is computed from the finite prior demand list; `freshSource old binder = boundary old + binder`. `extend old previous local` is a proof witness that retains previous values below the boundary and uses local values above it. The executable candidate uses no witness or selected central type.

Independent local models are existential local valuations satisfying the original HeadFits and WhereFits judgments. Every ambient endpoint is interpreted by the same original assignment, so shared endpoint constraints remain shared. No equality of local binder spelling across separate invocations is imposed.

## Quantified target

For every endpoint-slot map, assignment, old demand list, declaration, goal, actual accepted binding list, the generated ordinary atoms using the computed freshSource have a model iff (there exists a valuation satisfying all old demands) and (there exists an independent local valuation satisfying the original head and all expanded original where templates). No consistency, successful child dictionary, source map, alias or graph hypothesis is assumed.

Prove freshness for every old demand and every binder, injectivity for every pair of binders, exact extension on all old demand names and every fresh binder. Lift the model theorem through the actual candidate return, and connect the computed-map wrapper to the previous cycle's original-root ownership theorem for real recursive histories.

## Evidence and remaining bridges

Read spec 6.3 and the existing audit x-oracle entries X13–X16, C3-PARENT and C3-PARENT-NEG. They constrain preservation of source sharing and ordered child obligations, but do not prove this namespace implementation. No new Yulang2 run or semantic choice is made. The main B4 bridges remain five: source boundary adequacy, generated work closure, termination/semantic saturation, final classification, dictionary order.

## Finite recursive composition

`Instruction` contains only the declaration and child position. `follow` repeatedly calls the actual runner and computes each new map from the real demand prefix. `PathModels` independently uses Accepts, the original expand child position, and LocalModels at every goal; it contains neither the runner nor the allocated map nor ordinary atoms. For every assignment, cursor and arbitrary finite instruction list, there exists a successful final cursor whose requests have a model iff the initial requests have a model and PathModels holds. Actual executable descents are also old History edges, so cycle66 root provenance composes unchanged. Missing children and outside/negative candidates stop only this selected-path utility, not a language-visible resolver.
