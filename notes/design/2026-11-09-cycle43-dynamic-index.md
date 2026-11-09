# Cycle43: dynamic receiver feedback for the checked Index declaration

Implemented scope is the existing checked `Index(box payload)` associated-value declaration, with str ordinary scalar evidence. This does not choose general role semantics.

Data: finite source-slot graph of requests `(receiver, output)` and ordinary State n. Facts `slot` are seeded by paired ordinary bounds; an enabled edge reads the receiver fact and produces str at the output. Unknown receivers do not produce facts. The finite work domain is computed from n and the single supported str scalar.

Independent judgment: `Derived seed edges fact`, with seed and edge-transfer rules. Execution: finite Horn saturation using these actual edges. Target: for all n, seed, edges, fact, membership in saturation iff Derived; finite termination and least closure. Bridge: each enabled supported receiver fact in the resulting state invokes the real `produceIndex`/checked declaration and yields the prescribed output equality, rather than taking an externally supplied associated output.

Any consistency hypothesis needed to select unique materialized evidence must remain explicit. No claim that every input has a model, that arbitrary declarations have monotone output, or that this closes general B4. This is a genuine dynamic-receiver fragment, not a change to the existing int-only Ty endpoint grammar.

Yulang2: existing fetched X13–X17 audit material distinguishes local interval tests from the general outer boundary. New read-only audit fetch was rejected by the execution reviewer as outside scope; no new runtime comparison. Current spec 6.3/6.5 and the existing checked Index declaration remain authoritative.

Completed: Executed interprets the finite schedule through real intermediate states. Complete-output consistency suffices for those receiver reads. Re-saturation membership is unchanged without a model premise.
