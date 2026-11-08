# Arbitrary-old-state finite path completion

The completed finite-path entry takes an arbitrary ordinary `State n`, an initial receiver slot, and a finite output-slot list. Seed equations come from the actual checked Index declaration. Each path step re-materializes the receiver from the returned state and invokes the real associated producer. An ordinary consistency check follows the path.

Independent success judgment: output equals the explicit fold of str equations, and that fold has an ordinary model. For all paths, receiver slots, old states and output states, `checkedRun = some out` iff this judgment. No model/success/fuel premise is supplied. A second entry materializes the last slot and builds the actual Parent dictionary, with `where Left a, Right a`. Its independent result judgment additionally names a str argument and a declarative Dictionary. All original constraints, including effects, are preserved.

The proof of success-domain completeness uses a model of the final fold to establish consistent str evidence at every intermediate state. It does NOT assume the constant-pure-str valuation satisfies an arbitrary old state. Successful-output uniqueness is derived from the final model and backward preservation.

Boundary: the input finite path supplies structural termination. This is not dynamically generated graph closure, general candidate narrowing, Paterson/K2 saturation, or a four-way language-visible classification. The concrete reverse-order example separately starts from Right's declaration; this arbitrary path entry starts from Index's declaration. Both registry phases are explicit, not claimed to be a proven whole-program parser/lowering.
