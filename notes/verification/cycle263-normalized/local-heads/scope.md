# Finite representative and observed head support

The new module changes no existing definition. It selects a witness snapshot for each ALREADY chosen representative, using its RegisteredAt proof. This matters: choosing a new arbitrary Plan from the owner class would not automatically produce head support for the existing representative. The witness specification proves actual source path, exact representative membership and owner code.

RepresentativeHeads quantifies only over the given finite owner list. For an owner which actually occurs, it requires Heads of its selected witness snapshot. Unused owner codes use the initial snapshot as a definitional fallback but incur no representative-head obligation. Each witness snapshot has a finite registered plan list; Heads refers only to actual head schemas, not body or output ClassEffects.

The local transport theorem additionally requires Heads for the actual observed reachable snapshot. It then produces normalized compatibility for any actual registered selected Plan whose owner lies in the finite list. all_registered_compatible packages this for every registered Plan at that one observed snapshot. No premise ranges over all source futures. The previously stronger SourceHeads implies the finite representative condition, but the converse is neither used nor claimed.

For a whole run, a caller still must supply the observed-head premise at each relevant observation (or use an inspector-dependent context). This module does not automatically derive those heads, model existence, valid source acceptance, M1, or old-Step simulation. Representative/witness selection is noncomputable proof infrastructure; executable finite scheduling remains separate.

Strict focused production and audit builds pass; only standard propext/Classical.choice/Quot.sound. Files and source hash are adjacent. No existing source files were modified.
