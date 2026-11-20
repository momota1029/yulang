# Boolean readiness without materializing dictionaries during checks

At each bounded round cache one Boolean per declared key, looking only at
the previous round for every ordered child. False can mean missing row or
insufficient fuel, so do not expose it as semantic rejection; the actual
dictionary read remains separate. With a domain proven to cover every
stored source row, every memoized entry is true exactly when the original
reader can produce some dictionary at that round. Duplicate domain keys
agree by construction; repeated edges and implementation IDs need not be
unique. Store earliest successful per-key ranks from these Boolean layers,
and compare with the original exhaustive readiness check, including a
synthetic cyclic and missing-row table.
