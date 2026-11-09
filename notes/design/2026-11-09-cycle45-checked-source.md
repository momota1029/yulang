# Cycle45: checked named source entrance

Partial goal: the finite string Index adapter must not silently drop a request whose named endpoint is absent. Keep the existing table/request language and add a decidable coverage gate with a precise list of invalid requests. This is an adapter input check, not a language rejected classification and not parser correctness.

Data: arbitrary finite occurrence table, arbitrary named request list, initial State.
Independent contract: existing WellScoped; semantic success is scope plus existing output-model condition. Implementation computes missing requests then returns an Except failure or the actual adapter output. Exact success/failure and conditional producer execution are the outer theorems. No consistency/existence is inferred from passing scope.

Yulang example: a table containing only name 10 with Index(10,20) has missing output occurrence 20. Delay language classification; the adapter returns that malformed request explicitly. Duplicate names are legal identity aliases.

B4 bridges remain five. This advances the finite source boundary only.
