Independent read review of 8d436511 GeneralRebaseBudget258: no issue. Runs counts
only new Step edges; n plus final remaining <= initial remaining, initial run
<= basis.length. Same proposal is idempotent and retry none. I45 <=1 is specific
to fixed observer and initialState. Does not bound old steps, observer internal
computation, failed/no-op attempts or general runtime. Commit matched; no rebuild.
