# C361 initial strict source check

Lean 4.35.0; `lean --stdin --trust=0 -DwarningAsError=true`, exact source (Git blob `74384b0bd60430b9e6cc0076f31be3c160691a92`), exit 0. Independent intended audit blob `43274e4602bf424db2146dd6286e18142d6429ce`; its exact five `#print axioms` commands were run at the end of a second strict evaluation of the source, exit 0 (on the read-only executor, a new module .olean could not be written, so this is not a separate imported audit build). Each audit reports only propext/Classical.choice/Quot.sound (model_fits did not use Classical.choice). Imported retained direct source hashes compared to exact C360. Whole build/Lake not run. Exact commands audit these declarations:

- `actual_receiver_state`
- `read_in_every_final_model`
- `model_fits`
- `exact_run_is_inhabited`
- `checked_state_links_all_receipts`
