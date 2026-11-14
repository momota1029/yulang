# Development failures and repairs

- First attempted ff-only merge from retained local cycle186 failed (divergent
  Git object histories). Subsequent integration merge conflicted. It was aborted;
  local prior branch retained, cycle187 starts at fresh remote cf362e7b. No conflict
  resolution was published, and the preservation gate checks all prior paths.
- CLI push failed: could not read Username for https://github.com. Used the
  GitHub app's create_tree/create_commit/update_ref with expected-head lease.
- CaptureBounds first compile failed because Origin was ambiguous. Qualified it.
- CaptureOrigins first compile needed explicit unfolding of inspection and a
  List.append congruence proof; repaired before checking the module.
- SchemaCapture first compile needed schema unfolding, Option.map_some and the
  same transparency option used by its upstream counterpart.
- SchemaTests initial compile needed explicit report binders and branch reduction;
  multiple-target split was unsupported and replaced with branch-local simplification.
- Initial publication serialization exceeded command-output limit because the
  root import file is 125KB. Retried supported tree construction after reading that
  file in bounded chunks. This was a local serialization failure, not a GitHub write.
- ProjectionFrame initial compile opened two namespaces with Report/inspectMany;
  narrowed the imported names, then the source check passed.
