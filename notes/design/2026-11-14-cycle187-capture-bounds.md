# Cycle187: independent capture bounds criterion

For I32/V6 WF evidence, remove the opaque merged BoundsFit obligation from
cycle186's revisited-head extension criterion. Prove exact correspondence with
all raw same-name capture intervals under the existing merge equations, and
transport values from historical binders using numeric-identity semantic readback.
No new semantics, no assumption that Prepared means every model is a branch model.
First establish a generic report theorem: recorded merge equations and existing
ProjectionModels imply every actually observed capture value fits the allocated
merged capture. Expose raw occurrence membership and nonemptiness, rather than
assuming target Fits. Then connect the criterion to the current Frame and existing
conservative whole-head extension. Output equations/child evidence remain outside
this result; general EvidenceNode stays open.
