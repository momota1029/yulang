# Actual propagation public-model equivalence

Actual propagate adds both cross inequalities and merge equations. It would be
incorrect to equate old state Models alone with propagated Models: cross may
constrain old endpoints. The exact interface therefore compares
exists assignment, old State.Models AND fresh Compatible bindings AND public
boundary against exists assignment, actual propagated State.Models AND same
boundary. Use finite public list extra and protected actual active+endpoint+extra
pool. Forward uses ActiveMerge249; backward uses actual propagate_models.
No assumed model existence, operational eligibility, registry checking or
source reachability is smuggled into the conclusion.
