# Deeper focused rebuild

Beyond the fresh build of current cycle256 modules, rebuilt 104 modules from
the actual dependency closure in the numbered 244–256 rewrite/source-support
layer in a separate cache, in dependency order. The exact list and full log are
critical-layer-modules.txt and critical-layer-build.txt. Start13:01:23, completion
13:03:21 UTC, exit0. This includes14 then-existing cycle256 modules and90 earlier
rewrite/normalization/source-support modules. The final OrderedRawPublic256
bridge was added afterward and separately rebuilt in the final focused run.

Older dependencies outside this selected layer were reused, with source hashes
checked. This was not a whole-repository rebuild and not an independent worker's
rebuild. The separate read-only reviewers did not rebuild. No source was changed
by this verification. The two newly needed242 adapters were separately strict
built in public-bridge-dependency-build.txt.
