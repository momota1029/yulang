# Realm / Band Cache Example

This directory is a small local fixture for the realm / band compiled-unit
cache.

```text
main.yu          entry module
math.yu          module loaded by use mod math::*
math/consts.yu   child module loaded by mod consts in math.yu
render.yu        module loaded by use mod render::*
```

This is a local realm / band cache smoke fixture. `use mod math::*` means
`mod math; use math::*`: it loads the local module file and imports the
module's public names. `math.yu` imports `math/consts.yu` with `mod consts`, so
the fixture has multiple source dependency SCCs inside the same band.

Run this twice:

```bash
yulang check examples/realm-band-cache/main.yu --infer-phase-timings
```

The first run writes compiled-unit artifacts for the dependency SCCs. The
second run should read unchanged dependency artifacts from the persistent cache.
