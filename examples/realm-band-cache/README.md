# Realm / Band Cache Example

This directory is a small editable-realm fixture for the realm / band
compiled-unit cache.

A realm is a versioned resolution space. A band is an import/build island
inside a realm. This fixture stays inside one editable realm and one band while
exercising multiple source dependency SCCs.

```text
main.yu          entry module
math.yu          module loaded by use mod math::*
math/consts.yu   child module loaded by mod consts in math.yu
render.yu        module loaded by use mod render::*
```

This is an editable realm / band cache smoke fixture. `use mod math::*` means
`mod math; use math::*`: it loads the local module file and imports the
module's public names. `math.yu` imports `math/consts.yu` with `mod consts`, so
the fixture has multiple source dependency SCCs inside the same band.

Run this twice:

```bash
yulang check examples/realm-band-cache/main.yu --infer-phase-timings
```

The first run writes compiled-unit artifacts for the dependency SCCs. The
second run should read unchanged dependency artifacts from the persistent cache.
