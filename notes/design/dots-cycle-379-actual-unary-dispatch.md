# C379: positive early dispatch in the existing unary native scanner

I-65 step 1. Work only in the existing C361 exact native matcher and
its already represented candidate scanner. No new fixtures, acceptance
rules, or successful-selection premises for the public theorem.

- Normalize the *actual* written query. In C361's unary native case the
  two key comparisons and real `readCtor e key 1` run before the child
  read. Extract the literal ordinal-zero child pair from those guards;
  prove that the exact outer `read` succeeds iff that recursive
  `read` succeeds. In particular child failure does not erase the
  fact that the outer branch dispatched.
- The scope is the existing unary source/code matcher (ordinary
  variables are not inspecting nodes). Its scoped `NativeAmbiguity361`
  caller uses a physically backed native port and its existing
  `exactGraph` test before inspecting two distinct visible literal
  rows. Keep the executable order: first candidate enters after the
  finite gate; second candidate is dispatched only after a positive
  first match. A missing result is not a language rejection, and the
  structural gate here is not automatically the general I-65 K2/priority
  rule. The two scoped shapes do not make a complete native scanner.
- Keep exact current release, source normalized pattern, real declared
  read, and actual recursive code separate. A hypothetical EarlyPorts
  entry or successful typed comparison cannot satisfy these premises.
