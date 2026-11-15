# Cycle217 verification

## Scope and commands

Lean4.35.0, existing local package; focused targets only, not a full umbrella or
legacy Audit rebuild. The final focused command was:

```
lake build --wfail Yulang.GeneralDictionaryCurrentChosen217 Yulang.GeneralDictionaryObservationPersistence217 Yulang.GeneralDictionaryPointObservation217 Yulang.GeneralDictionaryLooseGround217
lake env lean -j1 --trust=0 -DwarningAsError=true Audit/Cycle217Complete.lean
```

PASS:1341 dependency jobs. The standalone gate traverses every constant owned by
all9 cycle217 modules: PASS75 constants. Only propext, Classical.choice and
Quot.sound are allowed. These are75 definitions/theorems/generated constants,
not75 named theorems; the9 modules contain42 explicitly named theorems.
Logs: [build](cycle217/build.txt), [audit](cycle217/audit.txt).

## Earlier failures and resolution

Initial elaboration failures involved an implicit model name colliding with the
carrier model, binder equality simplifying to True, wrong argument order for
use_same, inability to infer a journal wrapper from a bare core, reducibility
of PointParameter, and a nonexistent Ty.evalAt name. These were fixed, all
modules rebuilt with warnings fatal, and the full gate rerun successfully.
An early3module/11constant gate also passed; the final9module gate supersedes it.
No failed proof was published as verified.

## Diff and review

No sorry/admit/newaxiom/native_decide/unsafe tokens in cycle217 Lean sources.
The sole run_cmd is the reviewed all-constant axiom gate. git diff --check PASS.
lean/Yulang.lean and notes/design/INDEX.md preserve their exact pre-cycle byte
prefixes and only append imports/index entry. No prior proof module changed.
Seven modules independently read-only reviewed; no critical flaw found. The
review explicitly retained all residual hypotheses and all-Frame quantifiers.
LooseGround and ObservationPersistence have local compile/kernel checks, not
independent review. No runtime/Yulang2/CLI end-to-end test is claimed.

## Publication checks

Checkpoint1:0e90f1b913ddc2870472d2032323ad5289a8bf04,7/7 blobs verified.
Checkpoint2:640b96f584cb4b4f919cec1975ba290d721753fe,8 changed blobs verified.
Latest observed integration:be34bf7f778fc300a79594bdfab5a5eef98288c5;
GitHub comparison to checkpoint2: ahead6,behind0. Final publication uses a fresh
work/dots-main parent with expected-sha lease; no force and no integration write.
Final artifact readback and writer release are recorded in the heartbeat.
