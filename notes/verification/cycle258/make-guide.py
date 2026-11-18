from pathlib import Path
import re
v=Path('notes/verification/cycle258');mods=v.joinpath('modules.txt').read_text().splitlines()
intro='''# Cycle258 verification scope and declaration inventory

Each declaration's full type is printed in AllTypes-final.txt; Complete audits
explicit declarations and Full enumerates generated/private declarations too.
Reach reports selected-root usage, not an assertion that all declarations are
reachable. Zero-sorry compilation is not evidence of general language semantics.

## Scope groups
- Modules1–5: I45 generated endpoint-family recognition and one fixed fill across
  all stages, under the positive finite journal model premise. Keeps binder.
- Modules6–10: direct alias and source extension, changing the internal binder
  while keeping initial0..4 and every row. Fixed I45 only; direct View still grows.
- Modules11–13: early bounded search extensionally equal to earlier recognition.
  i+1 is one recognizer's loop visits, not full fill or arithmetic/time complexity.
- Modules14–22: fixed source252 arbitrary output gap and private output type
  completion, actual packet/effect/Evidence, public projection, closed depth4
  readback after completion. Not an I50 refutation or general producer.
- Modules23–25: partial I52 successor. Finite fixed-fact write plus novelty gate
  terminates for every supplied observer. I45 fixed-table observer installs once;
  completed old stages and projected new states have equivalent public models.
  General source observer/compiler, microstep simulation, 239 correspondence,
  constructor/presence coverage and general language termination remain open.

## Independent review
All25 modules received read-only reviews at their checkpoint commits. No
independent reviewer rebuild. Fifth review prompted only a wording correction:
intermediate subsets formally get the else predicate, but its language
correctness is not claimed. Reviews are retained separately.

## Declarations by module
'''
for i,m in enumerate(mods,1):
 s=Path('lean/Yulang/'+m+'.lean').read_text();names=re.findall(r'^\s*(?:noncomputable\s+)?(?:theorem|def|abbrev)\s+(\w+)',s,re.M)
 intro+=f'\n### {i}. `{m}`\n'+', '.join('`'+n+'`' for n in names)+'\n'
v.joinpath('scope-guide.md').write_text(intro)
