from pathlib import Path
import re
v=Path('notes/verification/cycle256');mods=v.joinpath('modules.txt').read_text().splitlines();decls=[]
for m in mods:
 for n in re.findall(r'^\s*(?:theorem|def)\s+(\w+)',Path('lean/Yulang/'+m+'.lean').read_text(),re.M):decls.append('Yulang.'+m+'.'+n)
v.joinpath('declarations.txt').write_text('\n'.join(decls)+'\n')
imports=''.join('import Yulang.'+m+'\n' for m in mods)
Path('lean/Audit/Cycle256Complete.lean').write_text(imports+'\n'+''.join('#print axioms '+d+'\n' for d in decls))
Path('lean/Audit/Cycle256Full.lean').write_text(imports+'''import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let prefixes := #['''+', '.join('"Yulang.'+m+'."' for m in mods)+''']
 let mut count : Nat := 0
 for (name, _) in environment.constants.toList do
  if prefixes.any (fun pfx => name.toString.startsWith pfx || name.toString.startsWith ("_private." ++ pfx)) then
   for dependency in ← collectAxioms name do
    unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
   count := count + 1
 logInfo m!"CYCLE256-FULL-AUDIT-PASS: {count} declarations including generated and private declarations"
''')
p=Path('lean/Yulang.lean');s=p.read_text();s+=''.join('import Yulang.'+m+'\n' for m in mods if 'import Yulang.'+m+'\n' not in s);p.write_text(s)
print('explicit declarations',len(decls))
