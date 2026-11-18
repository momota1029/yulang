from pathlib import Path
import re,json
v=Path('notes/verification/cycle263'); mods=v.joinpath('modules.txt').read_text().splitlines(); decls=[]
for m in mods:
 for n in re.findall(r'^\s*(?:noncomputable\s+)?(?:theorem|def|abbrev)\s+(\w+)',Path('lean/Yulang/'+m+'.lean').read_text(),re.M):decls.append('Yulang.'+m+'.'+n)
v.joinpath('declarations.txt').write_text('\n'.join(decls)+'\n')
imports=''.join('import Yulang.'+m+'\n' for m in mods)
Path('lean/Audit/Cycle263Complete.lean').write_text(imports+'\n'+''.join('#print axioms '+d+'\n' for d in decls))
Path('lean/Audit/Cycle263Types.lean').write_text(imports+'\n'+''.join('#check @'+d+'\n' for d in decls))
Path('lean/Audit/Cycle263Full.lean').write_text(imports+'''open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let prefixes := #['''+', '.join(json.dumps('Yulang.'+m+'.') for m in mods)+''']
 let mut count : Nat := 0
 for (name, _) in environment.constants.toList do
  if prefixes.any (fun pfx => name.toString.startsWith pfx || name.toString.startsWith ("_private." ++ pfx)) then
   for dependency in ← collectAxioms name do
    unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
   count := count + 1
 logInfo m!"CYCLE263-FULL-AUDIT-PASS: {count} declarations including generated and private declarations"
''')
print(len(mods),'modules',len(decls),'explicit declarations')
