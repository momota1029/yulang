from pathlib import Path
import sys,re,json,hashlib
label=sys.argv[1]; mods=sys.argv[2:]; names=[]
for m in mods:names += ['Yulang.'+m+'.'+n for n in re.findall(r'^[ \t]*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|def|abbrev|structure|inductive)\s+([\w.]+)',Path('lean/Yulang/'+m+'.lean').read_text(),re.M)]
s=''.join('import Yulang.'+m+'\n' for m in mods)+'import Lean\nopen Lean Elab Command in\nrun_cmd do\n let environment ← getEnv\n let allowed := #[``propext, ``Classical.choice, ``Quot.sound]\n let names := #['+',\n  '.join('``'+n for n in names)+']\n for name in names do\n  unless environment.contains name do throwError "Missing declaration {name}"\n  for dependency in ← collectAxioms name do\n   unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"\n logInfo m!"CYCLE249-'+label.upper()+'-PASS: {names.size} explicit declarations in '+str(len(mods))+' modules"\n'
Path('lean/Audit/Cycle249'+label+'.lean').write_text(s)
b=Path('lean/Yulang.lean');s=b.read_text();s+=''.join('import Yulang.'+m+'\n' for m in mods if 'import Yulang.'+m+'\n' not in s);b.write_text(s)
v=Path('notes/verification/cycle249');(v/(label+'-modules.txt')).write_text('\n'.join(mods)+'\n');(v/(label+'-declarations.txt')).write_text('\n'.join(names)+'\n');(v/(label+'-source-sha256.json')).write_text(json.dumps({'lean/Yulang/'+m+'.lean':hashlib.sha256(Path('lean/Yulang/'+m+'.lean').read_bytes()).hexdigest() for m in mods},indent=2)+'\n')
