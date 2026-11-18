from pathlib import Path
import re,json,hashlib,subprocess
v=Path('notes/verification/cycle257')
prior=json.loads(Path('notes/verification/cycle256/dependency-source-sha256.json').read_text())
assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest()==h for p,h in prior.items())
print(f'PASS previous cycle256 dependency source hashes unchanged: {len(prior)}')
older=json.loads(Path('notes/verification/cycle255/dependency-source-sha256.json').read_text())
assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest()==h for p,h in older.items())
print(f'PASS previous cycle255 dependency source hashes unchanged: {len(older)}')
mods=v.joinpath('modules.txt').read_text().splitlines();seen=set()
def visit(m):
 p=Path('lean')/Path(*m.split('.')).with_suffix('.lean')
 if not p.exists() or str(p) in seen:return
 seen.add(str(p))
 for dep in re.findall(r'^import\s+(\S+)',p.read_text(),re.M):visit(dep)
for m in mods:visit('Yulang.'+m)
visit('Audit.Cycle257Usage')
visit('Audit.Cycle257Reach')
v.joinpath('dependency-source-sha256.json').write_text(json.dumps({p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in sorted(seen)},indent=2)+'\n')
print(f'PASS import closure hashed: {len(seen)}')
imports=0
for p in seen:
 for line in Path(p).read_text().splitlines():
  if re.match(r'^\s*(?:public\s+|meta\s+)?import\s+',line):
   imports+=1
   assert line.startswith('import ') and len(line.split('--',1)[0].split())==2, (p,line)
print(f'PASS dependency import syntax matches collector: {imports} lines')
for p in [Path('lean/Yulang/'+m+'.lean') for m in mods]+[Path('lean/Audit/Cycle257Usage.lean')]:
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',p.read_text())
print('PASS forbidden tokens absent in new modules and usage')
base='e4657fcb7f3f4640080d5606217ed45116ad802d'
oldpaths=set(subprocess.check_output(['git','ls-tree','-r','--name-only',base,'lean'],text=True).splitlines())
changed=subprocess.check_output(['git','diff','--name-only',base,'--','lean'],text=True).splitlines()
assert not [p for p in changed if p in oldpaths and p!='lean/Yulang.lean']
oldbarrel=subprocess.check_output(['git','show',base+':lean/Yulang.lean'],text=True)
assert Path('lean/Yulang.lean').read_text().startswith(oldbarrel)
print('PASS old Lean frozen; barrel append-only')
print('Whole repository build, verify-lean.sh and Yulang2 runtime not run')
