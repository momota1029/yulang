from pathlib import Path
import re,json,hashlib,subprocess
v=Path('notes/verification/cycle254')
prior=json.loads(Path('notes/verification/cycle253/dependency-source-sha256.json').read_text())
assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest()==h for p,h in prior.items())
print(f'PASS previous dependency source hashes unchanged: {len(prior)}')
mods=v.joinpath('modules.txt').read_text().splitlines();seen=set()
def visit(m):
 p=Path('lean')/Path(*m.split('.')).with_suffix('.lean')
 if not p.exists() or str(p) in seen:return
 seen.add(str(p))
 for dep in re.findall(r'^import\s+(\S+)',p.read_text(),re.M):visit(dep)
for m in mods:visit('Yulang.'+m)
visit('Audit.Cycle254Usage')
v.joinpath('dependency-source-sha256.json').write_text(json.dumps({p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in sorted(seen)},indent=2)+'\n')
print(f'PASS import closure hashed: {len(seen)}')
for p in [Path('lean/Yulang/'+m+'.lean') for m in mods]+[Path('lean/Audit/Cycle254Usage.lean')]:
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',p.read_text())
print('PASS forbidden tokens absent in new modules and usage')
base='5fb38d081976417c4ec6c3f1adb4813bc1208cc7'
oldpaths=set(subprocess.check_output(['git','ls-tree','-r','--name-only',base,'lean'],text=True).splitlines())
changed=subprocess.check_output(['git','diff','--name-only',base,'--','lean'],text=True).splitlines()
assert not [p for p in changed if p in oldpaths and p!='lean/Yulang.lean']
oldbarrel=subprocess.check_output(['git','show',base+':lean/Yulang.lean'],text=True)
assert Path('lean/Yulang.lean').read_text().startswith(oldbarrel)
print('PASS old Lean frozen; barrel append-only')
print('Whole repository build, verify-lean.sh and Yulang2 runtime not run')
