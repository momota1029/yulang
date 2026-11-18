from pathlib import Path
import json,hashlib,re,subprocess
v=Path('notes/verification/cycle251'); old=json.loads(Path('notes/verification/cycle250/dependency-source-sha256.json').read_text())
assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest()==h for p,h in old.items())
print(f'PASS previous dependency hashes unchanged: {len(old)}')
mods=v.joinpath('CompleteAudit-modules.txt').read_text().splitlines();seen=set()
def visit(m):
 p=Path('lean')/Path(*m.split('.')).with_suffix('.lean')
 if not p.exists() or str(p) in seen:return
 seen.add(str(p))
 for dep in re.findall(r'^import\s+(\S+)',p.read_text(),re.M):visit(dep)
for m in mods:visit('Yulang.'+m)
v.joinpath('dependency-source-sha256.json').write_text(json.dumps({p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in sorted(seen)},indent=2)+'\n')
print(f'PASS import closure hashed: {len(seen)}')
for m in mods:assert not re.search(r'\b(sorry|admit|native_decide)\b',Path('lean/Yulang/'+m+'.lean').read_text())
print('PASS no forbidden tokens in 28 new modules')
oldpaths=set(subprocess.check_output(['git','ls-tree','-r','--name-only','302bf6196','lean'],text=True).splitlines())
changed=subprocess.check_output(['git','diff','--name-only','302bf6196','--','lean'],text=True).splitlines()
assert not [p for p in changed if p in oldpaths and p!='lean/Yulang.lean']
oldbarrel=subprocess.check_output(['git','show','302bf6196:lean/Yulang.lean'],text=True)
assert Path('lean/Yulang.lean').read_text().startswith(oldbarrel)
print('PASS old Lean sources frozen; barrel append-only')
print('Latest integration 00793b4ac imported; I48 read at01:12; no new Lean added after that check')
print('Whole repository build, verify-lean.sh and Yulang2 runtime not run')
