from pathlib import Path
import subprocess,hashlib
base='676aee9e656d50b64f8a9f2fd14dfa16a6f0ad67'
def git(*a):return subprocess.check_output(['git',*a])
paths=git('ls-tree','-r','--name-only',base).decode().splitlines()
for path in paths:
 assert Path(path).is_file(),('missing',path)
 if path.startswith('lean/'):
  old=git('show',base+':'+path);new=Path(path).read_bytes()
  if path=='lean/Yulang.lean':assert new.startswith(old),path
  else:assert old==new,path
assert Path('notes/design/INDEX.md').read_bytes().startswith(git('show',base+':notes/design/INDEX.md'))
for checkpoint in ['720ef126fee791d11774947b989a108ac98960d8','7943083aa3d58e9c718292d015312e1fa05bc8f7']:
 for path in git('ls-tree','-r','--name-only',checkpoint).decode().splitlines():
  if path.startswith('lean/') and path!='lean/Yulang.lean':
   assert Path(path).read_bytes()==git('show',checkpoint+':'+path),(checkpoint,path)
modules=sorted(Path('lean/Yulang').glob('*186.lean'))
for p in modules:
 assert Path('lean/Yulang.lean').read_text().count('import Yulang.'+p.stem+'\n')==1,p
print('PASS:',len(paths),'prior paths retained; old Lean byte-exact; root and INDEX prefix; both published186 checkpoints unchanged;',len(modules),'modules each imported once')
Path('notes/verification/cycle186/source-hashes.tsv').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'\t'+str(p)+'\n' for p in modules))
