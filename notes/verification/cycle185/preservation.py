from pathlib import Path
import subprocess,hashlib
base='fa34ca1e4935de2b8fa0fa5d44ee9645878d2e6e'
def git(*a): return subprocess.check_output(['git',*a])
paths=git('ls-tree','-r','--name-only',base).decode().splitlines()
for path in paths:
 assert Path(path).is_file(),('missing',path)
 if path.startswith('lean/'):
  old=git('show',base+':'+path);new=Path(path).read_bytes()
  if path=='lean/Yulang.lean': assert new.startswith(old),path
  else: assert old==new,path
assert Path('notes/design/INDEX.md').read_bytes().startswith(git('show',base+':notes/design/INDEX.md'))
for path in git('ls-tree','-r','--name-only','8ede9291a2d487afe70f1c7227d2d790445964ed').decode().splitlines():
 if path.startswith('lean/Yulang/') and path.endswith('185.lean'):
  assert Path(path).read_bytes()==git('show','8ede9291a2d487afe70f1c7227d2d790445964ed:'+path),path
for p in sorted(Path('lean/Yulang').glob('*185.lean')):
 assert Path('lean/Yulang.lean').read_text().count('import Yulang.'+p.stem+'\n')==1,p
print('PASS: all',len(paths),'upstream paths retained; old Lean exact except appended root; INDEX prefix; checkpoint1 proof sources unchanged; all new modules imported exactly once')
Path('notes/verification/cycle185/source-hashes.tsv').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'\t'+str(p)+'\n' for p in sorted(Path('lean/Yulang').glob('*185.lean'))))
for checkpoint in ['ac2399ac4dd73d9bdb9a0ffaef7b10950c01a404','be65cec80b135558472440834a499de3a39f1a5e']:
 for path in git('ls-tree','-r','--name-only',checkpoint).decode().splitlines():
  if path.startswith('lean/') and path.endswith('185.lean'):
   assert Path(path).read_bytes()==git('show',checkpoint+':'+path),(checkpoint,path)
print('PASS: all published checkpoint2/3 cycle185 proof sources unchanged')
