import subprocess,re,hashlib
from pathlib import Path
G=lambda *a:subprocess.check_output(['git',*a],text=True)
a='0b2a6b482ef6d7e7e84223aad7fd3eb55eefd2d9'
def tree(c):
 return {l.split('\t',1)[1]:l.split()[2] for l in G('ls-tree','-r',c).splitlines()}
x=tree(a)
for p in x:
 assert Path(p).exists(),p
 if (p.endswith('.lean') and p!='lean/Yulang.lean') or p in ['lean/Audit.lean','lean/README.md']:
  data=Path(p).read_bytes(); assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==x[p],p
for p in ['lean/Yulang.lean','notes/design/INDEX.md']:
 assert Path(p).read_text().startswith(G('show',a+':'+p)),p
new=list(Path('lean/Yulang').glob('*184.lean'))
for p in new:
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',p.read_text()),p
print(f'PASS: {len(x)} prior paths retained; no old proof changes; frozen Audit/README unchanged; root/INDEX prefix retained; {len(new)} new184 modules free of forbidden proof tokens.')
