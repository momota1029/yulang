import subprocess,re
from pathlib import Path
G=lambda *a:subprocess.check_output(['git',*a],text=True)
a='63ff809839e1c23ae9e542da9a5bcf56e9c2ed10'; b='56b64b7a1a2961091927edfee4ffba049e9acd1d'
def tree(c):
 return {l.split('\t',1)[1]:l.split()[2] for l in G('ls-tree','-r',c).splitlines()}
x,y=tree(a),tree(b)
assert x.keys()<=y.keys()
for p in x:
 if p.endswith('.lean') and p!='lean/Yulang.lean': assert x[p]==y[p],p
for p in ['lean/Audit.lean','lean/README.md']: assert x[p]==y[p]
for p in ['lean/Yulang.lean','notes/design/INDEX.md']: assert G('show',b+':'+p).startswith(G('show',a+':'+p)),p
new=[p for p in y if p.startswith('lean/Yulang/') and p.endswith('183.lean')]
assert len(new)==8
root=G('show',b+':lean/Yulang.lean'); gate=G('show',b+':lean/Audit/Cycle183FinalGate.lean')
for p in new:
 imp='import Yulang.'+Path(p).stem
 assert root.splitlines().count(imp)==1 and imp in gate
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',G('show',b+':'+p)),p
print(f'PASS: {len(x)} prior paths retained; {len(y)} published paths; no prior proof changes; frozen Audit/README unchanged; root/INDEX prefix retained; eight unique imports audited; no forbidden tokens.')
print('Source commit: '+b)
