from pathlib import Path
import hashlib,json,re
r=Path('yulang181-public')
u={x['path']:x['sha'] for x in json.load(open('cycle181-verification/upTree.json'))['tree'] if x['type']=='blob'}
w={x['path']:x['sha'] for x in json.load(open('cycle181-verification/workTree.json'))['tree'] if x['type']=='blob'}
def sha(p):
 b=p.read_bytes(); return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
assert all((r/p).exists() for p in set(u)|set(w))
print('PASS all prior upstream/work blob paths retained:',len(set(u)|set(w)))
old=[p for p in set(u)|set(w) if p.startswith('lean/') and p!='lean/Yulang.lean']
assert all(sha(r/p)==u.get(p,w.get(p)) for p in old)
print('PASS previous Lean sources unchanged from supervisory upstream or preserved work-only blobs:',len(old))
for p in ['lean/Audit.lean','lean/README.md','lean/lakefile.toml','lean/lake-manifest.json','lean/lean-toolchain']:
 if p in u: assert sha(r/p)==u[p]
print('PASS frozen audit/readme and lake configuration unchanged')
new=sorted((r/'lean/Yulang').glob('*181.lean'))
imports=(r/'lean/Yulang.lean').read_text().splitlines()
for p in new:
 s=p.read_text();assert 'import Yulang.'+p.stem in imports
 assert not re.search(r'\b(sorry|sorryAx|admit|native_decide|ofReduceBool|skipKernelTC|implemented_by|axiom)\b|@\[extern|addDecl',s)
 assert not re.search(r'^\s*(run_cmd|#eval|elab|elab_rules|macro|macro_rules|syntax|initialize|builtin_initialize)\b',s,re.M)
 assert all(line.rstrip()==line for line in s.splitlines())
print('PASS root imports, proof construct scan, whitespace:',len(new),'new modules')
print('LIMIT: static content checks only, not the supervisor full-build gate; audit metaprogram is separately reviewed')
