import pathlib,subprocess,os,re,json,hashlib
repo=pathlib.Path('/workspace/scratch/1d0b4aaa3394/yulang166-public');lib=repo.parent/'y166lib';source=repo.parent/'yulang159/lean/.lake/build/lib/lean';lean='/tmp/lean137/lean-4.35.0-linux/bin/lean'
lib.mkdir(exist_ok=True)
for folder,dirs,files in os.walk(source):
 dest=lib/pathlib.Path(folder).relative_to(source); dest.mkdir(exist_ok=True)
 for name in files:
  out=dest/name
  if not out.exists() and not out.is_symlink():out.symlink_to(pathlib.Path(folder)/name)
env=dict(os.environ,LEAN_PATH=str(lib),LEAN_NUM_THREADS='1')
paths=subprocess.check_output(['git','diff','--name-only','63aab710204c91396e4957a8e52fc58778171b85','HEAD'],cwd=repo,text=True).splitlines();paths=[p for p in paths if p.startswith('lean/Yulang/') and p.endswith('.lean')];mods={'Yulang.'+pathlib.Path(p).stem:p for p in paths};done=set()
def build(m):
 if m in done:return
 p=repo/mods[m]
 for d in re.findall(r'^import (\S+)',p.read_text(),re.M):
  if d in mods:build(d)
 out=lib/(m.replace('.','/')+'.olean')
 if out.is_symlink():out.unlink()
 r=subprocess.run([lean,'--trust=0','-o',str(out),str(p)],cwd=repo/'lean',env=env,capture_output=True,text=True,timeout=180)
 print(m,'EXIT',r.returncode,r.stdout,r.stderr,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
 done.add(m)
for m in mods:build(m)
for p in sorted((repo/'lean/Audit').glob('Cycle166*.lean')) + [repo/'lean/Audit/GeneralNominalPointBudget.lean',repo/'lean/Audit/GeneralNominalPointClass.lean']:
 r=subprocess.run([lean,'--trust=0',str(p)],cwd=repo/'lean',env=env,capture_output=True,text=True,timeout=180)
 print(p.name,'EXIT',r.returncode,r.stdout,r.stderr,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
print('ALL PASS',len(mods),flush=True)
